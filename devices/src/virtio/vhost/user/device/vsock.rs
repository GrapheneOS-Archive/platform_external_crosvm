// Copyright 2021 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use std::os::unix::fs::OpenOptionsExt;
use std::{
    convert::{self, TryFrom, TryInto},
    fs::{File, OpenOptions},
    mem::size_of,
    num::Wrapping,
    os::unix::{io::AsRawFd, net::UnixListener},
    path::Path,
    str,
    sync::{Arc, Mutex},
};

use anyhow::{bail, Context};
use base::{
    clear_fd_flags, error, AsRawDescriptor, Event, FromRawDescriptor, IntoRawDescriptor,
    SafeDescriptor, UnlinkUnixListener,
};
use cros_async::{AsyncWrapper, Executor};
use data_model::{DataInit, Le64};
use getopts::Options;
use hypervisor::ProtectionType;
use once_cell::sync::OnceCell;
use vhost::{self, Vhost, Vsock};
use vm_memory::GuestMemory;
use vmm_vhost::{
    message::{
        VhostUserConfigFlags, VhostUserInflight, VhostUserMemoryRegion, VhostUserProtocolFeatures,
        VhostUserSingleMemoryRegion, VhostUserVirtioFeatures, VhostUserVringAddrFlags,
        VhostUserVringState,
    },
    Error, Result, SlaveReqHandler, VhostUserSlaveReqHandlerMut,
};

use crate::virtio::{
    base_features,
    vhost::{
        user::device::handler::{create_guest_memory, vmm_va_to_gpa, MappingInfo},
        vsock,
    },
    Queue,
};

static VSOCK_EXECUTOR: OnceCell<Executor> = OnceCell::new();

const MAX_VRING_LEN: u16 = vsock::QUEUE_SIZE;
const NUM_QUEUES: usize = vsock::QUEUE_SIZES.len();
const EVENT_QUEUE: usize = NUM_QUEUES - 1;

struct VsockBackend {
    handle: Vsock,
    cid: u64,
    features: u64,
    protocol_features: VhostUserProtocolFeatures,
    mem: Option<GuestMemory>,
    vmm_maps: Option<Vec<MappingInfo>>,
    queues: [Queue; NUM_QUEUES],
}

impl VsockBackend {
    fn new<P: AsRef<Path>>(cid: u64, vhost_socket: P) -> anyhow::Result<VsockBackend> {
        let handle = Vsock::new(
            OpenOptions::new()
                .read(true)
                .write(true)
                .custom_flags(libc::O_CLOEXEC | libc::O_NONBLOCK)
                .open(vhost_socket)
                .context("failed to open `Vsock` socket")?,
        );

        let features = handle.get_features().context("failed to get features")?;
        let protocol_features = VhostUserProtocolFeatures::MQ | VhostUserProtocolFeatures::CONFIG;
        Ok(VsockBackend {
            handle,
            cid,
            features,
            protocol_features,
            mem: None,
            vmm_maps: None,
            queues: [
                Queue::new(MAX_VRING_LEN),
                Queue::new(MAX_VRING_LEN),
                Queue::new(MAX_VRING_LEN),
            ],
        })
    }
}

fn convert_vhost_error(err: vhost::Error) -> Error {
    use vhost::Error::*;
    match err {
        IoctlError(e) => Error::ReqHandlerError(e),
        _ => Error::SlaveInternalError,
    }
}

impl VhostUserSlaveReqHandlerMut for VsockBackend {
    fn set_owner(&mut self) -> Result<()> {
        self.handle.set_owner().map_err(convert_vhost_error)
    }

    fn reset_owner(&mut self) -> Result<()> {
        self.handle.reset_owner().map_err(convert_vhost_error)
    }

    fn get_features(&mut self) -> Result<u64> {
        let features = base_features(ProtectionType::Unprotected)
            | self.features
            | VhostUserVirtioFeatures::PROTOCOL_FEATURES.bits();
        Ok(features)
    }

    fn set_features(&mut self, features: u64) -> Result<()> {
        self.handle
            .set_features(features & self.features)
            .map_err(convert_vhost_error)
    }

    fn get_protocol_features(&mut self) -> Result<VhostUserProtocolFeatures> {
        Ok(self.protocol_features)
    }

    fn set_protocol_features(&mut self, features: u64) -> Result<()> {
        let unrequested_features = features & !self.protocol_features.bits();
        if unrequested_features != 0 {
            Err(Error::InvalidParam)
        } else {
            Ok(())
        }
    }

    fn set_mem_table(
        &mut self,
        contexts: &[VhostUserMemoryRegion],
        files: Vec<File>,
    ) -> Result<()> {
        let (guest_mem, vmm_maps) = create_guest_memory(contexts, files)?;

        self.handle
            .set_mem_table(&guest_mem)
            .map_err(convert_vhost_error)?;

        self.mem = Some(guest_mem);
        self.vmm_maps = Some(vmm_maps);

        Ok(())
    }

    fn get_queue_num(&mut self) -> Result<u64> {
        Ok(NUM_QUEUES as u64)
    }

    fn set_vring_num(&mut self, index: u32, num: u32) -> Result<()> {
        if index >= NUM_QUEUES as u32 || num == 0 || num > vsock::QUEUE_SIZE.into() {
            return Err(Error::InvalidParam);
        }

        // We checked these values already.
        let index = index as usize;
        let num = num as u16;
        self.queues[index].size = num;

        // The last vq is an event-only vq that is not handled by the kernel.
        if index == EVENT_QUEUE {
            return Ok(());
        }

        self.handle
            .set_vring_num(index, num)
            .map_err(convert_vhost_error)
    }

    fn set_vring_addr(
        &mut self,
        index: u32,
        flags: VhostUserVringAddrFlags,
        descriptor: u64,
        used: u64,
        available: u64,
        log: u64,
    ) -> Result<()> {
        if index >= NUM_QUEUES as u32 {
            return Err(Error::InvalidParam);
        }

        let index = index as usize;

        let mem = self.mem.as_ref().ok_or(Error::InvalidParam)?;
        let maps = self.vmm_maps.as_ref().ok_or(Error::InvalidParam)?;

        let mut queue = &mut self.queues[index];
        queue.desc_table = vmm_va_to_gpa(maps, descriptor)?;
        queue.avail_ring = vmm_va_to_gpa(maps, available)?;
        queue.used_ring = vmm_va_to_gpa(maps, used)?;
        let log_addr = if flags.contains(VhostUserVringAddrFlags::VHOST_VRING_F_LOG) {
            vmm_va_to_gpa(maps, log).map(Some)?
        } else {
            None
        };

        if index == EVENT_QUEUE {
            return Ok(());
        }

        self.handle
            .set_vring_addr(
                mem,
                queue.max_size,
                queue.actual_size(),
                index,
                flags.bits(),
                queue.desc_table,
                queue.used_ring,
                queue.avail_ring,
                log_addr,
            )
            .map_err(convert_vhost_error)
    }

    fn set_vring_base(&mut self, index: u32, base: u32) -> Result<()> {
        if index >= NUM_QUEUES as u32 || base >= vsock::QUEUE_SIZE.into() {
            return Err(Error::InvalidParam);
        }

        let index = index as usize;
        let base = base as u16;

        let mut queue = &mut self.queues[index];
        queue.next_avail = Wrapping(base);
        queue.next_used = Wrapping(base);

        if index == EVENT_QUEUE {
            return Ok(());
        }

        self.handle
            .set_vring_base(index, base)
            .map_err(convert_vhost_error)
    }

    fn get_vring_base(&mut self, index: u32) -> Result<VhostUserVringState> {
        if index >= NUM_QUEUES as u32 {
            return Err(Error::InvalidParam);
        }

        let index = index as usize;
        let next_avail = if index == EVENT_QUEUE {
            self.queues[index].next_avail.0
        } else {
            self.handle
                .get_vring_base(index)
                .map_err(convert_vhost_error)?
        };

        Ok(VhostUserVringState::new(index as u32, next_avail.into()))
    }

    fn set_vring_kick(&mut self, index: u8, fd: Option<File>) -> Result<()> {
        if index >= NUM_QUEUES as u8 {
            return Err(Error::InvalidParam);
        }

        let index = usize::from(index);
        let file = fd.ok_or(Error::InvalidParam)?;

        // Safe because the descriptor is uniquely owned by `file`.
        let event = unsafe { Event::from_raw_descriptor(file.into_raw_descriptor()) };

        // Remove O_NONBLOCK from the kick fd.
        if let Err(e) = clear_fd_flags(event.as_raw_descriptor(), libc::O_NONBLOCK) {
            error!("failed to remove O_NONBLOCK for kick fd: {}", e);
            return Err(Error::InvalidParam);
        }

        if index != EVENT_QUEUE {
            self.handle
                .set_vring_kick(index, &event)
                .map_err(convert_vhost_error)?;
        }

        Ok(())
    }

    fn set_vring_call(&mut self, index: u8, fd: Option<File>) -> Result<()> {
        if index >= NUM_QUEUES as u8 {
            return Err(Error::InvalidParam);
        }

        let index = usize::from(index);
        let file = fd.ok_or(Error::InvalidParam)?;
        // Safe because the descriptor is uniquely owned by `file`.
        let event = unsafe { Event::from_raw_descriptor(file.into_raw_descriptor()) };

        if index != EVENT_QUEUE {
            self.handle
                .set_vring_call(index, &event)
                .map_err(convert_vhost_error)?;
        }

        Ok(())
    }

    fn set_vring_err(&mut self, index: u8, fd: Option<File>) -> Result<()> {
        if index >= NUM_QUEUES as u8 {
            return Err(Error::InvalidParam);
        }

        let index = usize::from(index);
        let file = fd.ok_or(Error::InvalidParam)?;

        // Safe because the descriptor is uniquely owned by `file`.
        let event = unsafe { Event::from_raw_descriptor(file.into_raw_descriptor()) };

        if index == EVENT_QUEUE {
            return Ok(());
        }

        self.handle
            .set_vring_err(index, &event)
            .map_err(convert_vhost_error)
    }

    fn set_vring_enable(&mut self, index: u32, enable: bool) -> Result<()> {
        if index >= NUM_QUEUES as u32 {
            return Err(Error::InvalidParam);
        }

        self.queues[index as usize].ready = enable;

        if index == (EVENT_QUEUE) as u32 {
            return Ok(());
        }

        if self.queues[..EVENT_QUEUE].iter().all(|q| q.ready) {
            // All queues are ready.  Start the device.
            self.handle.set_cid(self.cid).map_err(convert_vhost_error)?;
            self.handle.start().map_err(convert_vhost_error)
        } else if !enable {
            // If we just disabled a vring then stop the device.
            self.handle.stop().map_err(convert_vhost_error)
        } else {
            Ok(())
        }
    }

    fn get_config(
        &mut self,
        offset: u32,
        size: u32,
        _flags: VhostUserConfigFlags,
    ) -> Result<Vec<u8>> {
        let start: usize = offset.try_into().map_err(|_| Error::InvalidParam)?;
        let end: usize = offset
            .checked_add(size)
            .and_then(|e| e.try_into().ok())
            .ok_or(Error::InvalidParam)?;

        if start >= size_of::<Le64>() || end > size_of::<Le64>() {
            return Err(Error::InvalidParam);
        }

        Ok(Le64::from(self.cid).as_slice()[start..end].to_vec())
    }

    fn set_config(
        &mut self,
        _offset: u32,
        _buf: &[u8],
        _flags: VhostUserConfigFlags,
    ) -> Result<()> {
        Err(Error::InvalidOperation)
    }

    fn set_slave_req_fd(&mut self, _vu_req: File) {}

    fn get_inflight_fd(
        &mut self,
        _inflight: &VhostUserInflight,
    ) -> Result<(VhostUserInflight, File)> {
        Err(Error::InvalidOperation)
    }

    fn set_inflight_fd(&mut self, _inflight: &VhostUserInflight, _file: File) -> Result<()> {
        Err(Error::InvalidOperation)
    }

    fn get_max_mem_slots(&mut self) -> Result<u64> {
        Err(Error::InvalidOperation)
    }

    fn add_mem_region(&mut self, _region: &VhostUserSingleMemoryRegion, _fd: File) -> Result<()> {
        Err(Error::InvalidOperation)
    }

    fn remove_mem_region(&mut self, _region: &VhostUserSingleMemoryRegion) -> Result<()> {
        Err(Error::InvalidOperation)
    }
}

async fn run_device<P: AsRef<Path>>(
    ex: &Executor,
    socket: P,
    backend: Arc<Mutex<VsockBackend>>,
) -> anyhow::Result<()> {
    let listener = UnixListener::bind(socket)
        .map(UnlinkUnixListener)
        .context("failed to bind socket")?;
    let (socket, _) = ex
        .spawn_blocking(move || listener.accept())
        .await
        .context("failed to accept socket connection")?;

    let mut req_handler = SlaveReqHandler::from_stream(socket, backend);
    let h = SafeDescriptor::try_from(&req_handler as &dyn AsRawFd)
        .map(AsyncWrapper::new)
        .expect("failed to get safe descriptor for handler");
    let handler_source = ex.async_from(h).context("failed to create async handler")?;

    loop {
        handler_source
            .wait_readable()
            .await
            .context("failed to wait for vhost socket to become readable")?;
        req_handler
            .handle_request()
            .context("failed to handle vhost request")?;
    }
}

/// Returns an error if the given `args` is invalid or the device fails to run.
pub fn run_vsock_device(program_name: &str, args: std::env::Args) -> anyhow::Result<()> {
    let mut opts = Options::new();
    opts.optflag("h", "help", "print this help menu");
    opts.optopt(
        "s",
        "socket",
        "path to bind a listening vhost-user socket",
        "PATH",
    );
    opts.optopt("c", "cid", "the vsock context id for this device", "INT");
    opts.optopt(
        "",
        "vhost-socket",
        "path to the vhost-vsock control socket (default: \"/dev/vhost-vsock\")",
        "PATH",
    );

    let matches = match opts.parse(args) {
        Ok(m) => m,
        Err(e) => {
            bail!("failed to parse arguments: {}", e);
        }
    };

    if matches.opt_present("h") {
        println!("{}", opts.usage(program_name));
        return Ok(());
    }

    // We can safely `unwrap()` this because it is a required option.
    let socket = if let Some(s) = matches.opt_str("socket") {
        s
    } else {
        println!("`--socket` is required");
        println!("{}", opts.short_usage(program_name));
        return Ok(());
    };

    let cid = if let Some(cid) = matches
        .opt_str("cid")
        .as_deref()
        .map(str::parse)
        .transpose()?
    {
        cid
    } else {
        println!("`--cid` is required");
        println!("{}", opts.short_usage(program_name));
        return Ok(());
    };

    let ex = Executor::new().context("failed to create executor")?;
    let _ = VSOCK_EXECUTOR.set(ex.clone());

    let vhost_socket = matches
        .opt_str("vhost-socket")
        .unwrap_or_else(|| "/dev/vhost-vsock".to_string());

    let backend = VsockBackend::new(cid, vhost_socket)
        .map(Mutex::new)
        .map(Arc::new)?;

    // TODO: Replace the `and_then` with `Result::flatten` once it is stabilized.
    ex.run_until(run_device(&ex, socket, backend))
        .context("failed to run vsock device")
        .and_then(convert::identity)
}
