// Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use std::fmt::{self, Display};
use std::io::{self, Write};
use std::mem;
use std::net::Ipv4Addr;
use std::os::raw::c_uint;
use std::os::unix::io::{AsRawFd, RawFd};
use std::result;
use std::sync::Arc;
use std::thread;

use base::Error as SysError;
use base::{error, warn, EventFd, PollContext, PollToken, WatchingEvents};
use data_model::{DataInit, Le16, Le64};
use net_util::{Error as TapError, MacAddress, TapT};
use virtio_sys::virtio_net::{
    virtio_net_hdr_v1, VIRTIO_NET_CTRL_GUEST_OFFLOADS, VIRTIO_NET_CTRL_GUEST_OFFLOADS_SET,
    VIRTIO_NET_CTRL_MQ, VIRTIO_NET_CTRL_MQ_VQ_PAIRS_SET, VIRTIO_NET_ERR, VIRTIO_NET_OK,
};
use virtio_sys::{vhost, virtio_net};
use vm_memory::GuestMemory;

use super::{
    copy_config, DescriptorError, Interrupt, Queue, Reader, VirtioDevice, Writer, TYPE_NET,
};

const QUEUE_SIZE: u16 = 256;

#[derive(Debug)]
pub enum NetError {
    /// Creating kill eventfd failed.
    CreateKillEventFd(SysError),
    /// Creating PollContext failed.
    CreatePollContext(SysError),
    /// Cloning kill eventfd failed.
    CloneKillEventFd(SysError),
    /// Descriptor chain was invalid.
    DescriptorChain(DescriptorError),
    /// Removing EPOLLIN from the tap fd events failed.
    PollDisableTap(SysError),
    /// Adding EPOLLIN to the tap fd events failed.
    PollEnableTap(SysError),
    /// Error while polling for events.
    PollError(SysError),
    /// Error reading data from control queue.
    ReadCtrlData(io::Error),
    /// Error reading header from control queue.
    ReadCtrlHeader(io::Error),
    /// There are no more available descriptors to receive into.
    RxDescriptorsExhausted,
    /// Open tap device failed.
    TapOpen(TapError),
    /// Setting tap IP failed.
    TapSetIp(TapError),
    /// Setting tap netmask failed.
    TapSetNetmask(TapError),
    /// Setting tap mac address failed.
    TapSetMacAddress(TapError),
    /// Setting tap interface offload flags failed.
    TapSetOffload(TapError),
    /// Setting vnet header size failed.
    TapSetVnetHdrSize(TapError),
    /// Enabling tap interface failed.
    TapEnable(TapError),
    /// Validating tap interface failed.
    TapValidate(String),
    /// Failed writing an ack in response to a control message.
    WriteAck(io::Error),
    /// Writing to a buffer in the guest failed.
    WriteBuffer(io::Error),
}

impl Display for NetError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::NetError::*;

        match self {
            CreateKillEventFd(e) => write!(f, "failed to create kill eventfd: {}", e),
            CreatePollContext(e) => write!(f, "failed to create poll context: {}", e),
            CloneKillEventFd(e) => write!(f, "failed to clone kill eventfd: {}", e),
            DescriptorChain(e) => write!(f, "failed to valildate descriptor chain: {}", e),
            PollDisableTap(e) => write!(f, "failed to disable EPOLLIN on tap fd: {}", e),
            PollEnableTap(e) => write!(f, "failed to enable EPOLLIN on tap fd: {}", e),
            PollError(e) => write!(f, "error while polling for events: {}", e),
            ReadCtrlData(e) => write!(f, "failed to read control message data: {}", e),
            ReadCtrlHeader(e) => write!(f, "failed to read control message header: {}", e),
            RxDescriptorsExhausted => write!(f, "no rx descriptors available"),
            TapOpen(e) => write!(f, "failed to open tap device: {}", e),
            TapSetIp(e) => write!(f, "failed to set tap IP: {}", e),
            TapSetNetmask(e) => write!(f, "failed to set tap netmask: {}", e),
            TapSetMacAddress(e) => write!(f, "failed to set tap mac address: {}", e),
            TapSetOffload(e) => write!(f, "failed to set tap interface offload flags: {}", e),
            TapSetVnetHdrSize(e) => write!(f, "failed to set vnet header size: {}", e),
            TapEnable(e) => write!(f, "failed to enable tap interface: {}", e),
            TapValidate(s) => write!(f, "failed to validate tap interface: {}", s),
            WriteAck(e) => write!(f, "failed to write control message ack: {}", e),
            WriteBuffer(e) => write!(f, "failed to write to guest buffer: {}", e),
        }
    }
}

#[repr(C, packed)]
#[derive(Debug, Clone, Copy)]
pub struct virtio_net_ctrl_hdr {
    pub class: u8,
    pub cmd: u8,
}

// Safe because it only has data and has no implicit padding.
unsafe impl DataInit for virtio_net_ctrl_hdr {}

fn virtio_features_to_tap_offload(features: u64) -> c_uint {
    let mut tap_offloads: c_uint = 0;
    if features & (1 << virtio_net::VIRTIO_NET_F_GUEST_CSUM) != 0 {
        tap_offloads |= net_sys::TUN_F_CSUM;
    }
    if features & (1 << virtio_net::VIRTIO_NET_F_GUEST_TSO4) != 0 {
        tap_offloads |= net_sys::TUN_F_TSO4;
    }
    if features & (1 << virtio_net::VIRTIO_NET_F_GUEST_TSO6) != 0 {
        tap_offloads |= net_sys::TUN_F_TSO6;
    }
    if features & (1 << virtio_net::VIRTIO_NET_F_GUEST_ECN) != 0 {
        tap_offloads |= net_sys::TUN_F_TSO_ECN;
    }
    if features & (1 << virtio_net::VIRTIO_NET_F_GUEST_UFO) != 0 {
        tap_offloads |= net_sys::TUN_F_UFO;
    }

    tap_offloads
}

#[derive(Debug, Clone, Copy, Default)]
#[repr(C)]
struct VirtioNetConfig {
    mac: [u8; 6],
    status: Le16,
    max_vq_pairs: Le16,
    mtu: Le16,
}

// Safe because it only has data and has no implicit padding.
unsafe impl DataInit for VirtioNetConfig {}

struct Worker<T: TapT> {
    interrupt: Arc<Interrupt>,
    mem: GuestMemory,
    rx_queue: Queue,
    tx_queue: Queue,
    ctrl_queue: Option<Queue>,
    tap: T,
    acked_features: u64,
    vq_pairs: u16,
    kill_evt: EventFd,
}

impl<T> Worker<T>
where
    T: TapT,
{
    fn process_rx(&mut self) -> result::Result<(), NetError> {
        let mut needs_interrupt = false;
        let mut exhausted_queue = false;

        // Read as many frames as possible.
        loop {
            let desc_chain = match self.rx_queue.peek(&self.mem) {
                Some(desc) => desc,
                None => {
                    exhausted_queue = true;
                    break;
                }
            };

            let index = desc_chain.index;
            let bytes_written = match Writer::new(&self.mem, desc_chain) {
                Ok(mut writer) => {
                    match writer.write_from(&mut self.tap, writer.available_bytes()) {
                        Ok(_) => {}
                        Err(ref e) if e.kind() == io::ErrorKind::WriteZero => {
                            warn!("net: rx: buffer is too small to hold frame");
                            break;
                        }
                        Err(ref e) if e.kind() == io::ErrorKind::WouldBlock => {
                            // No more to read from the tap.
                            break;
                        }
                        Err(e) => {
                            warn!("net: rx: failed to write slice: {}", e);
                            return Err(NetError::WriteBuffer(e));
                        }
                    };

                    writer.bytes_written() as u32
                }
                Err(e) => {
                    error!("net: failed to create Writer: {}", e);
                    0
                }
            };

            if bytes_written > 0 {
                self.rx_queue.pop_peeked(&self.mem);
                self.rx_queue.add_used(&self.mem, index, bytes_written);
                needs_interrupt = true;
            }
        }

        if needs_interrupt {
            self.interrupt.signal_used_queue(self.rx_queue.vector);
        }

        if exhausted_queue {
            Err(NetError::RxDescriptorsExhausted)
        } else {
            Ok(())
        }
    }

    fn process_tx(&mut self) {
        while let Some(desc_chain) = self.tx_queue.pop(&self.mem) {
            let index = desc_chain.index;

            match Reader::new(&self.mem, desc_chain) {
                Ok(mut reader) => {
                    let expected_count = reader.available_bytes();
                    match reader.read_to(&mut self.tap, expected_count) {
                        Ok(count) => {
                            // Tap writes must be done in one call. If the entire frame was not
                            // written, it's an error.
                            if count != expected_count {
                                error!(
                                    "net: tx: wrote only {} bytes of {} byte frame",
                                    count, expected_count
                                );
                            }
                        }
                        Err(e) => error!("net: tx: failed to write frame to tap: {}", e),
                    }
                }
                Err(e) => error!("net: failed to create Reader: {}", e),
            }

            self.tx_queue.add_used(&self.mem, index, 0);
        }

        self.interrupt.signal_used_queue(self.tx_queue.vector);
    }

    fn process_ctrl(&mut self) -> Result<(), NetError> {
        let ctrl_queue = match self.ctrl_queue.as_mut() {
            Some(queue) => queue,
            None => return Ok(()),
        };

        while let Some(desc_chain) = ctrl_queue.pop(&self.mem) {
            let index = desc_chain.index;

            let mut reader =
                Reader::new(&self.mem, desc_chain.clone()).map_err(NetError::DescriptorChain)?;
            let mut writer =
                Writer::new(&self.mem, desc_chain).map_err(NetError::DescriptorChain)?;
            let ctrl_hdr: virtio_net_ctrl_hdr =
                reader.read_obj().map_err(NetError::ReadCtrlHeader)?;

            match ctrl_hdr.class as c_uint {
                VIRTIO_NET_CTRL_GUEST_OFFLOADS => {
                    if ctrl_hdr.cmd != VIRTIO_NET_CTRL_GUEST_OFFLOADS_SET as u8 {
                        error!(
                            "invalid cmd for VIRTIO_NET_CTRL_GUEST_OFFLOADS: {}",
                            ctrl_hdr.cmd
                        );
                        let ack = VIRTIO_NET_ERR as u8;
                        writer.write_all(&[ack]).map_err(NetError::WriteAck)?;
                        ctrl_queue.add_used(&self.mem, index, 0);
                        continue;
                    }
                    let offloads: Le64 = reader.read_obj().map_err(NetError::ReadCtrlData)?;
                    let tap_offloads = virtio_features_to_tap_offload(offloads.into());
                    self.tap
                        .set_offload(tap_offloads)
                        .map_err(NetError::TapSetOffload)?;
                    let ack = VIRTIO_NET_OK as u8;
                    writer.write_all(&[ack]).map_err(NetError::WriteAck)?;
                }
                VIRTIO_NET_CTRL_MQ => {
                    if ctrl_hdr.cmd == VIRTIO_NET_CTRL_MQ_VQ_PAIRS_SET as u8 {
                        let pairs: Le16 = reader.read_obj().map_err(NetError::ReadCtrlData)?;
                        // Simple handle it now
                        if self.acked_features & 1 << virtio_net::VIRTIO_NET_F_MQ == 0
                            || pairs.to_native() != self.vq_pairs
                        {
                            error!("Invalid VQ_PAIRS_SET cmd, driver request pairs: {}, device vq pairs: {}",
                                   pairs.to_native(), self.vq_pairs);
                            let ack = VIRTIO_NET_ERR as u8;
                            writer.write_all(&[ack]).map_err(NetError::WriteAck)?;
                            ctrl_queue.add_used(&self.mem, index, 0);
                            continue;
                        }
                        let ack = VIRTIO_NET_OK as u8;
                        writer.write_all(&[ack]).map_err(NetError::WriteAck)?;
                    }
                }
                _ => warn!(
                    "unimplemented class for VIRTIO_NET_CTRL_GUEST_OFFLOADS: {}",
                    ctrl_hdr.class
                ),
            }

            ctrl_queue.add_used(&self.mem, index, 0);
        }

        self.interrupt.signal_used_queue(ctrl_queue.vector);
        Ok(())
    }

    fn run(
        &mut self,
        rx_queue_evt: EventFd,
        tx_queue_evt: EventFd,
        ctrl_queue_evt: Option<EventFd>,
    ) -> Result<(), NetError> {
        #[derive(PollToken)]
        enum Token {
            // A frame is available for reading from the tap device to receive in the guest.
            RxTap,
            // The guest has made a buffer available to receive a frame into.
            RxQueue,
            // The transmit queue has a frame that is ready to send from the guest.
            TxQueue,
            // The control queue has a message.
            CtrlQueue,
            // Check if any interrupts need to be re-asserted.
            InterruptResample,
            // crosvm has requested the device to shut down.
            Kill,
        }

        let poll_ctx: PollContext<Token> = PollContext::build_with(&[
            (&self.tap, Token::RxTap),
            (&rx_queue_evt, Token::RxQueue),
            (&tx_queue_evt, Token::TxQueue),
            (&self.kill_evt, Token::Kill),
        ])
        .map_err(NetError::CreatePollContext)?;

        if let Some(ctrl_evt) = &ctrl_queue_evt {
            poll_ctx
                .add(ctrl_evt, Token::CtrlQueue)
                .map_err(NetError::CreatePollContext)?;
            // Let CtrlQueue's thread handle InterruptResample also.
            poll_ctx
                .add(self.interrupt.get_resample_evt(), Token::InterruptResample)
                .map_err(NetError::CreatePollContext)?;
        }

        let mut tap_polling_enabled = true;
        'poll: loop {
            let events = poll_ctx.wait().map_err(NetError::PollError)?;
            for event in events.iter_readable() {
                match event.token() {
                    Token::RxTap => match self.process_rx() {
                        Ok(()) => {}
                        Err(NetError::RxDescriptorsExhausted) => {
                            poll_ctx
                                .modify(&self.tap, WatchingEvents::empty(), Token::RxTap)
                                .map_err(NetError::PollDisableTap)?;
                            tap_polling_enabled = false;
                        }
                        Err(e) => return Err(e),
                    },
                    Token::RxQueue => {
                        if let Err(e) = rx_queue_evt.read() {
                            error!("net: error reading rx queue EventFd: {}", e);
                            break 'poll;
                        }
                        if !tap_polling_enabled {
                            poll_ctx
                                .modify(&self.tap, WatchingEvents::empty().set_read(), Token::RxTap)
                                .map_err(NetError::PollEnableTap)?;
                            tap_polling_enabled = true;
                        }
                    }
                    Token::TxQueue => {
                        if let Err(e) = tx_queue_evt.read() {
                            error!("net: error reading tx queue EventFd: {}", e);
                            break 'poll;
                        }
                        self.process_tx();
                    }
                    Token::CtrlQueue => {
                        if let Some(ctrl_evt) = &ctrl_queue_evt {
                            if let Err(e) = ctrl_evt.read() {
                                error!("net: error reading ctrl queue EventFd: {}", e);
                                break 'poll;
                            }
                        } else {
                            break 'poll;
                        }
                        if let Err(e) = self.process_ctrl() {
                            error!("net: failed to process control message: {}", e);
                            break 'poll;
                        }
                    }
                    Token::InterruptResample => {
                        self.interrupt.interrupt_resample();
                    }
                    Token::Kill => {
                        let _ = self.kill_evt.read();
                        break 'poll;
                    }
                }
            }
        }
        Ok(())
    }
}

pub struct Net<T: TapT> {
    queue_sizes: Box<[u16]>,
    workers_kill_evt: Vec<EventFd>,
    kill_evts: Vec<EventFd>,
    worker_threads: Vec<thread::JoinHandle<Worker<T>>>,
    taps: Vec<T>,
    avail_features: u64,
    acked_features: u64,
}

impl<T> Net<T>
where
    T: TapT,
{
    /// Create a new virtio network device with the given IP address and
    /// netmask.
    pub fn new(
        ip_addr: Ipv4Addr,
        netmask: Ipv4Addr,
        mac_addr: MacAddress,
        vq_pairs: u16,
    ) -> Result<Net<T>, NetError> {
        let multi_queue = if vq_pairs > 1 { true } else { false };
        let tap: T = T::new(true, multi_queue).map_err(NetError::TapOpen)?;
        tap.set_ip_addr(ip_addr).map_err(NetError::TapSetIp)?;
        tap.set_netmask(netmask).map_err(NetError::TapSetNetmask)?;
        tap.set_mac_address(mac_addr)
            .map_err(NetError::TapSetMacAddress)?;

        tap.enable().map_err(NetError::TapEnable)?;

        Net::from(tap, vq_pairs)
    }

    /// Creates a new virtio network device from a tap device that has already been
    /// configured.
    pub fn from(tap: T, vq_pairs: u16) -> Result<Net<T>, NetError> {
        let taps = tap.into_mq_taps(vq_pairs).map_err(NetError::TapOpen)?;

        // This would also validate a tap created by Self::new(), but that's a good thing as it
        // would ensure that any changes in the creation procedure are matched in the validation.
        // Plus we still need to set the offload and vnet_hdr_size values.
        for tap in &taps {
            validate_and_configure_tap(tap, vq_pairs)?;
        }

        let mut avail_features = 1 << virtio_net::VIRTIO_NET_F_GUEST_CSUM
            | 1 << virtio_net::VIRTIO_NET_F_CSUM
            | 1 << virtio_net::VIRTIO_NET_F_CTRL_VQ
            | 1 << virtio_net::VIRTIO_NET_F_CTRL_GUEST_OFFLOADS
            | 1 << virtio_net::VIRTIO_NET_F_GUEST_TSO4
            | 1 << virtio_net::VIRTIO_NET_F_GUEST_UFO
            | 1 << virtio_net::VIRTIO_NET_F_HOST_TSO4
            | 1 << virtio_net::VIRTIO_NET_F_HOST_UFO
            | 1 << vhost::VIRTIO_F_VERSION_1;

        if vq_pairs > 1 {
            avail_features |= 1 << virtio_net::VIRTIO_NET_F_MQ;
        }

        let mut kill_evts: Vec<EventFd> = Vec::new();
        let mut workers_kill_evt: Vec<EventFd> = Vec::new();
        for _ in 0..taps.len() {
            let kill_evt = EventFd::new().map_err(NetError::CreateKillEventFd)?;
            let worker_kill_evt = kill_evt.try_clone().map_err(NetError::CloneKillEventFd)?;
            kill_evts.push(kill_evt);
            workers_kill_evt.push(worker_kill_evt);
        }

        Ok(Net {
            queue_sizes: vec![QUEUE_SIZE; (vq_pairs * 2 + 1) as usize].into_boxed_slice(),
            workers_kill_evt,
            kill_evts,
            worker_threads: Vec::new(),
            taps,
            avail_features,
            acked_features: 0u64,
        })
    }

    fn build_config(&self) -> VirtioNetConfig {
        let vq_pairs = self.queue_sizes.len() as u16 / 2;

        VirtioNetConfig {
            max_vq_pairs: Le16::from(vq_pairs),
            // Other field has meaningful value when the corresponding feature
            // is enabled, but all these features aren't supported now.
            // So set them to default.
            ..Default::default()
        }
    }
}

// Ensure that the tap interface has the correct flags and sets the offload and VNET header size
// to the appropriate values.
fn validate_and_configure_tap<T: TapT>(tap: &T, vq_pairs: u16) -> Result<(), NetError> {
    let flags = tap.if_flags();
    let mut required_flags = vec![
        (net_sys::IFF_TAP, "IFF_TAP"),
        (net_sys::IFF_NO_PI, "IFF_NO_PI"),
        (net_sys::IFF_VNET_HDR, "IFF_VNET_HDR"),
    ];
    if vq_pairs > 1 {
        required_flags.push((net_sys::IFF_MULTI_QUEUE, "IFF_MULTI_QUEUE"));
    }
    let missing_flags = required_flags
        .iter()
        .filter_map(
            |(value, name)| {
                if value & flags == 0 {
                    Some(name)
                } else {
                    None
                }
            },
        )
        .collect::<Vec<_>>();

    if !missing_flags.is_empty() {
        return Err(NetError::TapValidate(format!(
            "Missing flags: {:?}",
            missing_flags
        )));
    }

    let vnet_hdr_size = mem::size_of::<virtio_net_hdr_v1>() as i32;
    tap.set_vnet_hdr_size(vnet_hdr_size)
        .map_err(NetError::TapSetVnetHdrSize)?;

    Ok(())
}

impl<T> Drop for Net<T>
where
    T: TapT,
{
    fn drop(&mut self) {
        let len = self.kill_evts.len();
        for i in 0..len {
            // Only kill the child if it claimed its eventfd.
            if self.workers_kill_evt.get(i).is_none() {
                if let Some(kill_evt) = self.kill_evts.get(i) {
                    // Ignore the result because there is nothing we can do about it.
                    let _ = kill_evt.write(1);
                }
            }
        }

        let len = self.worker_threads.len();
        for _ in 0..len {
            let _ = self.worker_threads.remove(0).join();
        }
    }
}

impl<T> VirtioDevice for Net<T>
where
    T: 'static + TapT,
{
    fn keep_fds(&self) -> Vec<RawFd> {
        let mut keep_fds = Vec::new();

        for tap in &self.taps {
            keep_fds.push(tap.as_raw_fd());
        }

        for worker_kill_evt in &self.workers_kill_evt {
            keep_fds.push(worker_kill_evt.as_raw_fd());
        }
        for kill_evt in &self.kill_evts {
            keep_fds.push(kill_evt.as_raw_fd());
        }

        keep_fds
    }

    fn device_type(&self) -> u32 {
        TYPE_NET
    }

    fn queue_max_sizes(&self) -> &[u16] {
        &self.queue_sizes
    }

    fn features(&self) -> u64 {
        self.avail_features
    }

    fn ack_features(&mut self, value: u64) {
        let mut v = value;

        // Check if the guest is ACK'ing a feature that we didn't claim to have.
        let unrequested_features = v & !self.avail_features;
        if unrequested_features != 0 {
            warn!("net: virtio net got unknown feature ack: {:x}", v);

            // Don't count these features as acked.
            v &= !unrequested_features;
        }
        self.acked_features |= v;

        // Set offload flags to match acked virtio features.
        if let Some(tap) = self.taps.first() {
            if let Err(e) = tap.set_offload(virtio_features_to_tap_offload(self.acked_features)) {
                warn!(
                    "net: failed to set tap offload to match acked features: {}",
                    e
                );
            }
        }
    }

    fn read_config(&self, offset: u64, data: &mut [u8]) {
        let config_space = self.build_config();
        copy_config(data, 0, config_space.as_slice(), offset);
    }

    fn activate(
        &mut self,
        mem: GuestMemory,
        interrupt: Interrupt,
        mut queues: Vec<Queue>,
        mut queue_evts: Vec<EventFd>,
    ) {
        if queues.len() != self.queue_sizes.len() || queue_evts.len() != self.queue_sizes.len() {
            error!(
                "net: expected {} queues, got {}",
                self.queue_sizes.len(),
                queues.len()
            );
            return;
        }

        let vq_pairs = self.queue_sizes.len() / 2;
        if self.taps.len() != vq_pairs {
            error!("net: expected {} taps, got {}", vq_pairs, self.taps.len());
            return;
        }
        if self.workers_kill_evt.len() != vq_pairs {
            error!(
                "net: expected {} worker_kill_evt, got {}",
                vq_pairs,
                self.workers_kill_evt.len()
            );
            return;
        }
        let interrupt_arc = Arc::new(interrupt);
        for i in 0..vq_pairs {
            let tap = self.taps.remove(0);
            let acked_features = self.acked_features;
            let interrupt = interrupt_arc.clone();
            let memory = mem.clone();
            let kill_evt = self.workers_kill_evt.remove(0);
            // Queues alternate between rx0, tx0, rx1, tx1, ..., rxN, txN, ctrl.
            let rx_queue = queues.remove(0);
            let tx_queue = queues.remove(0);
            let ctrl_queue = if i == 0 {
                Some(queues.remove(queues.len() - 1))
            } else {
                None
            };
            let pairs = vq_pairs as u16;
            let rx_queue_evt = queue_evts.remove(0);
            let tx_queue_evt = queue_evts.remove(0);
            let ctrl_queue_evt = if i == 0 {
                Some(queue_evts.remove(queue_evts.len() - 1))
            } else {
                None
            };
            let worker_result = thread::Builder::new()
                .name(format!("virtio_net worker {}", i))
                .spawn(move || {
                    let mut worker = Worker {
                        interrupt,
                        mem: memory,
                        rx_queue,
                        tx_queue,
                        ctrl_queue,
                        tap,
                        acked_features,
                        vq_pairs: pairs,
                        kill_evt,
                    };
                    let result = worker.run(rx_queue_evt, tx_queue_evt, ctrl_queue_evt);
                    if let Err(e) = result {
                        error!("net worker thread exited with error: {}", e);
                    }
                    worker
                });

            match worker_result {
                Err(e) => {
                    error!("failed to spawn virtio_net worker: {}", e);
                    return;
                }
                Ok(join_handle) => self.worker_threads.push(join_handle),
            }
        }
    }

    fn reset(&mut self) -> bool {
        let len = self.kill_evts.len();
        for i in 0..len {
            // Only kill the child if it claimed its eventfd.
            if self.workers_kill_evt.get(i).is_none() {
                if let Some(kill_evt) = self.kill_evts.get(i) {
                    if kill_evt.write(1).is_err() {
                        error!("{}: failed to notify the kill event", self.debug_label());
                        return false;
                    }
                }
            }
        }

        let len = self.worker_threads.len();
        for _ in 0..len {
            match self.worker_threads.remove(0).join() {
                Err(_) => {
                    error!("{}: failed to get back resources", self.debug_label());
                    return false;
                }
                Ok(worker) => {
                    self.taps.push(worker.tap);
                    self.workers_kill_evt.push(worker.kill_evt);
                }
            }
        }

        return true;
    }
}
