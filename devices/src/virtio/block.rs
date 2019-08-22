// Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use std::fmt::{self, Display};
use std::io::{self, Seek, SeekFrom};
use std::mem::size_of;
use std::os::unix::io::{AsRawFd, RawFd};
use std::result;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;
use std::u32;

use sync::Mutex;
use sys_util::Error as SysError;
use sys_util::Result as SysResult;
use sys_util::{
    error, info, warn, EventFd, FileReadWriteVolatile, FileSetLen, FileSync, GuestMemory,
    PollContext, PollToken, PunchHole, TimerFd, WriteZeroes,
};

use data_model::{DataInit, Le16, Le32, Le64};
use msg_socket::{MsgReceiver, MsgSender};
use vm_control::{DiskControlCommand, DiskControlResponseSocket, DiskControlResult};

use super::{
    copy_config, DescriptorChain, DescriptorError, Queue, Reader, VirtioDevice, Writer,
    INTERRUPT_STATUS_CONFIG_CHANGED, INTERRUPT_STATUS_USED_RING, TYPE_BLOCK, VIRTIO_F_VERSION_1,
};

const QUEUE_SIZE: u16 = 256;
const QUEUE_SIZES: &[u16] = &[QUEUE_SIZE];
const SECTOR_SHIFT: u8 = 9;
const SECTOR_SIZE: u64 = 0x01 << SECTOR_SHIFT;
const MAX_DISCARD_SECTORS: u32 = u32::MAX;
const MAX_WRITE_ZEROES_SECTORS: u32 = u32::MAX;
// Arbitrary limits for number of discard/write zeroes segments.
const MAX_DISCARD_SEG: u32 = 32;
const MAX_WRITE_ZEROES_SEG: u32 = 32;
// Hard-coded to 64 KiB (in 512-byte sectors) for now,
// but this should probably be based on cluster size for qcow.
const DISCARD_SECTOR_ALIGNMENT: u32 = 128;

const VIRTIO_BLK_T_IN: u32 = 0;
const VIRTIO_BLK_T_OUT: u32 = 1;
const VIRTIO_BLK_T_FLUSH: u32 = 4;
const VIRTIO_BLK_T_DISCARD: u32 = 11;
const VIRTIO_BLK_T_WRITE_ZEROES: u32 = 13;

const VIRTIO_BLK_S_OK: u8 = 0;
const VIRTIO_BLK_S_IOERR: u8 = 1;
const VIRTIO_BLK_S_UNSUPP: u8 = 2;

const VIRTIO_BLK_F_RO: u32 = 5;
const VIRTIO_BLK_F_BLK_SIZE: u32 = 6;
const VIRTIO_BLK_F_FLUSH: u32 = 9;
const VIRTIO_BLK_F_DISCARD: u32 = 13;
const VIRTIO_BLK_F_WRITE_ZEROES: u32 = 14;

#[derive(Copy, Clone, Debug, Default)]
#[repr(C)]
struct virtio_blk_geometry {
    cylinders: Le16,
    heads: u8,
    sectors: u8,
}

// Safe because it only has data and has no implicit padding.
unsafe impl DataInit for virtio_blk_geometry {}

#[derive(Copy, Clone, Debug, Default)]
#[repr(C)]
struct virtio_blk_topology {
    physical_block_exp: u8,
    alignment_offset: u8,
    min_io_size: Le16,
    opt_io_size: Le32,
}

// Safe because it only has data and has no implicit padding.
unsafe impl DataInit for virtio_blk_topology {}

#[derive(Copy, Clone, Debug, Default)]
#[repr(C)]
struct virtio_blk_config {
    capacity: Le64,
    size_max: Le32,
    seg_max: Le32,
    geometry: virtio_blk_geometry,
    blk_size: Le32,
    topology: virtio_blk_topology,
    writeback: u8,
    unused0: [u8; 3],
    max_discard_sectors: Le32,
    max_discard_seg: Le32,
    discard_sector_alignment: Le32,
    max_write_zeroes_sectors: Le32,
    max_write_zeroes_seg: Le32,
    write_zeroes_may_unmap: u8,
    unused1: [u8; 3],
}

// Safe because it only has data and has no implicit padding.
unsafe impl DataInit for virtio_blk_req_header {}

#[derive(Copy, Clone, Debug, Default)]
#[repr(C)]
struct virtio_blk_req_header {
    req_type: Le32,
    reserved: Le32,
    sector: Le64,
}

// Safe because it only has data and has no implicit padding.
unsafe impl DataInit for virtio_blk_config {}

#[derive(Copy, Clone, Debug, Default)]
#[repr(C)]
struct virtio_blk_discard_write_zeroes {
    sector: Le64,
    num_sectors: Le32,
    flags: Le32,
}

const VIRTIO_BLK_DISCARD_WRITE_ZEROES_FLAG_UNMAP: u32 = 1 << 0;

// Safe because it only has data and has no implicit padding.
unsafe impl DataInit for virtio_blk_discard_write_zeroes {}

pub trait DiskFile:
    FileSetLen + FileSync + FileReadWriteVolatile + PunchHole + Seek + WriteZeroes
{
}
impl<D: FileSetLen + FileSync + PunchHole + FileReadWriteVolatile + Seek + WriteZeroes> DiskFile
    for D
{
}

#[derive(Debug)]
enum ExecuteError {
    Descriptor(DescriptorError),
    /// Error arming the flush timer.
    Flush(io::Error),
    ReadIo {
        length: usize,
        sector: u64,
        desc_error: DescriptorError,
    },
    ShortRead {
        sector: u64,
        expected_length: usize,
        actual_length: usize,
    },
    Seek {
        ioerr: io::Error,
        sector: u64,
    },
    TimerFd(SysError),
    WriteIo {
        length: usize,
        sector: u64,
        desc_error: DescriptorError,
    },
    ShortWrite {
        sector: u64,
        expected_length: usize,
        actual_length: usize,
    },
    DiscardWriteZeroes {
        ioerr: Option<io::Error>,
        sector: u64,
        num_sectors: u32,
        flags: u32,
    },
    ReadOnly {
        request_type: u32,
    },
    OutOfRange,
    MissingStatus,
    Unsupported(u32),
}

impl Display for ExecuteError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::ExecuteError::*;

        match self {
            Descriptor(e) => write!(f, "virtio descriptor error: {}", e),
            Flush(e) => write!(f, "failed to flush: {}", e),
            ReadIo {
                length,
                sector,
                desc_error,
            } => write!(
                f,
                "io error reading {} bytes from sector {}: {}",
                length, sector, desc_error,
            ),
            ShortRead {
                sector,
                expected_length,
                actual_length,
            } => write!(
                f,
                "short read: {} bytes of {} at sector {}",
                actual_length, expected_length, sector
            ),
            Seek { ioerr, sector } => write!(f, "failed to seek to sector {}: {}", sector, ioerr),
            TimerFd(e) => write!(f, "{}", e),
            WriteIo {
                length,
                sector,
                desc_error,
            } => write!(
                f,
                "io error writing {} bytes to sector {}: {}",
                length, sector, desc_error,
            ),
            ShortWrite {
                sector,
                expected_length,
                actual_length,
            } => write!(
                f,
                "short write: {} bytes of {} at sector {}",
                actual_length, expected_length, sector
            ),
            DiscardWriteZeroes {
                ioerr: Some(ioerr),
                sector,
                num_sectors,
                flags,
            } => write!(
                f,
                "failed to perform discard or write zeroes; sector={} num_sectors={} flags={}; {}",
                sector, num_sectors, flags, ioerr,
            ),
            DiscardWriteZeroes {
                ioerr: None,
                sector,
                num_sectors,
                flags,
            } => write!(
                f,
                "failed to perform discard or write zeroes; sector={} num_sectors={} flags={}",
                sector, num_sectors, flags,
            ),
            ReadOnly { request_type } => write!(f, "read only; request_type={}", request_type),
            OutOfRange => write!(f, "out of range"),
            MissingStatus => write!(f, "not enough space in descriptor chain to write status"),
            Unsupported(n) => write!(f, "unsupported ({})", n),
        }
    }
}

impl ExecuteError {
    fn status(&self) -> u8 {
        match self {
            ExecuteError::Descriptor(_) => VIRTIO_BLK_S_IOERR,
            ExecuteError::Flush(_) => VIRTIO_BLK_S_IOERR,
            ExecuteError::ReadIo { .. } => VIRTIO_BLK_S_IOERR,
            ExecuteError::ShortRead { .. } => VIRTIO_BLK_S_IOERR,
            ExecuteError::Seek { .. } => VIRTIO_BLK_S_IOERR,
            ExecuteError::TimerFd(_) => VIRTIO_BLK_S_IOERR,
            ExecuteError::WriteIo { .. } => VIRTIO_BLK_S_IOERR,
            ExecuteError::ShortWrite { .. } => VIRTIO_BLK_S_IOERR,
            ExecuteError::DiscardWriteZeroes { .. } => VIRTIO_BLK_S_IOERR,
            ExecuteError::ReadOnly { .. } => VIRTIO_BLK_S_IOERR,
            ExecuteError::OutOfRange { .. } => VIRTIO_BLK_S_IOERR,
            ExecuteError::MissingStatus => VIRTIO_BLK_S_IOERR,
            ExecuteError::Unsupported(_) => VIRTIO_BLK_S_UNSUPP,
        }
    }
}

struct Worker<T: DiskFile> {
    queues: Vec<Queue>,
    mem: GuestMemory,
    disk_image: T,
    disk_size: Arc<Mutex<u64>>,
    read_only: bool,
    interrupt_status: Arc<AtomicUsize>,
    interrupt_evt: EventFd,
    interrupt_resample_evt: EventFd,
}

impl<T: DiskFile> Worker<T> {
    fn process_queue(
        &mut self,
        queue_index: usize,
        flush_timer: &mut TimerFd,
        flush_timer_armed: &mut bool,
    ) -> bool {
        let queue = &mut self.queues[queue_index];

        let disk_size = self.disk_size.lock();

        let mut needs_interrupt = false;
        while let Some(avail_desc) = queue.pop(&self.mem) {
            let desc_index = avail_desc.index;
            let mut status_writer = Writer::new(&self.mem, avail_desc.clone());

            let status = match Block::execute_request(
                avail_desc,
                self.read_only,
                &mut self.disk_image,
                *disk_size,
                flush_timer,
                flush_timer_armed,
                &self.mem,
            ) {
                Ok(()) => VIRTIO_BLK_S_OK,
                Err(e) => {
                    error!("failed executing disk request: {}", e);
                    e.status()
                }
            };

            let len = if let Ok(status_offset) = status_writer.seek(SeekFrom::End(-1)) {
                match status_writer.write_all(&[status]) {
                    Ok(_) => status_offset + 1,
                    Err(e) => {
                        error!("failed to write status: {}", e);
                        0
                    }
                }
            } else {
                error!("failed to seek to status location");
                0
            };

            queue.add_used(&self.mem, desc_index, len as u32);
            needs_interrupt = true;
        }

        needs_interrupt
    }

    fn resize(&mut self, new_size: u64) -> DiskControlResult {
        if self.read_only {
            error!("Attempted to resize read-only block device");
            return DiskControlResult::Err(SysError::new(libc::EROFS));
        }

        info!("Resizing block device to {} bytes", new_size);

        if let Err(e) = self.disk_image.set_len(new_size) {
            error!("Resizing disk failed! {}", e);
            return DiskControlResult::Err(SysError::new(libc::EIO));
        }

        if let Ok(new_disk_size) = self.disk_image.seek(SeekFrom::End(0)) {
            let mut disk_size = self.disk_size.lock();
            *disk_size = new_disk_size;
        }
        DiskControlResult::Ok
    }

    fn signal_used_queue(&self) {
        self.interrupt_status
            .fetch_or(INTERRUPT_STATUS_USED_RING as usize, Ordering::SeqCst);
        self.interrupt_evt.write(1).unwrap();
    }

    fn signal_config_changed(&self) {
        self.interrupt_status
            .fetch_or(INTERRUPT_STATUS_CONFIG_CHANGED as usize, Ordering::SeqCst);
        self.interrupt_evt.write(1).unwrap();
    }

    fn run(
        &mut self,
        queue_evt: EventFd,
        kill_evt: EventFd,
        control_socket: DiskControlResponseSocket,
    ) {
        #[derive(PollToken)]
        enum Token {
            FlushTimer,
            QueueAvailable,
            ControlRequest,
            InterruptResample,
            Kill,
        }

        let mut flush_timer = match TimerFd::new() {
            Ok(t) => t,
            Err(e) => {
                error!("Failed to create the flush timer: {}", e);
                return;
            }
        };
        let mut flush_timer_armed = false;

        let poll_ctx: PollContext<Token> = match PollContext::build_with(&[
            (&flush_timer, Token::FlushTimer),
            (&queue_evt, Token::QueueAvailable),
            (&control_socket, Token::ControlRequest),
            (&self.interrupt_resample_evt, Token::InterruptResample),
            (&kill_evt, Token::Kill),
        ]) {
            Ok(pc) => pc,
            Err(e) => {
                error!("failed creating PollContext: {}", e);
                return;
            }
        };

        'poll: loop {
            let events = match poll_ctx.wait() {
                Ok(v) => v,
                Err(e) => {
                    error!("failed polling for events: {}", e);
                    break;
                }
            };

            let mut needs_interrupt = false;
            let mut needs_config_interrupt = false;
            for event in events.iter_readable() {
                match event.token() {
                    Token::FlushTimer => {
                        if let Err(e) = self.disk_image.fsync() {
                            error!("Failed to flush the disk: {}", e);
                            break 'poll;
                        }
                        if let Err(e) = flush_timer.wait() {
                            error!("Failed to clear flush timer: {}", e);
                            break 'poll;
                        }
                    }
                    Token::QueueAvailable => {
                        if let Err(e) = queue_evt.read() {
                            error!("failed reading queue EventFd: {}", e);
                            break 'poll;
                        }
                        needs_interrupt |=
                            self.process_queue(0, &mut flush_timer, &mut flush_timer_armed);
                    }
                    Token::ControlRequest => {
                        let req = match control_socket.recv() {
                            Ok(req) => req,
                            Err(e) => {
                                error!("control socket failed recv: {}", e);
                                break 'poll;
                            }
                        };

                        let resp = match req {
                            DiskControlCommand::Resize { new_size } => {
                                needs_config_interrupt = true;
                                self.resize(new_size)
                            }
                        };

                        if let Err(e) = control_socket.send(&resp) {
                            error!("control socket failed send: {}", e);
                            break 'poll;
                        }
                    }
                    Token::InterruptResample => {
                        let _ = self.interrupt_resample_evt.read();
                        if self.interrupt_status.load(Ordering::SeqCst) != 0 {
                            self.interrupt_evt.write(1).unwrap();
                        }
                    }
                    Token::Kill => break 'poll,
                }
            }
            if needs_interrupt {
                self.signal_used_queue();
            }
            if needs_config_interrupt {
                self.signal_config_changed();
            }
        }
    }
}

/// Virtio device for exposing block level read/write operations on a host file.
pub struct Block<T: DiskFile> {
    kill_evt: Option<EventFd>,
    disk_image: Option<T>,
    disk_size: Arc<Mutex<u64>>,
    avail_features: u64,
    read_only: bool,
    control_socket: Option<DiskControlResponseSocket>,
}

fn build_config_space(disk_size: u64) -> virtio_blk_config {
    virtio_blk_config {
        // If the image is not a multiple of the sector size, the tail bits are not exposed.
        capacity: Le64::from(disk_size >> SECTOR_SHIFT),
        blk_size: Le32::from(SECTOR_SIZE as u32),
        max_discard_sectors: Le32::from(MAX_DISCARD_SECTORS),
        discard_sector_alignment: Le32::from(DISCARD_SECTOR_ALIGNMENT),
        max_write_zeroes_sectors: Le32::from(MAX_WRITE_ZEROES_SECTORS),
        write_zeroes_may_unmap: 1,
        max_discard_seg: Le32::from(MAX_DISCARD_SEG),
        max_write_zeroes_seg: Le32::from(MAX_WRITE_ZEROES_SEG),
        ..Default::default()
    }
}

impl<T: DiskFile> Block<T> {
    /// Create a new virtio block device that operates on the given file.
    ///
    /// The given file must be seekable and sizable.
    pub fn new(
        mut disk_image: T,
        read_only: bool,
        control_socket: Option<DiskControlResponseSocket>,
    ) -> SysResult<Block<T>> {
        let disk_size = disk_image.seek(SeekFrom::End(0))? as u64;
        if disk_size % SECTOR_SIZE != 0 {
            warn!(
                "Disk size {} is not a multiple of sector size {}; \
                 the remainder will not be visible to the guest.",
                disk_size, SECTOR_SIZE
            );
        }

        let mut avail_features: u64 = 1 << VIRTIO_BLK_F_FLUSH;
        if read_only {
            avail_features |= 1 << VIRTIO_BLK_F_RO;
        } else {
            avail_features |= 1 << VIRTIO_BLK_F_DISCARD;
            avail_features |= 1 << VIRTIO_BLK_F_WRITE_ZEROES;
        }
        avail_features |= 1 << VIRTIO_F_VERSION_1;
        avail_features |= 1 << VIRTIO_BLK_F_BLK_SIZE;

        Ok(Block {
            kill_evt: None,
            disk_image: Some(disk_image),
            disk_size: Arc::new(Mutex::new(disk_size)),
            avail_features,
            read_only,
            control_socket,
        })
    }

    fn execute_request(
        avail_desc: DescriptorChain,
        read_only: bool,
        disk: &mut T,
        disk_size: u64,
        flush_timer: &mut TimerFd,
        flush_timer_armed: &mut bool,
        mem: &GuestMemory,
    ) -> result::Result<(), ExecuteError> {
        let mut reader = Reader::new(mem, avail_desc.clone());
        let mut writer = Writer::new(mem, avail_desc);

        let req_header: virtio_blk_req_header =
            reader.read_obj().map_err(ExecuteError::Descriptor)?;

        let req_type = req_header.req_type.to_native();
        let sector = req_header.sector.to_native();
        // Delay after a write when the file is auto-flushed.
        let flush_delay = Duration::from_secs(60);

        if read_only && req_type != VIRTIO_BLK_T_IN {
            return Err(ExecuteError::ReadOnly {
                request_type: req_type,
            });
        }

        /// Check that a request accesses only data within the disk's current size.
        /// All parameters are in units of bytes.
        fn check_range(
            io_start: u64,
            io_length: u64,
            disk_size: u64,
        ) -> result::Result<(), ExecuteError> {
            let io_end = io_start
                .checked_add(io_length)
                .ok_or(ExecuteError::OutOfRange)?;
            if io_end > disk_size {
                Err(ExecuteError::OutOfRange)
            } else {
                Ok(())
            }
        }

        match req_type {
            VIRTIO_BLK_T_IN => {
                // The last byte of writer is virtio_blk_req::status, so subtract it from data_len.
                let data_len = writer
                    .available_bytes()
                    .checked_sub(1)
                    .ok_or(ExecuteError::MissingStatus)?;
                let offset = sector
                    .checked_shl(u32::from(SECTOR_SHIFT))
                    .ok_or(ExecuteError::OutOfRange)?;
                check_range(offset, data_len as u64, disk_size)?;
                disk.seek(SeekFrom::Start(offset))
                    .map_err(|e| ExecuteError::Seek { ioerr: e, sector })?;
                let actual_length =
                    writer
                        .write_from_volatile(disk, data_len)
                        .map_err(|desc_error| ExecuteError::ReadIo {
                            length: data_len,
                            sector,
                            desc_error,
                        })?;
                if actual_length < data_len {
                    return Err(ExecuteError::ShortRead {
                        sector,
                        expected_length: data_len,
                        actual_length,
                    });
                }
            }
            VIRTIO_BLK_T_OUT => {
                let data_len = reader.available_bytes();
                let offset = sector
                    .checked_shl(u32::from(SECTOR_SHIFT))
                    .ok_or(ExecuteError::OutOfRange)?;
                check_range(offset, data_len as u64, disk_size)?;
                disk.seek(SeekFrom::Start(offset))
                    .map_err(|e| ExecuteError::Seek { ioerr: e, sector })?;
                let actual_length =
                    reader
                        .read_to_volatile(disk, data_len)
                        .map_err(|desc_error| ExecuteError::WriteIo {
                            length: data_len,
                            sector,
                            desc_error,
                        })?;
                if actual_length < data_len {
                    return Err(ExecuteError::ShortWrite {
                        sector,
                        expected_length: data_len,
                        actual_length,
                    });
                }
                if !*flush_timer_armed {
                    flush_timer
                        .reset(flush_delay, None)
                        .map_err(ExecuteError::TimerFd)?;
                    *flush_timer_armed = true;
                }
            }
            VIRTIO_BLK_T_DISCARD | VIRTIO_BLK_T_WRITE_ZEROES => {
                while reader.available_bytes() >= size_of::<virtio_blk_discard_write_zeroes>() {
                    let seg: virtio_blk_discard_write_zeroes =
                        reader.read_obj().map_err(ExecuteError::Descriptor)?;

                    let sector = seg.sector.to_native();
                    let num_sectors = seg.num_sectors.to_native();
                    let flags = seg.flags.to_native();

                    let valid_flags = if req_type == VIRTIO_BLK_T_WRITE_ZEROES {
                        VIRTIO_BLK_DISCARD_WRITE_ZEROES_FLAG_UNMAP
                    } else {
                        0
                    };

                    if (flags & !valid_flags) != 0 {
                        return Err(ExecuteError::DiscardWriteZeroes {
                            ioerr: None,
                            sector,
                            num_sectors,
                            flags,
                        });
                    }

                    let offset = sector
                        .checked_shl(u32::from(SECTOR_SHIFT))
                        .ok_or(ExecuteError::OutOfRange)?;
                    let length = u64::from(num_sectors)
                        .checked_shl(u32::from(SECTOR_SHIFT))
                        .ok_or(ExecuteError::OutOfRange)?;
                    check_range(offset, length, disk_size)?;

                    if req_type == VIRTIO_BLK_T_DISCARD {
                        // Since Discard is just a hint and some filesystems may not implement
                        // FALLOC_FL_PUNCH_HOLE, ignore punch_hole errors.
                        let _ = disk.punch_hole(offset, length);
                    } else {
                        disk.seek(SeekFrom::Start(offset))
                            .map_err(|e| ExecuteError::Seek { ioerr: e, sector })?;
                        disk.write_zeroes(length as usize).map_err(|e| {
                            ExecuteError::DiscardWriteZeroes {
                                ioerr: Some(e),
                                sector,
                                num_sectors,
                                flags,
                            }
                        })?;
                    }
                }
            }
            VIRTIO_BLK_T_FLUSH => {
                disk.fsync().map_err(ExecuteError::Flush)?;
                flush_timer.clear().map_err(ExecuteError::TimerFd)?;
                *flush_timer_armed = false;
            }
            t => return Err(ExecuteError::Unsupported(t)),
        };
        Ok(())
    }
}

impl<T: DiskFile> Drop for Block<T> {
    fn drop(&mut self) {
        if let Some(kill_evt) = self.kill_evt.take() {
            // Ignore the result because there is nothing we can do about it.
            let _ = kill_evt.write(1);
        }
    }
}

impl<T: 'static + AsRawFd + DiskFile + Send> VirtioDevice for Block<T> {
    fn keep_fds(&self) -> Vec<RawFd> {
        let mut keep_fds = Vec::new();

        if let Some(disk_image) = &self.disk_image {
            keep_fds.push(disk_image.as_raw_fd());
        }

        if let Some(control_socket) = &self.control_socket {
            keep_fds.push(control_socket.as_raw_fd());
        }

        keep_fds
    }

    fn features(&self) -> u64 {
        self.avail_features
    }

    fn device_type(&self) -> u32 {
        TYPE_BLOCK
    }

    fn queue_max_sizes(&self) -> &[u16] {
        QUEUE_SIZES
    }

    fn read_config(&self, offset: u64, data: &mut [u8]) {
        let config_space = {
            let disk_size = self.disk_size.lock();
            build_config_space(*disk_size)
        };
        copy_config(data, 0, config_space.as_slice(), offset);
    }

    fn activate(
        &mut self,
        mem: GuestMemory,
        interrupt_evt: EventFd,
        interrupt_resample_evt: EventFd,
        status: Arc<AtomicUsize>,
        queues: Vec<Queue>,
        mut queue_evts: Vec<EventFd>,
    ) {
        if queues.len() != 1 || queue_evts.len() != 1 {
            return;
        }

        let (self_kill_evt, kill_evt) = match EventFd::new().and_then(|e| Ok((e.try_clone()?, e))) {
            Ok(v) => v,
            Err(e) => {
                error!("failed creating kill EventFd pair: {}", e);
                return;
            }
        };
        self.kill_evt = Some(self_kill_evt);

        let read_only = self.read_only;
        let disk_size = self.disk_size.clone();
        if let Some(disk_image) = self.disk_image.take() {
            if let Some(control_socket) = self.control_socket.take() {
                let worker_result =
                    thread::Builder::new()
                        .name("virtio_blk".to_string())
                        .spawn(move || {
                            let mut worker = Worker {
                                queues,
                                mem,
                                disk_image,
                                disk_size,
                                read_only,
                                interrupt_status: status,
                                interrupt_evt,
                                interrupt_resample_evt,
                            };
                            worker.run(queue_evts.remove(0), kill_evt, control_socket);
                        });

                if let Err(e) = worker_result {
                    error!("failed to spawn virtio_blk worker: {}", e);
                    return;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::fs::{File, OpenOptions};
    use std::mem::size_of_val;
    use sys_util::GuestAddress;
    use tempfile::TempDir;

    use crate::virtio::descriptor_utils::{create_descriptor_chain, DescriptorType};

    use super::*;

    #[test]
    fn read_size() {
        let tempdir = TempDir::new().unwrap();
        let mut path = tempdir.path().to_owned();
        path.push("disk_image");
        let f = File::create(&path).unwrap();
        f.set_len(0x1000).unwrap();

        let b = Block::new(f, true, None).unwrap();
        let mut num_sectors = [0u8; 4];
        b.read_config(0, &mut num_sectors);
        // size is 0x1000, so num_sectors is 8 (4096/512).
        assert_eq!([0x08, 0x00, 0x00, 0x00], num_sectors);
        let mut msw_sectors = [0u8; 4];
        b.read_config(4, &mut msw_sectors);
        // size is 0x1000, so msw_sectors is 0.
        assert_eq!([0x00, 0x00, 0x00, 0x00], msw_sectors);
    }

    #[test]
    fn read_features() {
        let tempdir = TempDir::new().unwrap();
        let mut path = tempdir.path().to_owned();
        path.push("disk_image");

        // read-write block device
        {
            let f = File::create(&path).unwrap();
            let b = Block::new(f, false, None).unwrap();
            // writable device should set VIRTIO_BLK_F_FLUSH + VIRTIO_BLK_F_DISCARD
            // + VIRTIO_BLK_F_WRITE_ZEROES + VIRTIO_F_VERSION_1 + VIRTIO_BLK_F_BLK_SIZE
            assert_eq!(0x100006240, b.features());
        }

        // read-only block device
        {
            let f = File::create(&path).unwrap();
            let b = Block::new(f, true, None).unwrap();
            // read-only device should set VIRTIO_BLK_F_FLUSH and VIRTIO_BLK_F_RO
            // + VIRTIO_F_VERSION_1 + VIRTIO_BLK_F_BLK_SIZE
            assert_eq!(0x100000260, b.features());
        }
    }

    #[test]
    fn read_last_sector() {
        let tempdir = TempDir::new().unwrap();
        let mut path = tempdir.path().to_owned();
        path.push("disk_image");
        let mut f = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(&path)
            .unwrap();
        let disk_size = 0x1000;
        f.set_len(disk_size).unwrap();

        let mem = GuestMemory::new(&[(GuestAddress(0u64), 4 * 1024 * 1024)])
            .expect("Creating guest memory failed.");

        let req_hdr = virtio_blk_req_header {
            req_type: Le32::from(VIRTIO_BLK_T_IN),
            reserved: Le32::from(0),
            sector: Le64::from(7), // Disk is 8 sectors long, so this is the last valid sector.
        };
        mem.write_obj_at_addr(req_hdr, GuestAddress(0x1000))
            .expect("writing req failed");

        let avail_desc = create_descriptor_chain(
            &mem,
            GuestAddress(0x100),  // Place descriptor chain at 0x100.
            GuestAddress(0x1000), // Describe buffer at 0x1000.
            vec![
                // Request header
                (DescriptorType::Readable, size_of_val(&req_hdr) as u32),
                // I/O buffer (1 sector of data)
                (DescriptorType::Writable, 512),
                // Request status
                (DescriptorType::Writable, 1),
            ],
            0,
        )
        .expect("create_descriptor_chain failed");

        let mut flush_timer = TimerFd::new().expect("failed to create flush_timer");
        let mut flush_timer_armed = false;

        Block::execute_request(
            avail_desc,
            false,
            &mut f,
            disk_size,
            &mut flush_timer,
            &mut flush_timer_armed,
            &mem,
        )
        .expect("execute failed");
    }

    #[test]
    fn read_beyond_last_sector() {
        let tempdir = TempDir::new().unwrap();
        let mut path = tempdir.path().to_owned();
        path.push("disk_image");
        let mut f = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(&path)
            .unwrap();
        let disk_size = 0x1000;
        f.set_len(disk_size).unwrap();

        let mem = GuestMemory::new(&[(GuestAddress(0u64), 4 * 1024 * 1024)])
            .expect("Creating guest memory failed.");

        let req_hdr = virtio_blk_req_header {
            req_type: Le32::from(VIRTIO_BLK_T_IN),
            reserved: Le32::from(0),
            sector: Le64::from(7), // Disk is 8 sectors long, so this is the last valid sector.
        };
        mem.write_obj_at_addr(req_hdr, GuestAddress(0x1000))
            .expect("writing req failed");

        let avail_desc = create_descriptor_chain(
            &mem,
            GuestAddress(0x100),  // Place descriptor chain at 0x100.
            GuestAddress(0x1000), // Describe buffer at 0x1000.
            vec![
                // Request header
                (DescriptorType::Readable, size_of_val(&req_hdr) as u32),
                // I/O buffer (2 sectors of data - overlap the end of the disk).
                (DescriptorType::Writable, 512 * 2),
                // Request status
                (DescriptorType::Writable, 1),
            ],
            0,
        )
        .expect("create_descriptor_chain failed");

        let mut flush_timer = TimerFd::new().expect("failed to create flush_timer");
        let mut flush_timer_armed = false;

        Block::execute_request(
            avail_desc,
            false,
            &mut f,
            disk_size,
            &mut flush_timer,
            &mut flush_timer_armed,
            &mem,
        )
        .expect_err("execute was supposed to fail");
    }
}
