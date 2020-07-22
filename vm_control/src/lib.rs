// Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

//! Handles IPC for controlling the main VM process.
//!
//! The VM Control IPC protocol is synchronous, meaning that each `VmRequest` sent over a connection
//! will receive a `VmResponse` for that request next time data is received over that connection.
//!
//! The wire message format is a little-endian C-struct of fixed size, along with a file descriptor
//! if the request type expects one.

use std::fmt::{self, Display};
use std::fs::File;
use std::io::{Seek, SeekFrom};
use std::mem::ManuallyDrop;
use std::os::unix::io::{AsRawFd, FromRawFd, RawFd};
use std::sync::Arc;

use libc::{EINVAL, EIO, ENODEV};

use kvm::{IrqRoute, IrqSource, Vm};
use msg_socket::{MsgError, MsgOnSocket, MsgReceiver, MsgResult, MsgSender, MsgSocket};
use resources::{Alloc, GpuMemoryDesc, MmioType, SystemAllocator};
use sync::Mutex;
use sys_util::{
    error, Error as SysError, EventFd, ExternalMapping, GuestAddress, MappedRegion, MemoryMapping,
    MmapError, Result,
};

/// A file descriptor either borrowed or owned by this.
#[derive(Debug)]
pub enum MaybeOwnedFd {
    /// Owned by this enum variant, and will be destructed automatically if not moved out.
    Owned(File),
    /// A file descriptor borrwed by this enum.
    Borrowed(RawFd),
}

impl AsRawFd for MaybeOwnedFd {
    fn as_raw_fd(&self) -> RawFd {
        match self {
            MaybeOwnedFd::Owned(f) => f.as_raw_fd(),
            MaybeOwnedFd::Borrowed(fd) => *fd,
        }
    }
}

// When sent, it could be owned or borrowed. On the receiver end, it always owned.
impl MsgOnSocket for MaybeOwnedFd {
    fn uses_fd() -> bool {
        true
    }
    fn fixed_size() -> Option<usize> {
        Some(0)
    }
    fn fd_count(&self) -> usize {
        1usize
    }
    unsafe fn read_from_buffer(buffer: &[u8], fds: &[RawFd]) -> MsgResult<(Self, usize)> {
        let (file, size) = File::read_from_buffer(buffer, fds)?;
        Ok((MaybeOwnedFd::Owned(file), size))
    }
    fn write_to_buffer(&self, _buffer: &mut [u8], fds: &mut [RawFd]) -> MsgResult<usize> {
        if fds.is_empty() {
            return Err(MsgError::WrongFdBufferSize);
        }

        fds[0] = self.as_raw_fd();
        Ok(1)
    }
}

/// Mode of execution for the VM.
#[derive(Debug)]
pub enum VmRunMode {
    /// The default run mode indicating the VCPUs are running.
    Running,
    /// Indicates that the VCPUs are suspending execution until the `Running` mode is set.
    Suspending,
    /// Indicates that the VM is exiting all processes.
    Exiting,
}

impl Display for VmRunMode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::VmRunMode::*;

        match self {
            Running => write!(f, "running"),
            Suspending => write!(f, "suspending"),
            Exiting => write!(f, "exiting"),
        }
    }
}

impl Default for VmRunMode {
    fn default() -> Self {
        VmRunMode::Running
    }
}

/// The maximum number of devices that can be listed in one `UsbControlCommand`.
///
/// This value was set to be equal to `xhci_regs::MAX_PORTS` for convenience, but it is not
/// necessary for correctness. Importing that value directly would be overkill because it would
/// require adding a big dependency for a single const.
pub const USB_CONTROL_MAX_PORTS: usize = 16;

#[derive(MsgOnSocket, Debug)]
pub enum BalloonControlCommand {
    /// Set the size of the VM's balloon.
    Adjust {
        num_bytes: u64,
    },
    Stats,
}

// BalloonStats holds stats returned from the stats_queue.
#[derive(Default, MsgOnSocket, Debug)]
pub struct BalloonStats {
    pub swap_in: Option<u64>,
    pub swap_out: Option<u64>,
    pub major_faults: Option<u64>,
    pub minor_faults: Option<u64>,
    pub free_memory: Option<u64>,
    pub total_memory: Option<u64>,
    pub available_memory: Option<u64>,
    pub disk_caches: Option<u64>,
    pub hugetlb_allocations: Option<u64>,
    pub hugetlb_failures: Option<u64>,
}

impl Display for BalloonStats {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{")?;
        if let Some(swap_in) = self.swap_in {
            write!(f, "\n    swap_in: {}", swap_in)?;
        }
        if let Some(swap_out) = self.swap_out {
            write!(f, "\n    swap_out: {}", swap_out)?;
        }
        if let Some(major_faults) = self.major_faults {
            write!(f, "\n    major_faults: {}", major_faults)?;
        }
        if let Some(minor_faults) = self.minor_faults {
            write!(f, "\n    minor_faults: {}", minor_faults)?;
        }
        if let Some(free_memory) = self.free_memory {
            write!(f, "\n    free_memory: {}", free_memory)?;
        }
        if let Some(total_memory) = self.total_memory {
            write!(f, "\n    total_memory: {}", total_memory)?;
        }
        if let Some(available_memory) = self.available_memory {
            write!(f, "\n    available_memory: {}", available_memory)?;
        }
        if let Some(disk_caches) = self.disk_caches {
            write!(f, "\n    disk_caches: {}", disk_caches)?;
        }
        if let Some(hugetlb_allocations) = self.hugetlb_allocations {
            write!(f, "\n    hugetlb_allocations: {}", hugetlb_allocations)?;
        }
        if let Some(hugetlb_failures) = self.hugetlb_failures {
            write!(f, "\n    hugetlb_failures: {}", hugetlb_failures)?;
        }
        write!(f, "\n}}")
    }
}

#[derive(MsgOnSocket, Debug)]
pub enum BalloonControlResult {
    Stats {
        stats: BalloonStats,
        balloon_actual: u64,
    },
}

#[derive(MsgOnSocket, Debug)]
pub enum DiskControlCommand {
    /// Resize a disk to `new_size` in bytes.
    Resize { new_size: u64 },
}

impl Display for DiskControlCommand {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::DiskControlCommand::*;

        match self {
            Resize { new_size } => write!(f, "disk_resize {}", new_size),
        }
    }
}

#[derive(MsgOnSocket, Debug)]
pub enum DiskControlResult {
    Ok,
    Err(SysError),
}

#[derive(MsgOnSocket, Debug)]
pub enum UsbControlCommand {
    AttachDevice {
        bus: u8,
        addr: u8,
        vid: u16,
        pid: u16,
        fd: Option<MaybeOwnedFd>,
    },
    DetachDevice {
        port: u8,
    },
    ListDevice {
        ports: [u8; USB_CONTROL_MAX_PORTS],
    },
}

#[derive(MsgOnSocket, Copy, Clone, Debug, Default)]
pub struct UsbControlAttachedDevice {
    pub port: u8,
    pub vendor_id: u16,
    pub product_id: u16,
}

impl UsbControlAttachedDevice {
    fn valid(self) -> bool {
        self.port != 0
    }
}

#[derive(MsgOnSocket, Debug)]
pub enum UsbControlResult {
    Ok { port: u8 },
    NoAvailablePort,
    NoSuchDevice,
    NoSuchPort,
    FailedToOpenDevice,
    Devices([UsbControlAttachedDevice; USB_CONTROL_MAX_PORTS]),
}

impl Display for UsbControlResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::UsbControlResult::*;

        match self {
            Ok { port } => write!(f, "ok {}", port),
            NoAvailablePort => write!(f, "no_available_port"),
            NoSuchDevice => write!(f, "no_such_device"),
            NoSuchPort => write!(f, "no_such_port"),
            FailedToOpenDevice => write!(f, "failed_to_open_device"),
            Devices(devices) => {
                write!(f, "devices")?;
                for d in devices.iter().filter(|d| d.valid()) {
                    write!(f, " {} {:04x} {:04x}", d.port, d.vendor_id, d.product_id)?;
                }
                std::result::Result::Ok(())
            }
        }
    }
}

#[derive(MsgOnSocket, Debug)]
pub enum VmMemoryRequest {
    /// Register shared memory represented by the given fd into guest address space. The response
    /// variant is `VmResponse::RegisterMemory`.
    RegisterMemory(MaybeOwnedFd, usize),
    /// Similiar to `VmMemoryRequest::RegisterMemory`, but doesn't allocate new address space.
    /// Useful for cases where the address space is already allocated (PCI regions).
    RegisterFdAtPciBarOffset(Alloc, MaybeOwnedFd, usize, u64),
    /// Similar to RegisterFdAtPciBarOffset, but is for buffers in the current address space.
    RegisterHostPointerAtPciBarOffset(Alloc, u64),
    /// Unregister the given memory slot that was previously registered with `RegisterMemory*`.
    UnregisterMemory(u32),
    /// Allocate GPU buffer of a given size/format and register the memory into guest address space.
    /// The response variant is `VmResponse::AllocateAndRegisterGpuMemory`
    AllocateAndRegisterGpuMemory {
        width: u32,
        height: u32,
        format: u32,
    },
    /// Register mmaped memory into kvm's EPT.
    RegisterMmapMemory {
        fd: MaybeOwnedFd,
        size: usize,
        offset: u64,
        gpa: u64,
    },
}

impl VmMemoryRequest {
    /// Executes this request on the given Vm.
    ///
    /// # Arguments
    /// * `vm` - The `Vm` to perform the request on.
    /// * `allocator` - Used to allocate addresses.
    ///
    /// This does not return a result, instead encapsulating the success or failure in a
    /// `VmMemoryResponse` with the intended purpose of sending the response back over the socket
    /// that received this `VmMemoryResponse`.
    pub fn execute(
        &self,
        vm: &mut Vm,
        sys_allocator: &mut SystemAllocator,
        map_request: Arc<Mutex<Option<ExternalMapping>>>,
    ) -> VmMemoryResponse {
        use self::VmMemoryRequest::*;
        match *self {
            RegisterMemory(ref fd, size) => {
                match register_memory(vm, sys_allocator, fd, size, None) {
                    Ok((pfn, slot)) => VmMemoryResponse::RegisterMemory { pfn, slot },
                    Err(e) => VmMemoryResponse::Err(e),
                }
            }
            RegisterFdAtPciBarOffset(alloc, ref fd, size, offset) => {
                match register_memory(vm, sys_allocator, fd, size, Some((alloc, offset))) {
                    Ok((pfn, slot)) => VmMemoryResponse::RegisterMemory { pfn, slot },
                    Err(e) => VmMemoryResponse::Err(e),
                }
            }
            UnregisterMemory(slot) => match vm.remove_memory_region(slot) {
                Ok(_) => VmMemoryResponse::Ok,
                Err(e) => VmMemoryResponse::Err(e),
            },
            RegisterHostPointerAtPciBarOffset(alloc, offset) => {
                let mem = map_request
                    .lock()
                    .take()
                    .ok_or(VmMemoryResponse::Err(SysError::new(EINVAL)))
                    .unwrap();

                match register_memory_hva(vm, sys_allocator, Box::new(mem), (alloc, offset)) {
                    Ok((pfn, slot)) => VmMemoryResponse::RegisterMemory { pfn, slot },
                    Err(e) => VmMemoryResponse::Err(e),
                }
            }
            AllocateAndRegisterGpuMemory {
                width,
                height,
                format,
            } => {
                let (mut fd, desc) = match sys_allocator.gpu_memory_allocator() {
                    Some(gpu_allocator) => match gpu_allocator.allocate(width, height, format) {
                        Ok(v) => v,
                        Err(e) => return VmMemoryResponse::Err(e),
                    },
                    None => return VmMemoryResponse::Err(SysError::new(ENODEV)),
                };
                // Determine size of buffer using 0 byte seek from end. This is preferred over
                // `stride * height` as it's not limited to packed pixel formats.
                let size = match fd.seek(SeekFrom::End(0)) {
                    Ok(v) => v,
                    Err(e) => return VmMemoryResponse::Err(SysError::from(e)),
                };
                match register_memory(vm, sys_allocator, &fd, size as usize, None) {
                    Ok((pfn, slot)) => VmMemoryResponse::AllocateAndRegisterGpuMemory {
                        fd: MaybeOwnedFd::Owned(fd),
                        pfn,
                        slot,
                        desc,
                    },
                    Err(e) => VmMemoryResponse::Err(e),
                }
            }
            RegisterMmapMemory {
                ref fd,
                size,
                offset,
                gpa,
            } => {
                let mmap = match MemoryMapping::from_fd_offset(fd, size, offset as u64) {
                    Ok(v) => v,
                    Err(_e) => return VmMemoryResponse::Err(SysError::new(EINVAL)),
                };
                match vm.add_memory_region(GuestAddress(gpa), Box::new(mmap), false, false) {
                    Ok(_) => VmMemoryResponse::Ok,
                    Err(e) => VmMemoryResponse::Err(e),
                }
            }
        }
    }
}

#[derive(MsgOnSocket, Debug)]
pub enum VmMemoryResponse {
    /// The request to register memory into guest address space was successfully done at page frame
    /// number `pfn` and memory slot number `slot`.
    RegisterMemory {
        pfn: u64,
        slot: u32,
    },
    /// The request to allocate and register GPU memory into guest address space was successfully
    /// done at page frame number `pfn` and memory slot number `slot` for buffer with `desc`.
    AllocateAndRegisterGpuMemory {
        fd: MaybeOwnedFd,
        pfn: u64,
        slot: u32,
        desc: GpuMemoryDesc,
    },
    Ok,
    Err(SysError),
}

#[derive(MsgOnSocket, Debug)]
pub enum VmIrqRequest {
    /// Allocate one gsi, and associate gsi to irqfd with register_irqfd()
    AllocateOneMsi { irqfd: MaybeOwnedFd },
    /// Add one msi route entry into kvm
    AddMsiRoute {
        gsi: u32,
        msi_address: u64,
        msi_data: u32,
    },
}

impl VmIrqRequest {
    /// Executes this request on the given Vm.
    ///
    /// # Arguments
    /// * `vm` - The `Vm` to perform the request on.
    ///
    /// This does not return a result, instead encapsulating the success or failure in a
    /// `VmIrqResponse` with the intended purpose of sending the response back over the socket
    /// that received this `VmIrqResponse`.
    pub fn execute(&self, vm: &mut Vm, sys_allocator: &mut SystemAllocator) -> VmIrqResponse {
        use self::VmIrqRequest::*;
        match *self {
            AllocateOneMsi { ref irqfd } => {
                if let Some(irq_num) = sys_allocator.allocate_irq() {
                    // Beacuse of the limitation of `MaybeOwnedFd` not fitting into `register_irqfd`
                    // which expects an `&EventFd`, we use the unsafe `from_raw_fd` to assume that
                    // the fd given is an `EventFd`, and we ignore the ownership question using
                    // `ManuallyDrop`. This is safe because `ManuallyDrop` prevents any Drop
                    // implementation from triggering on `irqfd` which already has an owner, and the
                    // `EventFd` methods are never called. The underlying fd is merely passed to the
                    // kernel which doesn't care about ownership and deals with incorrect FDs, in
                    // the case of bugs on our part.
                    let evt = unsafe { ManuallyDrop::new(EventFd::from_raw_fd(irqfd.as_raw_fd())) };
                    match vm.register_irqfd(&evt, irq_num) {
                        Ok(_) => VmIrqResponse::AllocateOneMsi { gsi: irq_num },
                        Err(e) => VmIrqResponse::Err(e),
                    }
                } else {
                    VmIrqResponse::Err(SysError::new(EINVAL))
                }
            }
            AddMsiRoute {
                gsi,
                msi_address,
                msi_data,
            } => {
                let route = IrqRoute {
                    gsi,
                    source: IrqSource::Msi {
                        address: msi_address,
                        data: msi_data,
                    },
                };

                match vm.add_irq_route_entry(route) {
                    Ok(_) => VmIrqResponse::Ok,
                    Err(e) => VmIrqResponse::Err(e),
                }
            }
        }
    }
}

#[derive(MsgOnSocket, Debug)]
pub enum VmIrqResponse {
    AllocateOneMsi { gsi: u32 },
    Ok,
    Err(SysError),
}

#[derive(MsgOnSocket, Debug)]
pub enum VmMsyncRequest {
    /// Flush the content of a memory mapping to its backing file.
    /// `slot` selects the arena (as returned by `Vm::add_mmap_arena`).
    /// `offset` is the offset of the mapping to sync within the arena.
    /// `size` is the size of the mapping to sync within the arena.
    MsyncArena {
        slot: u32,
        offset: usize,
        size: usize,
    },
}

#[derive(MsgOnSocket, Debug)]
pub enum VmMsyncResponse {
    Ok,
    Err(SysError),
}

impl VmMsyncRequest {
    /// Executes this request on the given Vm.
    ///
    /// # Arguments
    /// * `vm` - The `Vm` to perform the request on.
    ///
    /// This does not return a result, instead encapsulating the success or failure in a
    /// `VmMsyncResponse` with the intended purpose of sending the response back over the socket
    /// that received this `VmMsyncResponse`.
    pub fn execute(&self, vm: &mut Vm) -> VmMsyncResponse {
        use self::VmMsyncRequest::*;
        match *self {
            MsyncArena { slot, offset, size } => match vm.mysnc_memory_region(slot, offset, size) {
                Ok(()) => VmMsyncResponse::Ok,
                Err(e) => VmMsyncResponse::Err(e),
            },
        }
    }
}

pub type BalloonControlRequestSocket = MsgSocket<BalloonControlCommand, BalloonControlResult>;
pub type BalloonControlResponseSocket = MsgSocket<BalloonControlResult, BalloonControlCommand>;

pub type DiskControlRequestSocket = MsgSocket<DiskControlCommand, DiskControlResult>;
pub type DiskControlResponseSocket = MsgSocket<DiskControlResult, DiskControlCommand>;

pub type UsbControlSocket = MsgSocket<UsbControlCommand, UsbControlResult>;

pub type VmMemoryControlRequestSocket = MsgSocket<VmMemoryRequest, VmMemoryResponse>;
pub type VmMemoryControlResponseSocket = MsgSocket<VmMemoryResponse, VmMemoryRequest>;

pub type VmIrqRequestSocket = MsgSocket<VmIrqRequest, VmIrqResponse>;
pub type VmIrqResponseSocket = MsgSocket<VmIrqResponse, VmIrqRequest>;

pub type VmMsyncRequestSocket = MsgSocket<VmMsyncRequest, VmMsyncResponse>;
pub type VmMsyncResponseSocket = MsgSocket<VmMsyncResponse, VmMsyncRequest>;

pub type VmControlRequestSocket = MsgSocket<VmRequest, VmResponse>;
pub type VmControlResponseSocket = MsgSocket<VmResponse, VmRequest>;

/// A request to the main process to perform some operation on the VM.
///
/// Unless otherwise noted, each request should expect a `VmResponse::Ok` to be received on success.
#[derive(MsgOnSocket, Debug)]
pub enum VmRequest {
    /// Break the VM's run loop and exit.
    Exit,
    /// Suspend the VM's VCPUs until resume.
    Suspend,
    /// Resume the VM's VCPUs that were previously suspended.
    Resume,
    /// Command for balloon driver.
    BalloonCommand(BalloonControlCommand),
    /// Send a command to a disk chosen by `disk_index`.
    /// `disk_index` is a 0-based count of `--disk`, `--rwdisk`, and `-r` command-line options.
    DiskCommand {
        disk_index: usize,
        command: DiskControlCommand,
    },
    /// Command to use controller.
    UsbCommand(UsbControlCommand),
}

fn register_memory(
    vm: &mut Vm,
    allocator: &mut SystemAllocator,
    fd: &dyn AsRawFd,
    size: usize,
    pci_allocation: Option<(Alloc, u64)>,
) -> Result<(u64, u32)> {
    let mmap = match MemoryMapping::from_fd(fd, size) {
        Ok(v) => v,
        Err(MmapError::SystemCallFailed(e)) => return Err(e),
        _ => return Err(SysError::new(EINVAL)),
    };

    let addr = match pci_allocation {
        Some(pci_allocation) => allocator
            .mmio_allocator(MmioType::High)
            .address_from_pci_offset(pci_allocation.0, pci_allocation.1, size as u64)
            .map_err(|_e| SysError::new(EINVAL))?,
        None => {
            let alloc = allocator.get_anon_alloc();
            allocator
                .mmio_allocator(MmioType::High)
                .allocate(size as u64, alloc, "vmcontrol_register_memory".to_string())
                .map_err(|_e| SysError::new(EINVAL))?
        }
    };

    let slot = vm.add_memory_region(GuestAddress(addr), Box::new(mmap), false, false)?;

    Ok((addr >> 12, slot))
}

fn register_memory_hva(
    vm: &mut Vm,
    allocator: &mut SystemAllocator,
    mem: Box<dyn MappedRegion>,
    pci_allocation: (Alloc, u64),
) -> Result<(u64, u32)> {
    let addr = allocator
        .mmio_allocator(MmioType::High)
        .address_from_pci_offset(pci_allocation.0, pci_allocation.1, mem.size() as u64)
        .map_err(|_e| SysError::new(EINVAL))?;

    let slot = vm.add_memory_region(GuestAddress(addr), mem, false, false)?;
    Ok((addr >> 12, slot))
}

impl VmRequest {
    /// Executes this request on the given Vm and other mutable state.
    ///
    /// This does not return a result, instead encapsulating the success or failure in a
    /// `VmResponse` with the intended purpose of sending the response back over the  socket that
    /// received this `VmRequest`.
    pub fn execute(
        &self,
        run_mode: &mut Option<VmRunMode>,
        balloon_host_socket: &BalloonControlRequestSocket,
        disk_host_sockets: &[DiskControlRequestSocket],
        usb_control_socket: &UsbControlSocket,
    ) -> VmResponse {
        match *self {
            VmRequest::Exit => {
                *run_mode = Some(VmRunMode::Exiting);
                VmResponse::Ok
            }
            VmRequest::Suspend => {
                *run_mode = Some(VmRunMode::Suspending);
                VmResponse::Ok
            }
            VmRequest::Resume => {
                *run_mode = Some(VmRunMode::Running);
                VmResponse::Ok
            }
            VmRequest::BalloonCommand(BalloonControlCommand::Adjust { num_bytes }) => {
                match balloon_host_socket.send(&BalloonControlCommand::Adjust { num_bytes }) {
                    Ok(_) => VmResponse::Ok,
                    Err(_) => VmResponse::Err(SysError::last()),
                }
            }
            VmRequest::BalloonCommand(BalloonControlCommand::Stats) => {
                match balloon_host_socket.send(&BalloonControlCommand::Stats {}) {
                    Ok(_) => match balloon_host_socket.recv() {
                        Ok(BalloonControlResult::Stats {
                            stats,
                            balloon_actual,
                        }) => VmResponse::BalloonStats {
                            stats,
                            balloon_actual,
                        },
                        Err(e) => {
                            error!("balloon socket recv failed: {}", e);
                            VmResponse::Err(SysError::last())
                        }
                    },
                    Err(_) => VmResponse::Err(SysError::last()),
                }
            }
            VmRequest::DiskCommand {
                disk_index,
                ref command,
            } => {
                // Forward the request to the block device process via its control socket.
                if let Some(sock) = disk_host_sockets.get(disk_index) {
                    if let Err(e) = sock.send(command) {
                        error!("disk socket send failed: {}", e);
                        VmResponse::Err(SysError::new(EINVAL))
                    } else {
                        match sock.recv() {
                            Ok(DiskControlResult::Ok) => VmResponse::Ok,
                            Ok(DiskControlResult::Err(e)) => VmResponse::Err(e),
                            Err(e) => {
                                error!("disk socket recv failed: {}", e);
                                VmResponse::Err(SysError::new(EINVAL))
                            }
                        }
                    }
                } else {
                    VmResponse::Err(SysError::new(ENODEV))
                }
            }
            VmRequest::UsbCommand(ref cmd) => {
                let res = usb_control_socket.send(cmd);
                if let Err(e) = res {
                    error!("fail to send command to usb control socket: {}", e);
                    return VmResponse::Err(SysError::new(EIO));
                }
                match usb_control_socket.recv() {
                    Ok(response) => VmResponse::UsbResponse(response),
                    Err(e) => {
                        error!("fail to recv command from usb control socket: {}", e);
                        VmResponse::Err(SysError::new(EIO))
                    }
                }
            }
        }
    }
}

/// Indication of success or failure of a `VmRequest`.
///
/// Success is usually indicated `VmResponse::Ok` unless there is data associated with the response.
#[derive(MsgOnSocket, Debug)]
pub enum VmResponse {
    /// Indicates the request was executed successfully.
    Ok,
    /// Indicates the request encountered some error during execution.
    Err(SysError),
    /// The request to register memory into guest address space was successfully done at page frame
    /// number `pfn` and memory slot number `slot`.
    RegisterMemory { pfn: u64, slot: u32 },
    /// The request to allocate and register GPU memory into guest address space was successfully
    /// done at page frame number `pfn` and memory slot number `slot` for buffer with `desc`.
    AllocateAndRegisterGpuMemory {
        fd: MaybeOwnedFd,
        pfn: u64,
        slot: u32,
        desc: GpuMemoryDesc,
    },
    /// Results of balloon control commands.
    BalloonStats {
        stats: BalloonStats,
        balloon_actual: u64,
    },
    /// Results of usb control commands.
    UsbResponse(UsbControlResult),
}

impl Display for VmResponse {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::VmResponse::*;

        match self {
            Ok => write!(f, "ok"),
            Err(e) => write!(f, "error: {}", e),
            RegisterMemory { pfn, slot } => write!(
                f,
                "memory registered to page frame number {:#x} and memory slot {}",
                pfn, slot
            ),
            AllocateAndRegisterGpuMemory { pfn, slot, .. } => write!(
                f,
                "gpu memory allocated and registered to page frame number {:#x} and memory slot {}",
                pfn, slot
            ),
            BalloonStats {
                stats,
                balloon_actual,
            } => write!(
                f,
                "balloon size: {}\nballoon stats: {}",
                balloon_actual, stats
            ),
            UsbResponse(result) => write!(f, "usb control request get result {:?}", result),
        }
    }
}
