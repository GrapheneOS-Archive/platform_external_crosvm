// Copyright 2018 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

pub mod android;
pub mod fdt;
pub mod pstore;
pub mod serial;

use std::collections::BTreeMap;
use std::error::Error as StdError;
use std::fmt::{self, Display};
use std::fs::File;
use std::io::{self, Read, Seek, SeekFrom};
use std::os::unix::io::AsRawFd;
use std::path::PathBuf;
use std::sync::Arc;

use acpi_tables::sdt::SDT;
use base::{syslog, AsRawDescriptor, Event};
use devices::virtio::VirtioDevice;
use devices::{
    Bus, BusDevice, BusError, IrqChip, PciAddress, PciDevice, PciDeviceError, PciInterruptPin,
    PciRoot, ProxyDevice,
};
use hypervisor::{IoEventAddress, Vcpu, Vm};
use minijail::Minijail;
use resources::SystemAllocator;
use sync::Mutex;
use vm_memory::{GuestAddress, GuestMemory, GuestMemoryError};

#[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
use {
    devices::IrqChipAArch64 as IrqChipArch,
    hypervisor::{Hypervisor as HypervisorArch, VcpuAArch64 as VcpuArch, VmAArch64 as VmArch},
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use {
    devices::IrqChipX86_64 as IrqChipArch,
    hypervisor::{HypervisorX86_64 as HypervisorArch, VcpuX86_64 as VcpuArch, VmX86_64 as VmArch},
};

pub use serial::{
    add_serial_devices, get_serial_cmdline, set_default_serial_parameters, GetSerialCmdlineError,
    SerialHardware, SerialParameters, SerialType, SERIAL_ADDR,
};

pub enum VmImage {
    Kernel(File),
    Bios(File),
}

#[derive(Clone)]
pub struct Pstore {
    pub path: PathBuf,
    pub size: u32,
}

/// Mapping of guest VCPU threads to host CPU cores.
#[derive(Clone, Debug, PartialEq)]
pub enum VcpuAffinity {
    /// All VCPU threads will be pinned to the same set of host CPU cores.
    Global(Vec<usize>),
    /// Each VCPU may be pinned to a set of host CPU cores.
    /// The map key is a guest VCPU index, and the corresponding value is the set of
    /// host CPU indices that the VCPU thread will be allowed to run on.
    /// If a VCPU index is not present in the map, its affinity will not be set.
    PerVcpu(BTreeMap<usize, Vec<usize>>),
}

/// Holds the pieces needed to build a VM. Passed to `build_vm` in the `LinuxArch` trait below to
/// create a `RunnableLinuxVm`.
pub struct VmComponents {
    pub memory_size: u64,
    pub vcpu_count: usize,
    pub vcpu_affinity: Option<VcpuAffinity>,
    pub no_smt: bool,
    pub vm_image: VmImage,
    pub android_fstab: Option<File>,
    pub pstore: Option<Pstore>,
    pub initrd_image: Option<File>,
    pub extra_kernel_params: Vec<String>,
    pub wayland_dmabuf: bool,
    pub acpi_sdts: Vec<SDT>,
    pub rt_cpus: Vec<usize>,
}

/// Holds the elements needed to run a Linux VM. Created by `build_vm`.
pub struct RunnableLinuxVm<V: VmArch, I: IrqChipArch<V::Vcpu>> {
    pub vm: V,
    pub resources: SystemAllocator,
    pub exit_evt: Event,
    pub vcpu_count: usize,
    /// If vcpus is None, then it's the responsibility of the vcpu thread to create vcpus.
    /// If it's Some, then `build_vm` already created the vcpus.
    pub vcpus: Option<Vec<V::Vcpu>>,
    pub vcpu_affinity: Option<VcpuAffinity>,
    pub no_smt: bool,
    pub irq_chip: I,
    pub has_bios: bool,
    pub io_bus: Bus,
    pub mmio_bus: Bus,
    pub pid_debug_label_map: BTreeMap<u32, String>,
    pub suspend_evt: Event,
    pub rt_cpus: Vec<usize>,
}

/// The device and optional jail.
pub struct VirtioDeviceStub {
    pub dev: Box<dyn VirtioDevice>,
    pub jail: Option<Minijail>,
}

/// Trait which is implemented for each Linux Architecture in order to
/// set up the memory, cpus, and system devices and to boot the kernel.
pub trait LinuxArch {
    type Error: StdError;

    /// Takes `VmComponents` and generates a `RunnableLinuxVm`.
    ///
    /// # Arguments
    ///
    /// * `components` - Parts to use to build the VM.
    /// * `serial_parameters` - definitions for how the serial devices should be configured.
    /// * `create_devices` - Function to generate a list of devices.
    /// * `create_vm` - Function to generate a VM.
    /// * `create_irq_chip` - Function to generate an IRQ chip.
    fn build_vm<V, I, FD, FV, FI, E1, E2, E3>(
        components: VmComponents,
        serial_parameters: &BTreeMap<(SerialHardware, u8), SerialParameters>,
        serial_jail: Option<Minijail>,
        create_devices: FD,
        create_vm: FV,
        create_irq_chip: FI,
    ) -> std::result::Result<RunnableLinuxVm<V, I>, Self::Error>
    where
        V: VmArch,
        I: IrqChipArch<V::Vcpu>,
        FD: FnOnce(
            &GuestMemory,
            &mut V,
            &mut SystemAllocator,
            &Event,
        ) -> std::result::Result<Vec<(Box<dyn PciDevice>, Option<Minijail>)>, E1>,
        FV: FnOnce(GuestMemory) -> std::result::Result<V, E2>,
        FI: FnOnce(&V, /* vcpu_count: */ usize) -> std::result::Result<I, E3>,
        E1: StdError + 'static,
        E2: StdError + 'static,
        E3: StdError + 'static;

    /// Configures the vcpu and should be called once per vcpu from the vcpu's thread.
    ///
    /// # Arguments
    ///
    /// * `guest_mem` - The memory to be used by the guest.
    /// * `hypervisor` - The `Hypervisor` that created the vcpu.
    /// * `irq_chip` - The `IrqChip` associated with this vm.
    /// * `vcpu` - The VCPU object to configure.
    /// * `vcpu_id` - The id of the given `vcpu`.
    /// * `num_cpus` - Number of virtual CPUs the guest will have.
    /// * `has_bios` - Whether the `VmImage` is a `Bios` image
    fn configure_vcpu<T: VcpuArch>(
        guest_mem: &GuestMemory,
        hypervisor: &impl HypervisorArch,
        irq_chip: &mut impl IrqChipArch<T>,
        vcpu: &mut impl VcpuArch,
        vcpu_id: usize,
        num_cpus: usize,
        has_bios: bool,
        no_smt: bool,
    ) -> Result<(), Self::Error>;
}

/// Errors for device manager.
#[derive(Debug)]
pub enum DeviceRegistrationError {
    /// Could not allocate IO space for the device.
    AllocateIoAddrs(PciDeviceError),
    /// Could not allocate device address space for the device.
    AllocateDeviceAddrs(PciDeviceError),
    /// Could not allocate an IRQ number.
    AllocateIrq,
    // Unable to create a pipe.
    CreatePipe(base::Error),
    // Unable to create serial device from serial parameters
    CreateSerialDevice(serial::Error),
    /// Could not clone an event.
    EventClone(base::Error),
    /// Could not create an event.
    EventCreate(base::Error),
    /// Missing a required serial device.
    MissingRequiredSerialDevice(u8),
    /// Could not add a device to the mmio bus.
    MmioInsert(BusError),
    /// Failed to register ioevent with VM.
    RegisterIoevent(base::Error),
    /// Failed to register irq event with VM.
    RegisterIrqfd(base::Error),
    /// Failed to initialize proxy device for jailed device.
    ProxyDeviceCreation(devices::ProxyError),
    /// Appending to kernel command line failed.
    Cmdline(kernel_cmdline::Error),
    /// No more IRQs are available.
    IrqsExhausted,
    /// No more MMIO space available.
    AddrsExhausted,
    /// Could not register PCI device capabilities.
    RegisterDeviceCapabilities(PciDeviceError),
}

impl Display for DeviceRegistrationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::DeviceRegistrationError::*;

        match self {
            AllocateIoAddrs(e) => write!(f, "Allocating IO addresses: {}", e),
            AllocateDeviceAddrs(e) => write!(f, "Allocating device addresses: {}", e),
            AllocateIrq => write!(f, "Allocating IRQ number"),
            CreatePipe(e) => write!(f, "failed to create pipe: {}", e),
            CreateSerialDevice(e) => write!(f, "failed to create serial device: {}", e),
            Cmdline(e) => write!(f, "unable to add device to kernel command line: {}", e),
            EventClone(e) => write!(f, "failed to clone event: {}", e),
            EventCreate(e) => write!(f, "failed to create event: {}", e),
            MissingRequiredSerialDevice(n) => write!(f, "missing required serial device {}", n),
            MmioInsert(e) => write!(f, "failed to add to mmio bus: {}", e),
            RegisterIoevent(e) => write!(f, "failed to register ioevent to VM: {}", e),
            RegisterIrqfd(e) => write!(f, "failed to register irq event to VM: {}", e),
            ProxyDeviceCreation(e) => write!(f, "failed to create proxy device: {}", e),
            IrqsExhausted => write!(f, "no more IRQs are available"),
            AddrsExhausted => write!(f, "no more addresses are available"),
            RegisterDeviceCapabilities(e) => {
                write!(f, "could not register PCI device capabilities: {}", e)
            }
        }
    }
}

/// Creates a root PCI device for use by this Vm.
pub fn generate_pci_root<T: Vcpu>(
    mut devices: Vec<(Box<dyn PciDevice>, Option<Minijail>)>,
    irq_chip: &mut impl IrqChip<T>,
    mmio_bus: &mut Bus,
    resources: &mut SystemAllocator,
    vm: &mut impl Vm,
    max_irqs: usize,
) -> Result<
    (
        PciRoot,
        Vec<(PciAddress, u32, PciInterruptPin)>,
        BTreeMap<u32, String>,
    ),
    DeviceRegistrationError,
> {
    let mut root = PciRoot::new();
    let mut pci_irqs = Vec::new();
    let mut pid_labels = BTreeMap::new();

    let mut irqs: Vec<Option<u32>> = vec![None; max_irqs];

    // Assign addresses to all devices before allocating BARs.
    let device_addrs: Vec<PciAddress> = devices
        .iter_mut()
        .enumerate()
        .map(|(dev_idx, (device, _jail))| {
            let address = PciAddress {
                bus: 0,
                dev: 1 + dev_idx as u8,
                func: 0,
            };
            device.assign_address(address);
            address
        })
        .collect();

    // Allocate ranges that may need to be in the low MMIO region (MmioType::Low).
    let mut io_ranges = BTreeMap::new();
    for (dev_idx, (device, _jail)) in devices.iter_mut().enumerate() {
        let ranges = device
            .allocate_io_bars(resources)
            .map_err(DeviceRegistrationError::AllocateIoAddrs)?;
        io_ranges.insert(dev_idx, ranges);
    }

    // Allocate device ranges that may be in low or high MMIO after low-only ranges.
    let mut device_ranges = BTreeMap::new();
    for (dev_idx, (device, _jail)) in devices.iter_mut().enumerate() {
        let ranges = device
            .allocate_device_bars(resources)
            .map_err(DeviceRegistrationError::AllocateDeviceAddrs)?;
        device_ranges.insert(dev_idx, ranges);
    }

    for (dev_idx, (mut device, jail)) in devices.into_iter().enumerate() {
        let address = device_addrs[dev_idx];
        let mut keep_fds = device.keep_fds();
        syslog::push_fds(&mut keep_fds);

        let irqfd = Event::new().map_err(DeviceRegistrationError::EventCreate)?;
        let irq_resample_fd = Event::new().map_err(DeviceRegistrationError::EventCreate)?;
        let irq_num = if let Some(irq) = irqs[dev_idx % max_irqs] {
            irq
        } else {
            let irq = resources
                .allocate_irq()
                .ok_or(DeviceRegistrationError::AllocateIrq)?;
            irqs[dev_idx % max_irqs] = Some(irq);
            irq
        };
        let pci_irq_pin = match dev_idx % 4 {
            0 => PciInterruptPin::IntA,
            1 => PciInterruptPin::IntB,
            2 => PciInterruptPin::IntC,
            3 => PciInterruptPin::IntD,
            _ => unreachable!(), // Obviously not possible, but the compiler is not smart enough.
        };

        irq_chip
            .register_irq_event(irq_num, &irqfd, Some(&irq_resample_fd))
            .map_err(DeviceRegistrationError::RegisterIrqfd)?;

        keep_fds.push(irqfd.as_raw_fd());
        keep_fds.push(irq_resample_fd.as_raw_fd());
        device.assign_irq(irqfd, irq_resample_fd, irq_num, pci_irq_pin);
        pci_irqs.push((address, irq_num, pci_irq_pin));
        let ranges = io_ranges.remove(&dev_idx).unwrap_or_default();
        let device_ranges = device_ranges.remove(&dev_idx).unwrap_or_default();
        device
            .register_device_capabilities()
            .map_err(DeviceRegistrationError::RegisterDeviceCapabilities)?;
        for (event, addr, datamatch) in device.ioevents() {
            let io_addr = IoEventAddress::Mmio(addr);
            vm.register_ioevent(&event, io_addr, datamatch)
                .map_err(DeviceRegistrationError::RegisterIoevent)?;
            keep_fds.push(event.as_raw_fd());
        }
        let arced_dev: Arc<Mutex<dyn BusDevice>> = if let Some(jail) = jail {
            let proxy = ProxyDevice::new(device, &jail, keep_fds)
                .map_err(DeviceRegistrationError::ProxyDeviceCreation)?;
            pid_labels.insert(proxy.pid() as u32, proxy.debug_label());
            Arc::new(Mutex::new(proxy))
        } else {
            device.on_sandboxed();
            Arc::new(Mutex::new(device))
        };
        root.add_device(address, arced_dev.clone());
        for range in &ranges {
            mmio_bus
                .insert(arced_dev.clone(), range.0, range.1, true)
                .map_err(DeviceRegistrationError::MmioInsert)?;
        }

        for range in &device_ranges {
            mmio_bus
                .insert(arced_dev.clone(), range.0, range.1, true)
                .map_err(DeviceRegistrationError::MmioInsert)?;
        }
    }
    Ok((root, pci_irqs, pid_labels))
}

/// Errors for image loading.
#[derive(Debug)]
pub enum LoadImageError {
    BadAlignment(u64),
    Seek(io::Error),
    ImageSizeTooLarge(u64),
    ReadToMemory(GuestMemoryError),
}

impl Display for LoadImageError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::LoadImageError::*;

        match self {
            BadAlignment(a) => write!(f, "Alignment not a power of two: {}", a),
            Seek(e) => write!(f, "Seek failed: {}", e),
            ImageSizeTooLarge(size) => write!(f, "Image size too large: {}", size),
            ReadToMemory(e) => write!(f, "Reading image into memory failed: {}", e),
        }
    }
}

/// Load an image from a file into guest memory.
///
/// # Arguments
///
/// * `guest_mem` - The memory to be used by the guest.
/// * `guest_addr` - The starting address to load the image in the guest memory.
/// * `max_size` - The amount of space in bytes available in the guest memory for the image.
/// * `image` - The file containing the image to be loaded.
///
/// The size in bytes of the loaded image is returned.
pub fn load_image<F>(
    guest_mem: &GuestMemory,
    image: &mut F,
    guest_addr: GuestAddress,
    max_size: u64,
) -> Result<usize, LoadImageError>
where
    F: Read + Seek + AsRawDescriptor,
{
    let size = image.seek(SeekFrom::End(0)).map_err(LoadImageError::Seek)?;

    if size > usize::max_value() as u64 || size > max_size {
        return Err(LoadImageError::ImageSizeTooLarge(size));
    }

    // This is safe due to the bounds check above.
    let size = size as usize;

    image
        .seek(SeekFrom::Start(0))
        .map_err(LoadImageError::Seek)?;

    guest_mem
        .read_to_memory(guest_addr, image, size)
        .map_err(LoadImageError::ReadToMemory)?;

    Ok(size)
}

/// Load an image from a file into guest memory at the highest possible address.
///
/// # Arguments
///
/// * `guest_mem` - The memory to be used by the guest.
/// * `image` - The file containing the image to be loaded.
/// * `min_guest_addr` - The minimum address of the start of the image.
/// * `max_guest_addr` - The address to load the last byte of the image.
/// * `align` - The minimum alignment of the start address of the image in bytes
///   (must be a power of two).
///
/// The guest address and size in bytes of the loaded image are returned.
pub fn load_image_high<F>(
    guest_mem: &GuestMemory,
    image: &mut F,
    min_guest_addr: GuestAddress,
    max_guest_addr: GuestAddress,
    align: u64,
) -> Result<(GuestAddress, usize), LoadImageError>
where
    F: Read + Seek + AsRawDescriptor,
{
    if !align.is_power_of_two() {
        return Err(LoadImageError::BadAlignment(align));
    }

    let max_size = max_guest_addr.offset_from(min_guest_addr) & !(align - 1);
    let size = image.seek(SeekFrom::End(0)).map_err(LoadImageError::Seek)?;

    if size > usize::max_value() as u64 || size > max_size {
        return Err(LoadImageError::ImageSizeTooLarge(size));
    }

    image
        .seek(SeekFrom::Start(0))
        .map_err(LoadImageError::Seek)?;

    // Load image at the maximum aligned address allowed.
    // The subtraction cannot underflow because of the size checks above.
    let guest_addr = GuestAddress((max_guest_addr.offset() - size) & !(align - 1));

    // This is safe due to the bounds check above.
    let size = size as usize;

    guest_mem
        .read_to_memory(guest_addr, image, size)
        .map_err(LoadImageError::ReadToMemory)?;

    Ok((guest_addr, size))
}
