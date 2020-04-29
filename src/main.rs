// Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

//! Runs a virtual machine under KVM

pub mod panic_hook;

use std::default::Default;
use std::fmt;
use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader};
use std::num::ParseIntError;
use std::os::unix::io::{FromRawFd, RawFd};
use std::path::{Path, PathBuf};
use std::string::String;
use std::thread::sleep;
use std::time::Duration;

use arch::{set_default_serial_parameters, Pstore, SerialHardware, SerialParameters, SerialType};
use audio_streams::StreamEffect;
use crosvm::{
    argument::{self, print_help, set_arguments, Argument},
    linux, BindMount, Config, DiskOption, Executable, GidMap, SharedDir, TouchDeviceOption,
};
#[cfg(feature = "gpu")]
use devices::virtio::gpu::{GpuMode, GpuParameters};
use devices::{Ac97Backend, Ac97Parameters};
use disk::QcowFile;
use msg_socket::{MsgReceiver, MsgSender, MsgSocket};
use sys_util::{
    debug, error, getpid, info, kill_process_group, net::UnixSeqpacket, reap_child, syslog,
    validate_raw_fd, warn,
};
use vm_control::{
    BalloonControlCommand, DiskControlCommand, MaybeOwnedFd, UsbControlCommand, UsbControlResult,
    VmControlRequestSocket, VmRequest, VmResponse, USB_CONTROL_MAX_PORTS,
};

fn executable_is_plugin(executable: &Option<Executable>) -> bool {
    match executable {
        Some(Executable::Plugin(_)) => true,
        _ => false,
    }
}

// Wait for all children to exit. Return true if they have all exited, false
// otherwise.
fn wait_all_children() -> bool {
    const CHILD_WAIT_MAX_ITER: isize = 100;
    const CHILD_WAIT_MS: u64 = 10;
    for _ in 0..CHILD_WAIT_MAX_ITER {
        loop {
            match reap_child() {
                Ok(0) => break,
                // We expect ECHILD which indicates that there were no children left.
                Err(e) if e.errno() == libc::ECHILD => return true,
                Err(e) => {
                    warn!("error while waiting for children: {}", e);
                    return false;
                }
                // We reaped one child, so continue reaping.
                _ => {}
            }
        }
        // There's no timeout option for waitpid which reap_child calls internally, so our only
        // recourse is to sleep while waiting for the children to exit.
        sleep(Duration::from_millis(CHILD_WAIT_MS));
    }

    // If we've made it to this point, not all of the children have exited.
    false
}

/// Parse a comma-separated list of CPU numbers and ranges and convert it to a Vec of CPU numbers.
fn parse_cpu_set(s: &str) -> argument::Result<Vec<usize>> {
    let mut cpuset = Vec::new();
    for part in s.split(',') {
        let range: Vec<&str> = part.split('-').collect();
        if range.is_empty() || range.len() > 2 {
            return Err(argument::Error::InvalidValue {
                value: part.to_owned(),
                expected: String::from("invalid list syntax"),
            });
        }
        let first_cpu: usize = range[0]
            .parse()
            .map_err(|_| argument::Error::InvalidValue {
                value: part.to_owned(),
                expected: String::from("CPU index must be a non-negative integer"),
            })?;
        let last_cpu: usize = if range.len() == 2 {
            range[1]
                .parse()
                .map_err(|_| argument::Error::InvalidValue {
                    value: part.to_owned(),
                    expected: String::from("CPU index must be a non-negative integer"),
                })?
        } else {
            first_cpu
        };

        if last_cpu < first_cpu {
            return Err(argument::Error::InvalidValue {
                value: part.to_owned(),
                expected: String::from("CPU ranges must be from low to high"),
            });
        }

        for cpu in first_cpu..=last_cpu {
            cpuset.push(cpu);
        }
    }
    Ok(cpuset)
}

#[cfg(feature = "gpu")]
fn parse_gpu_options(s: Option<&str>) -> argument::Result<GpuParameters> {
    let mut gpu_params: GpuParameters = Default::default();

    if let Some(s) = s {
        let opts = s
            .split(',')
            .map(|frag| frag.split('='))
            .map(|mut kv| (kv.next().unwrap_or(""), kv.next().unwrap_or("")));

        for (k, v) in opts {
            match k {
                // Deprecated: Specifying --gpu=<mode> Not great as the mode can be set multiple
                // times if the user specifies several modes (--gpu=2d,3d,gfxstream)
                "2d" | "2D" => {
                    gpu_params.mode = GpuMode::Mode2D;
                }
                "3d" | "3D" => {
                    gpu_params.mode = GpuMode::Mode3D;
                }
                #[cfg(feature = "gfxstream")]
                "gfxstream" => {
                    gpu_params.mode = GpuMode::ModeGfxStream;
                }
                // Preferred: Specifying --gpu,backend=<mode>
                "backend" => match v {
                    "2d" | "2D" => {
                        gpu_params.mode = GpuMode::Mode2D;
                    }
                    "3d" | "3D" => {
                        gpu_params.mode = GpuMode::Mode3D;
                    }
                    #[cfg(feature = "gfxstream")]
                    "gfxstream" => {
                        gpu_params.mode = GpuMode::ModeGfxStream;
                    }
                    _ => {
                        return Err(argument::Error::InvalidValue {
                            value: v.to_string(),
                            expected: String::from(
                                "gpu parameter 'backend' should be one of (2d|3d|gfxstream)",
                            ),
                        });
                    }
                },
                "egl" => match v {
                    "true" | "" => {
                        gpu_params.renderer_use_egl = true;
                    }
                    "false" => {
                        gpu_params.renderer_use_egl = false;
                    }
                    _ => {
                        return Err(argument::Error::InvalidValue {
                            value: v.to_string(),
                            expected: String::from("gpu parameter 'egl' should be a boolean"),
                        });
                    }
                },
                "gles" => match v {
                    "true" | "" => {
                        gpu_params.renderer_use_gles = true;
                    }
                    "false" => {
                        gpu_params.renderer_use_gles = false;
                    }
                    _ => {
                        return Err(argument::Error::InvalidValue {
                            value: v.to_string(),
                            expected: String::from("gpu parameter 'gles' should be a boolean"),
                        });
                    }
                },
                "glx" => match v {
                    "true" | "" => {
                        gpu_params.renderer_use_glx = true;
                    }
                    "false" => {
                        gpu_params.renderer_use_glx = false;
                    }
                    _ => {
                        return Err(argument::Error::InvalidValue {
                            value: v.to_string(),
                            expected: String::from("gpu parameter 'glx' should be a boolean"),
                        });
                    }
                },
                "surfaceless" => match v {
                    "true" | "" => {
                        gpu_params.renderer_use_surfaceless = true;
                    }
                    "false" => {
                        gpu_params.renderer_use_surfaceless = false;
                    }
                    _ => {
                        return Err(argument::Error::InvalidValue {
                            value: v.to_string(),
                            expected: String::from(
                                "gpu parameter 'surfaceless' should be a boolean",
                            ),
                        });
                    }
                },
                "width" => {
                    gpu_params.display_width =
                        v.parse::<u32>()
                            .map_err(|_| argument::Error::InvalidValue {
                                value: v.to_string(),
                                expected: String::from(
                                    "gpu parameter 'width' must be a valid integer",
                                ),
                            })?;
                }
                "height" => {
                    gpu_params.display_height =
                        v.parse::<u32>()
                            .map_err(|_| argument::Error::InvalidValue {
                                value: v.to_string(),
                                expected: String::from(
                                    "gpu parameter 'height' must be a valid integer",
                                ),
                            })?;
                }
                "" => {}
                _ => {
                    return Err(argument::Error::UnknownArgument(format!(
                        "gpu parameter {}",
                        k
                    )));
                }
            }
        }
    }

    Ok(gpu_params)
}

fn parse_ac97_options(s: &str) -> argument::Result<Ac97Parameters> {
    let mut ac97_params: Ac97Parameters = Default::default();

    let opts = s
        .split(',')
        .map(|frag| frag.split('='))
        .map(|mut kv| (kv.next().unwrap_or(""), kv.next().unwrap_or("")));

    for (k, v) in opts {
        match k {
            "backend" => {
                ac97_params.backend =
                    v.parse::<Ac97Backend>()
                        .map_err(|e| argument::Error::InvalidValue {
                            value: v.to_string(),
                            expected: e.to_string(),
                        })?;
            }
            "capture" => {
                ac97_params.capture = v.parse::<bool>().map_err(|e| {
                    argument::Error::Syntax(format!("invalid capture option: {}", e))
                })?;
            }
            "capture_effects" => {
                ac97_params.capture_effects = v
                    .split('|')
                    .map(|val| {
                        val.parse::<StreamEffect>()
                            .map_err(|e| argument::Error::InvalidValue {
                                value: val.to_string(),
                                expected: e.to_string(),
                            })
                    })
                    .collect::<argument::Result<Vec<_>>>()?;
            }
            _ => {
                return Err(argument::Error::UnknownArgument(format!(
                    "unknown ac97 parameter {}",
                    k
                )));
            }
        }
    }

    Ok(ac97_params)
}

fn parse_serial_options(s: &str) -> argument::Result<SerialParameters> {
    let mut serial_setting = SerialParameters {
        type_: SerialType::Sink,
        hardware: SerialHardware::Serial,
        path: None,
        input: None,
        num: 1,
        console: false,
        earlycon: false,
        stdin: false,
    };

    let opts = s
        .split(',')
        .map(|frag| frag.split('='))
        .map(|mut kv| (kv.next().unwrap_or(""), kv.next().unwrap_or("")));

    for (k, v) in opts {
        match k {
            "hardware" => {
                serial_setting.hardware = v
                    .parse::<SerialHardware>()
                    .map_err(|e| argument::Error::UnknownArgument(format!("{}", e)))?
            }
            "type" => {
                serial_setting.type_ = v
                    .parse::<SerialType>()
                    .map_err(|e| argument::Error::UnknownArgument(format!("{}", e)))?
            }
            "num" => {
                let num = v.parse::<u8>().map_err(|e| {
                    argument::Error::Syntax(format!("serial device number is not parsable: {}", e))
                })?;
                if num < 1 || num > 4 {
                    return Err(argument::Error::InvalidValue {
                        value: num.to_string(),
                        expected: String::from("Serial port num must be between 1 - 4"),
                    });
                }
                serial_setting.num = num;
            }
            "console" => {
                serial_setting.console = v.parse::<bool>().map_err(|e| {
                    argument::Error::Syntax(format!(
                        "serial device console is not parseable: {}",
                        e
                    ))
                })?
            }
            "earlycon" => {
                serial_setting.earlycon = v.parse::<bool>().map_err(|e| {
                    argument::Error::Syntax(format!(
                        "serial device earlycon is not parseable: {}",
                        e,
                    ))
                })?
            }
            "stdin" => {
                serial_setting.stdin = v.parse::<bool>().map_err(|e| {
                    argument::Error::Syntax(format!("serial device stdin is not parseable: {}", e))
                })?;
                if serial_setting.stdin && serial_setting.input.is_some() {
                    return Err(argument::Error::TooManyArguments(
                        "Cannot specify both stdin and input options".to_string(),
                    ));
                }
            }
            "path" => serial_setting.path = Some(PathBuf::from(v)),
            "input" => {
                if serial_setting.stdin {
                    return Err(argument::Error::TooManyArguments(
                        "Cannot specify both stdin and input options".to_string(),
                    ));
                }
                serial_setting.input = Some(PathBuf::from(v));
            }
            _ => {
                return Err(argument::Error::UnknownArgument(format!(
                    "serial parameter {}",
                    k
                )));
            }
        }
    }

    Ok(serial_setting)
}

fn parse_plugin_mount_option(value: &str) -> argument::Result<BindMount> {
    let components: Vec<&str> = value.split(':').collect();
    if components.is_empty() || components.len() > 3 || components[0].is_empty() {
        return Err(argument::Error::InvalidValue {
            value: value.to_owned(),
            expected: String::from(
                "`plugin-mount` should be in a form of: <src>[:[<dst>][:<writable>]]",
            ),
        });
    }

    let src = PathBuf::from(components[0]);
    if src.is_relative() {
        return Err(argument::Error::InvalidValue {
            value: components[0].to_owned(),
            expected: String::from("the source path for `plugin-mount` must be absolute"),
        });
    }
    if !src.exists() {
        return Err(argument::Error::InvalidValue {
            value: components[0].to_owned(),
            expected: String::from("the source path for `plugin-mount` does not exist"),
        });
    }

    let dst = PathBuf::from(match components.get(1) {
        None | Some(&"") => components[0],
        Some(path) => path,
    });
    if dst.is_relative() {
        return Err(argument::Error::InvalidValue {
            value: components[1].to_owned(),
            expected: String::from("the destination path for `plugin-mount` must be absolute"),
        });
    }

    let writable: bool = match components.get(2) {
        None => false,
        Some(s) => s.parse().map_err(|_| argument::Error::InvalidValue {
            value: components[2].to_owned(),
            expected: String::from("the <writable> component for `plugin-mount` is not valid bool"),
        })?,
    };

    Ok(BindMount { src, dst, writable })
}

fn parse_plugin_gid_map_option(value: &str) -> argument::Result<GidMap> {
    let components: Vec<&str> = value.split(':').collect();
    if components.is_empty() || components.len() > 3 || components[0].is_empty() {
        return Err(argument::Error::InvalidValue {
            value: value.to_owned(),
            expected: String::from(
                "`plugin-gid-map` must have exactly 3 components: <inner>[:[<outer>][:<count>]]",
            ),
        });
    }

    let inner: libc::gid_t = components[0]
        .parse()
        .map_err(|_| argument::Error::InvalidValue {
            value: components[0].to_owned(),
            expected: String::from("the <inner> component for `plugin-gid-map` is not valid gid"),
        })?;

    let outer: libc::gid_t = match components.get(1) {
        None | Some(&"") => inner,
        Some(s) => s.parse().map_err(|_| argument::Error::InvalidValue {
            value: components[1].to_owned(),
            expected: String::from("the <outer> component for `plugin-gid-map` is not valid gid"),
        })?,
    };

    let count: u32 = match components.get(2) {
        None => 1,
        Some(s) => s.parse().map_err(|_| argument::Error::InvalidValue {
            value: components[2].to_owned(),
            expected: String::from(
                "the <count> component for `plugin-gid-map` is not valid number",
            ),
        })?,
    };

    Ok(GidMap {
        inner,
        outer,
        count,
    })
}

fn set_argument(cfg: &mut Config, name: &str, value: Option<&str>) -> argument::Result<()> {
    match name {
        "" => {
            if cfg.executable_path.is_some() {
                return Err(argument::Error::TooManyArguments(format!(
                    "A VM executable was already specified: {:?}",
                    cfg.executable_path
                )));
            }
            let kernel_path = PathBuf::from(value.unwrap());
            if !kernel_path.exists() {
                return Err(argument::Error::InvalidValue {
                    value: value.unwrap().to_owned(),
                    expected: String::from("this kernel path does not exist"),
                });
            }
            cfg.executable_path = Some(Executable::Kernel(kernel_path));
        }
        "android-fstab" => {
            if cfg.android_fstab.is_some()
                && !cfg.android_fstab.as_ref().unwrap().as_os_str().is_empty()
            {
                return Err(argument::Error::TooManyArguments(
                    "expected exactly one android fstab path".to_owned(),
                ));
            } else {
                let android_fstab = PathBuf::from(value.unwrap());
                if !android_fstab.exists() {
                    return Err(argument::Error::InvalidValue {
                        value: value.unwrap().to_owned(),
                        expected: String::from("this android fstab path does not exist"),
                    });
                }
                cfg.android_fstab = Some(android_fstab);
            }
        }
        "params" => {
            cfg.params.push(value.unwrap().to_owned());
        }
        "cpus" => {
            if cfg.vcpu_count.is_some() {
                return Err(argument::Error::TooManyArguments(
                    "`cpus` already given".to_owned(),
                ));
            }
            cfg.vcpu_count =
                Some(
                    value
                        .unwrap()
                        .parse()
                        .map_err(|_| argument::Error::InvalidValue {
                            value: value.unwrap().to_owned(),
                            expected: String::from("this value for `cpus` needs to be integer"),
                        })?,
                )
        }
        "cpu-affinity" => {
            if !cfg.vcpu_affinity.is_empty() {
                return Err(argument::Error::TooManyArguments(
                    "`cpu-affinity` already given".to_owned(),
                ));
            }
            cfg.vcpu_affinity = parse_cpu_set(value.unwrap())?;
        }
        "mem" => {
            if cfg.memory.is_some() {
                return Err(argument::Error::TooManyArguments(
                    "`mem` already given".to_owned(),
                ));
            }
            cfg.memory =
                Some(
                    value
                        .unwrap()
                        .parse()
                        .map_err(|_| argument::Error::InvalidValue {
                            value: value.unwrap().to_owned(),
                            expected: String::from("this value for `mem` needs to be integer"),
                        })?,
                )
        }
        "ac97" => {
            let ac97_params = parse_ac97_options(value.unwrap())?;
            cfg.ac97_parameters.push(ac97_params);
        }
        "serial" => {
            let serial_params = parse_serial_options(value.unwrap())?;
            let num = serial_params.num;
            let key = (serial_params.hardware, num);
            if cfg.serial_parameters.contains_key(&key) {
                return Err(argument::Error::TooManyArguments(format!(
                    "serial hardware {} num {}",
                    serial_params.hardware, num,
                )));
            }

            if serial_params.console {
                for params in cfg.serial_parameters.values() {
                    if params.console {
                        return Err(argument::Error::TooManyArguments(format!(
                            "{} device {} already set as console",
                            params.hardware, params.num,
                        )));
                    }
                }
            }

            if serial_params.earlycon {
                // Only SerialHardware::Serial supports earlycon= currently.
                match serial_params.hardware {
                    SerialHardware::Serial => {}
                    _ => {
                        return Err(argument::Error::InvalidValue {
                            value: serial_params.hardware.to_string().to_owned(),
                            expected: String::from("earlycon not supported for hardware"),
                        });
                    }
                }
                for params in cfg.serial_parameters.values() {
                    if params.earlycon {
                        return Err(argument::Error::TooManyArguments(format!(
                            "{} device {} already set as earlycon",
                            params.hardware, params.num,
                        )));
                    }
                }
            }

            if serial_params.stdin {
                if let Some(previous_stdin) = cfg.serial_parameters.values().find(|sp| sp.stdin) {
                    return Err(argument::Error::TooManyArguments(format!(
                        "{} device {} already connected to standard input",
                        previous_stdin.hardware, previous_stdin.num,
                    )));
                }
            }

            cfg.serial_parameters.insert(key, serial_params);
        }
        "syslog-tag" => {
            if cfg.syslog_tag.is_some() {
                return Err(argument::Error::TooManyArguments(
                    "`syslog-tag` already given".to_owned(),
                ));
            }
            syslog::set_proc_name(value.unwrap());
            cfg.syslog_tag = Some(value.unwrap().to_owned());
        }
        "root" | "rwroot" | "disk" | "rwdisk" => {
            let param = value.unwrap();
            let mut components = param.split(',');
            let read_only = !name.starts_with("rw");
            let disk_path =
                PathBuf::from(
                    components
                        .next()
                        .ok_or_else(|| argument::Error::InvalidValue {
                            value: param.to_owned(),
                            expected: String::from("missing disk path"),
                        })?,
                );
            if !disk_path.exists() {
                return Err(argument::Error::InvalidValue {
                    value: param.to_owned(),
                    expected: String::from("this disk path does not exist"),
                });
            }
            if name.ends_with("root") {
                if cfg.disks.len() >= 26 {
                    return Err(argument::Error::TooManyArguments(
                        "ran out of letters for to assign to root disk".to_owned(),
                    ));
                }
                cfg.params.push(format!(
                    "root=/dev/vd{} {}",
                    char::from(b'a' + cfg.disks.len() as u8),
                    if read_only { "ro" } else { "rw" }
                ));
            }

            let mut disk = DiskOption {
                path: disk_path,
                read_only,
                sparse: true,
                block_size: 512,
            };

            for opt in components {
                let mut o = opt.splitn(2, '=');
                let kind = o.next().ok_or_else(|| argument::Error::InvalidValue {
                    value: opt.to_owned(),
                    expected: String::from("disk options must not be empty"),
                })?;
                let value = o.next().ok_or_else(|| argument::Error::InvalidValue {
                    value: opt.to_owned(),
                    expected: String::from("disk options must be of the form `kind=value`"),
                })?;

                match kind {
                    "sparse" => {
                        let sparse = value.parse().map_err(|_| argument::Error::InvalidValue {
                            value: value.to_owned(),
                            expected: String::from("`sparse` must be a boolean"),
                        })?;
                        disk.sparse = sparse;
                    }
                    "block_size" => {
                        let block_size =
                            value.parse().map_err(|_| argument::Error::InvalidValue {
                                value: value.to_owned(),
                                expected: String::from("`block_size` must be an integer"),
                            })?;
                        disk.block_size = block_size;
                    }
                    _ => {
                        return Err(argument::Error::InvalidValue {
                            value: kind.to_owned(),
                            expected: String::from("unrecognized disk option"),
                        });
                    }
                }
            }

            cfg.disks.push(disk);
        }
        "pmem-device" | "rw-pmem-device" => {
            let disk_path = PathBuf::from(value.unwrap());
            if !disk_path.exists() {
                return Err(argument::Error::InvalidValue {
                    value: value.unwrap().to_owned(),
                    expected: String::from("this disk path does not exist"),
                });
            }

            cfg.pmem_devices.push(DiskOption {
                path: disk_path,
                read_only: !name.starts_with("rw"),
                sparse: false,
                block_size: sys_util::pagesize() as u32,
            });
        }
        "pstore" => {
            if cfg.pstore.is_some() {
                return Err(argument::Error::TooManyArguments(
                    "`pstore` already given".to_owned(),
                ));
            }

            let value = value.unwrap();
            let components: Vec<&str> = value.split(',').collect();
            if components.len() != 2 {
                return Err(argument::Error::InvalidValue {
                    value: value.to_owned(),
                    expected: String::from(
                        "pstore must have exactly 2 components: path=<path>,size=<size>",
                    ),
                });
            }
            cfg.pstore = Some(Pstore {
                path: {
                    if components[0].len() <= 5 || !components[0].starts_with("path=") {
                        return Err(argument::Error::InvalidValue {
                            value: components[0].to_owned(),
                            expected: String::from("pstore path must follow with `path=`"),
                        });
                    };
                    PathBuf::from(&components[0][5..])
                },
                size: {
                    if components[1].len() <= 5 || !components[1].starts_with("size=") {
                        return Err(argument::Error::InvalidValue {
                            value: components[1].to_owned(),
                            expected: String::from("pstore size must follow with `size=`"),
                        });
                    };
                    components[1][5..]
                        .parse()
                        .map_err(|_| argument::Error::InvalidValue {
                            value: value.to_owned(),
                            expected: String::from("pstore size must be an integer"),
                        })?
                },
            });
        }
        "host_ip" => {
            if cfg.host_ip.is_some() {
                return Err(argument::Error::TooManyArguments(
                    "`host_ip` already given".to_owned(),
                ));
            }
            cfg.host_ip =
                Some(
                    value
                        .unwrap()
                        .parse()
                        .map_err(|_| argument::Error::InvalidValue {
                            value: value.unwrap().to_owned(),
                            expected: String::from("`host_ip` needs to be in the form \"x.x.x.x\""),
                        })?,
                )
        }
        "netmask" => {
            if cfg.netmask.is_some() {
                return Err(argument::Error::TooManyArguments(
                    "`netmask` already given".to_owned(),
                ));
            }
            cfg.netmask =
                Some(
                    value
                        .unwrap()
                        .parse()
                        .map_err(|_| argument::Error::InvalidValue {
                            value: value.unwrap().to_owned(),
                            expected: String::from("`netmask` needs to be in the form \"x.x.x.x\""),
                        })?,
                )
        }
        "mac" => {
            if cfg.mac_address.is_some() {
                return Err(argument::Error::TooManyArguments(
                    "`mac` already given".to_owned(),
                ));
            }
            cfg.mac_address =
                Some(
                    value
                        .unwrap()
                        .parse()
                        .map_err(|_| argument::Error::InvalidValue {
                            value: value.unwrap().to_owned(),
                            expected: String::from(
                                "`mac` needs to be in the form \"XX:XX:XX:XX:XX:XX\"",
                            ),
                        })?,
                )
        }
        "net-vq-pairs" => {
            if cfg.net_vq_pairs.is_some() {
                return Err(argument::Error::TooManyArguments(
                    "`net-vq-pairs` already given".to_owned(),
                ));
            }
            cfg.net_vq_pairs =
                Some(
                    value
                        .unwrap()
                        .parse()
                        .map_err(|_| argument::Error::InvalidValue {
                            value: value.unwrap().to_owned(),
                            expected: String::from(
                                "this value for `net-vq-pairs` needs to be integer",
                            ),
                        })?,
                )
        }

        "wayland-sock" => {
            let mut components = value.unwrap().split(',');
            let path =
                PathBuf::from(
                    components
                        .next()
                        .ok_or_else(|| argument::Error::InvalidValue {
                            value: value.unwrap().to_owned(),
                            expected: String::from("missing socket path"),
                        })?,
                );
            let mut name = "";
            for c in components {
                let mut kv = c.splitn(2, '=');
                let (kind, value) = match (kv.next(), kv.next()) {
                    (Some(kind), Some(value)) => (kind, value),
                    _ => {
                        return Err(argument::Error::InvalidValue {
                            value: c.to_owned(),
                            expected: String::from("option must be of the form `kind=value`"),
                        })
                    }
                };
                match kind {
                    "name" => name = value,
                    _ => {
                        return Err(argument::Error::InvalidValue {
                            value: kind.to_owned(),
                            expected: String::from("unrecognized option"),
                        })
                    }
                }
            }
            if cfg.wayland_socket_paths.contains_key(name) {
                return Err(argument::Error::TooManyArguments(format!(
                    "wayland socket name already used: '{}'",
                    name
                )));
            }
            cfg.wayland_socket_paths.insert(name.to_string(), path);
        }
        #[cfg(feature = "wl-dmabuf")]
        "wayland-dmabuf" => cfg.wayland_dmabuf = true,
        "x-display" => {
            if cfg.x_display.is_some() {
                return Err(argument::Error::TooManyArguments(
                    "`x-display` already given".to_owned(),
                ));
            }
            cfg.x_display = Some(value.unwrap().to_owned());
        }
        "display-window-keyboard" => {
            cfg.display_window_keyboard = true;
        }
        "display-window-mouse" => {
            cfg.display_window_mouse = true;
        }
        "socket" => {
            if cfg.socket_path.is_some() {
                return Err(argument::Error::TooManyArguments(
                    "`socket` already given".to_owned(),
                ));
            }
            let mut socket_path = PathBuf::from(value.unwrap());
            if socket_path.is_dir() {
                socket_path.push(format!("crosvm-{}.sock", getpid()));
            }
            if socket_path.exists() {
                return Err(argument::Error::InvalidValue {
                    value: socket_path.to_string_lossy().into_owned(),
                    expected: String::from("this socket path already exists"),
                });
            }
            cfg.socket_path = Some(socket_path);
        }
        "disable-sandbox" => {
            cfg.sandbox = false;
        }
        "cid" => {
            if cfg.cid.is_some() {
                return Err(argument::Error::TooManyArguments(
                    "`cid` alread given".to_owned(),
                ));
            }
            cfg.cid = Some(
                value
                    .unwrap()
                    .parse()
                    .map_err(|_| argument::Error::InvalidValue {
                        value: value.unwrap().to_owned(),
                        expected: String::from("this value for `cid` must be an unsigned integer"),
                    })?,
            );
        }
        "shared-dir" => {
            // This is formatted as multiple fields, each separated by ":". The first 2 fields are
            // fixed (src:tag).  The rest may appear in any order:
            //
            // * type=TYPE - must be one of "p9" or "fs" (default: p9)
            // * uidmap=UIDMAP - a uid map in the format "inner outer count[,inner outer count]"
            //   (default: "0 <current euid> 1")
            // * gidmap=GIDMAP - a gid map in the same format as uidmap
            //   (default: "0 <current egid> 1")
            // * timeout=TIMEOUT - a timeout value in seconds, which indicates how long attributes
            //   and directory contents should be considered valid (default: 5)
            // * cache=CACHE - one of "never", "always", or "auto" (default: auto)
            // * writeback=BOOL - indicates whether writeback caching should be enabled (default: false)
            let param = value.unwrap();
            let mut components = param.split(':');
            let src =
                PathBuf::from(
                    components
                        .next()
                        .ok_or_else(|| argument::Error::InvalidValue {
                            value: param.to_owned(),
                            expected: String::from("missing source path for `shared-dir`"),
                        })?,
                );
            let tag = components
                .next()
                .ok_or_else(|| argument::Error::InvalidValue {
                    value: param.to_owned(),
                    expected: String::from("missing tag for `shared-dir`"),
                })?
                .to_owned();

            if !src.is_dir() {
                return Err(argument::Error::InvalidValue {
                    value: param.to_owned(),
                    expected: String::from("source path for `shared-dir` must be a directory"),
                });
            }

            let mut shared_dir = SharedDir {
                src,
                tag,
                ..Default::default()
            };
            for opt in components {
                let mut o = opt.splitn(2, '=');
                let kind = o.next().ok_or_else(|| argument::Error::InvalidValue {
                    value: opt.to_owned(),
                    expected: String::from("`shared-dir` options must not be empty"),
                })?;
                let value = o.next().ok_or_else(|| argument::Error::InvalidValue {
                    value: opt.to_owned(),
                    expected: String::from("`shared-dir` options must be of the form `kind=value`"),
                })?;

                match kind {
                    "type" => {
                        shared_dir.kind =
                            value.parse().map_err(|_| argument::Error::InvalidValue {
                                value: value.to_owned(),
                                expected: String::from("`type` must be one of `fs` or `9p`"),
                            })?
                    }
                    "uidmap" => shared_dir.uid_map = value.into(),
                    "gidmap" => shared_dir.gid_map = value.into(),
                    "timeout" => {
                        let seconds = value.parse().map_err(|_| argument::Error::InvalidValue {
                            value: value.to_owned(),
                            expected: String::from("`timeout` must be an integer"),
                        })?;

                        let dur = Duration::from_secs(seconds);
                        shared_dir.cfg.entry_timeout = dur.clone();
                        shared_dir.cfg.attr_timeout = dur;
                    }
                    "cache" => {
                        let policy = value.parse().map_err(|_| argument::Error::InvalidValue {
                            value: value.to_owned(),
                            expected: String::from(
                                "`cache` must be one of `never`, `always`, or `auto`",
                            ),
                        })?;
                        shared_dir.cfg.cache_policy = policy;
                    }
                    "writeback" => {
                        let writeback =
                            value.parse().map_err(|_| argument::Error::InvalidValue {
                                value: value.to_owned(),
                                expected: String::from("`writeback` must be a boolean"),
                            })?;
                        shared_dir.cfg.writeback = writeback;
                    }
                    _ => {
                        return Err(argument::Error::InvalidValue {
                            value: kind.to_owned(),
                            expected: String::from("unrecognized option for `shared-dir`"),
                        })
                    }
                }
            }
            cfg.shared_dirs.push(shared_dir);
        }
        "seccomp-policy-dir" => {
            // `value` is Some because we are in this match so it's safe to unwrap.
            cfg.seccomp_policy_dir = PathBuf::from(value.unwrap());
        }
        "seccomp-log-failures" => {
            // A side-effect of this flag is to force the use of .policy files
            // instead of .bpf files (.bpf files are expected and assumed to be
            // compiled to fail an unpermitted action with "trap").
            // Normally crosvm will first attempt to use a .bpf file, and if
            // not present it will then try to use a .policy file.  It's up
            // to the build to decide which of these files is present for
            // crosvm to use (for CrOS the build will use .bpf files for
            // x64 builds and .policy files for arm/arm64 builds).
            //
            // This flag will likely work as expected for builds that use
            // .policy files.  For builds that only use .bpf files the initial
            // result when using this flag is likely to be a file-not-found
            // error (since the .policy files are not present).
            // For .bpf builds you can either 1) manually add the .policy files,
            // or 2) do not use this command-line parameter and instead
            // temporarily change the build by passing "log" rather than
            // "trap" as the "--default-action" to compile_seccomp_policy.py.
            cfg.seccomp_log_failures = true;
        }
        "plugin" => {
            if cfg.executable_path.is_some() {
                return Err(argument::Error::TooManyArguments(format!(
                    "A VM executable was already specified: {:?}",
                    cfg.executable_path
                )));
            }
            let plugin = PathBuf::from(value.unwrap().to_owned());
            if plugin.is_relative() {
                return Err(argument::Error::InvalidValue {
                    value: plugin.to_string_lossy().into_owned(),
                    expected: String::from("the plugin path must be an absolute path"),
                });
            }
            cfg.executable_path = Some(Executable::Plugin(plugin));
        }
        "plugin-root" => {
            cfg.plugin_root = Some(PathBuf::from(value.unwrap().to_owned()));
        }
        "plugin-mount" => {
            let mount = parse_plugin_mount_option(value.unwrap())?;
            cfg.plugin_mounts.push(mount);
        }
        "plugin-mount-file" => {
            let file = File::open(value.unwrap()).map_err(|_| argument::Error::InvalidValue {
                value: value.unwrap().to_owned(),
                expected: String::from("unable to open `plugin-mount-file` file"),
            })?;
            let reader = BufReader::new(file);
            for l in reader.lines() {
                let line = l.unwrap();
                let trimmed_line = line.splitn(2, '#').next().unwrap().trim();
                if !trimmed_line.is_empty() {
                    let mount = parse_plugin_mount_option(trimmed_line)?;
                    cfg.plugin_mounts.push(mount);
                }
            }
        }
        "plugin-gid-map" => {
            let map = parse_plugin_gid_map_option(value.unwrap())?;
            cfg.plugin_gid_maps.push(map);
        }
        "plugin-gid-map-file" => {
            let file = File::open(value.unwrap()).map_err(|_| argument::Error::InvalidValue {
                value: value.unwrap().to_owned(),
                expected: String::from("unable to open `plugin-gid-map-file` file"),
            })?;
            let reader = BufReader::new(file);
            for l in reader.lines() {
                let line = l.unwrap();
                let trimmed_line = line.splitn(2, '#').next().unwrap().trim();
                if !trimmed_line.is_empty() {
                    let map = parse_plugin_gid_map_option(trimmed_line)?;
                    cfg.plugin_gid_maps.push(map);
                }
            }
        }
        "vhost-net" => cfg.vhost_net = true,
        "tap-fd" => {
            cfg.tap_fd.push(
                value
                    .unwrap()
                    .parse()
                    .map_err(|_| argument::Error::InvalidValue {
                        value: value.unwrap().to_owned(),
                        expected: String::from(
                            "this value for `tap-fd` must be an unsigned integer",
                        ),
                    })?,
            );
        }
        #[cfg(feature = "gpu")]
        "gpu" => {
            let params = parse_gpu_options(value)?;
            cfg.gpu_parameters = Some(params);
        }
        "software-tpm" => {
            cfg.software_tpm = true;
        }
        "single-touch" => {
            if cfg.virtio_single_touch.is_some() {
                return Err(argument::Error::TooManyArguments(
                    "`single-touch` already given".to_owned(),
                ));
            }
            let mut it = value.unwrap().split(':');

            let mut single_touch_spec =
                TouchDeviceOption::new(PathBuf::from(it.next().unwrap().to_owned()));
            if let Some(width) = it.next() {
                single_touch_spec.set_width(width.trim().parse().unwrap());
            }
            if let Some(height) = it.next() {
                single_touch_spec.set_height(height.trim().parse().unwrap());
            }
            cfg.virtio_single_touch = Some(single_touch_spec);
        }
        "trackpad" => {
            if cfg.virtio_trackpad.is_some() {
                return Err(argument::Error::TooManyArguments(
                    "`trackpad` already given".to_owned(),
                ));
            }
            let mut it = value.unwrap().split(':');

            let mut trackpad_spec =
                TouchDeviceOption::new(PathBuf::from(it.next().unwrap().to_owned()));
            if let Some(width) = it.next() {
                trackpad_spec.set_width(width.trim().parse().unwrap());
            }
            if let Some(height) = it.next() {
                trackpad_spec.set_height(height.trim().parse().unwrap());
            }
            cfg.virtio_trackpad = Some(trackpad_spec);
        }
        "mouse" => {
            if cfg.virtio_mouse.is_some() {
                return Err(argument::Error::TooManyArguments(
                    "`mouse` already given".to_owned(),
                ));
            }
            cfg.virtio_mouse = Some(PathBuf::from(value.unwrap().to_owned()));
        }
        "keyboard" => {
            if cfg.virtio_keyboard.is_some() {
                return Err(argument::Error::TooManyArguments(
                    "`keyboard` already given".to_owned(),
                ));
            }
            cfg.virtio_keyboard = Some(PathBuf::from(value.unwrap().to_owned()));
        }
        "evdev" => {
            let dev_path = PathBuf::from(value.unwrap());
            if !dev_path.exists() {
                return Err(argument::Error::InvalidValue {
                    value: value.unwrap().to_owned(),
                    expected: String::from("this input device path does not exist"),
                });
            }
            cfg.virtio_input_evdevs.push(dev_path);
        }
        "split-irqchip" => {
            cfg.split_irqchip = true;
        }
        "initrd" => {
            cfg.initrd_path = Some(PathBuf::from(value.unwrap().to_owned()));
        }
        "bios" => {
            if cfg.executable_path.is_some() {
                return Err(argument::Error::TooManyArguments(format!(
                    "A VM executable was already specified: {:?}",
                    cfg.executable_path
                )));
            }
            cfg.executable_path = Some(Executable::Bios(PathBuf::from(value.unwrap().to_owned())));
        }
        "vfio" => {
            let vfio_path = PathBuf::from(value.unwrap());
            if !vfio_path.exists() {
                return Err(argument::Error::InvalidValue {
                    value: value.unwrap().to_owned(),
                    expected: String::from("the vfio path does not exist"),
                });
            }
            if !vfio_path.is_dir() {
                return Err(argument::Error::InvalidValue {
                    value: value.unwrap().to_owned(),
                    expected: String::from("the vfio path should be directory"),
                });
            }

            cfg.vfio.push(vfio_path);
        }

        "help" => return Err(argument::Error::PrintHelp),
        _ => unreachable!(),
    }
    Ok(())
}

fn validate_arguments(cfg: &mut Config) -> std::result::Result<(), argument::Error> {
    if cfg.executable_path.is_none() {
        return Err(argument::Error::ExpectedArgument("`KERNEL`".to_owned()));
    }
    if cfg.host_ip.is_some() || cfg.netmask.is_some() || cfg.mac_address.is_some() {
        if cfg.host_ip.is_none() {
            return Err(argument::Error::ExpectedArgument(
                "`host_ip` missing from network config".to_owned(),
            ));
        }
        if cfg.netmask.is_none() {
            return Err(argument::Error::ExpectedArgument(
                "`netmask` missing from network config".to_owned(),
            ));
        }
        if cfg.mac_address.is_none() {
            return Err(argument::Error::ExpectedArgument(
                "`mac` missing from network config".to_owned(),
            ));
        }
    }
    if cfg.plugin_root.is_some() && !executable_is_plugin(&cfg.executable_path) {
        return Err(argument::Error::ExpectedArgument(
            "`plugin-root` requires `plugin`".to_owned(),
        ));
    }
    #[cfg(feature = "gpu")]
    {
        if let Some(gpu_parameters) = cfg.gpu_parameters.as_ref() {
            let (width, height) = (gpu_parameters.display_width, gpu_parameters.display_height);
            if let Some(virtio_single_touch) = cfg.virtio_single_touch.as_mut() {
                virtio_single_touch.set_default_size(width, height);
            }
        }
    }
    set_default_serial_parameters(&mut cfg.serial_parameters);
    Ok(())
}

fn run_vm(args: std::env::Args) -> std::result::Result<(), ()> {
    let arguments =
        &[Argument::positional("KERNEL", "bzImage of kernel to run"),
          Argument::value("android-fstab", "PATH", "Path to Android fstab"),
          Argument::short_value('i', "initrd", "PATH", "Initial ramdisk to load."),
          Argument::short_value('p',
                                "params",
                                "PARAMS",
                                "Extra kernel or plugin command line arguments. Can be given more than once."),
          Argument::short_value('c', "cpus", "N", "Number of VCPUs. (default: 1)"),
          Argument::value("cpu-affinity", "CPUSET", "Comma-separated list of CPUs or CPU ranges to run VCPUs on. (e.g. 0,1-3,5) (default: no mask)"),
          Argument::short_value('m',
                                "mem",
                                "N",
                                "Amount of guest memory in MiB. (default: 256)"),
          Argument::short_value('r',
                                "root",
                                "PATH[,key=value[,key=value[,...]]",
                                "Path to a root disk image followed by optional comma-separated options.
                              Like `--disk` but adds appropriate kernel command line option.
                              See --disk for valid options."),
          Argument::value("rwroot", "PATH[,key=value[,key=value[,...]]", "Path to a writable root disk image followed by optional comma-separated options.
                              See --disk for valid options."),
          Argument::short_value('d', "disk", "PATH[,key=value[,key=value[,...]]", "Path to a disk image followed by optional comma-separated options.
                              Valid keys:
                              sparse=BOOL - Indicates whether the disk should support the discard operation (default: true)
                              block_size=BYTES - Set the reported block size of the disk (default: 512)"),
          Argument::value("rwdisk", "PATH[,key=value[,key=value[,...]]", "Path to a writable disk image followed by optional comma-separated options.
                              See --disk for valid options."),
          Argument::value("rw-pmem-device", "PATH", "Path to a writable disk image."),
          Argument::value("pmem-device", "PATH", "Path to a disk image."),
          Argument::value("pstore", "path=PATH,size=SIZE", "Path to pstore buffer backend file follewed by size."),
          Argument::value("host_ip",
                          "IP",
                          "IP address to assign to host tap interface."),
          Argument::value("netmask", "NETMASK", "Netmask for VM subnet."),
          Argument::value("mac", "MAC", "MAC address for VM."),
          Argument::value("net-vq-pairs", "N", "virtio net virtual queue paris. (default: 1)"),
          Argument::value("ac97",
                          "[backend=BACKEND,capture=true,capture_effect=EFFECT]",
                          "Comma separated key=value pairs for setting up Ac97 devices. Can be given more than once .
                          Possible key values:
                          backend=(null, cras) - Where to route the audio device. If not provided, backend will default to null.
                          `null` for /dev/null, and  cras for CRAS server.
                          capture - Enable audio capture
                          capture_effects - | separated effects to be enabled for recording. The only supported effect value now is EchoCancellation or aec."),
          Argument::value("serial",
                          "type=TYPE,[hardware=HW,num=NUM,path=PATH,input=PATH,console,earlycon,stdin]",
                          "Comma separated key=value pairs for setting up serial devices. Can be given more than once.
                          Possible key values:
                          type=(stdout,syslog,sink,file) - Where to route the serial device
                          hardware=(serial,virtio-console) - Which type of serial hardware to emulate. Defaults to 8250 UART (serial).
                          num=(1,2,3,4) - Serial Device Number. If not provided, num will default to 1.
                          path=PATH - The path to the file to write to when type=file
                          input=PATH - The path to the file to read from when not stdin
                          console - Use this serial device as the guest console. Can only be given once. Will default to first serial port if not provided.
                          earlycon - Use this serial device as the early console. Can only be given once.
                          stdin - Direct standard input to this serial device. Can only be given once. Will default to first serial port if not provided.
                          "),
          Argument::value("syslog-tag", "TAG", "When logging to syslog, use the provided tag."),
          Argument::value("x-display", "DISPLAY", "X11 display name to use."),
          Argument::flag("display-window-keyboard", "Capture keyboard input from the display window."),
          Argument::flag("display-window-mouse", "Capture keyboard input from the display window."),
          Argument::value("wayland-sock", "PATH[,name=NAME]", "Path to the Wayland socket to use. The unnamed one is used for displaying virtual screens. Named ones are only for IPC."),
          #[cfg(feature = "wl-dmabuf")]
          Argument::flag("wayland-dmabuf", "Enable support for DMABufs in Wayland device."),
          Argument::short_value('s',
                                "socket",
                                "PATH",
                                "Path to put the control socket. If PATH is a directory, a name will be generated."),
          Argument::flag("disable-sandbox", "Run all devices in one, non-sandboxed process."),
          Argument::value("cid", "CID", "Context ID for virtual sockets."),
          Argument::value("shared-dir", "PATH:TAG[:type=TYPE:writeback=BOOL:timeout=SECONDS:uidmap=UIDMAP:gidmap=GIDMAP:cache=CACHE]",
                          "Colon-separated options for configuring a directory to be shared with the VM.
The first field is the directory to be shared and the second field is the tag that the VM can use to identify the device.
The remaining fields are key=value pairs that may appear in any order.  Valid keys are:
type=(p9, fs) - Indicates whether the directory should be shared via virtio-9p or virtio-fs (default: p9).
uidmap=UIDMAP - The uid map to use for the device's jail in the format \"inner outer count[,inner outer count]\" (default: 0 <current euid> 1).
gidmap=GIDMAP - The gid map to use for the device's jail in the format \"inner outer count[,inner outer count]\" (default: 0 <current egid> 1).
cache=(never, auto, always) - Indicates whether the VM can cache the contents of the shared directory (default: auto).  When set to \"auto\" and the type is \"fs\", the VM will use close-to-open consistency for file contents.
timeout=SECONDS - How long the VM should consider file attributes and directory entries to be valid (default: 5).  If the VM has exclusive access to the directory, then this should be a large value.  If the directory can be modified by other processes, then this should be 0.
writeback=BOOL - Indicates whether the VM can use writeback caching (default: false).  This is only safe to do when the VM has exclusive access to the files in a directory.  Additionally, the server should have read permission for all files as the VM may issue read requests even for files that are opened write-only.
"),
          Argument::value("seccomp-policy-dir", "PATH", "Path to seccomp .policy files."),
          Argument::flag("seccomp-log-failures", "Instead of seccomp filter failures being fatal, they will be logged instead."),
          #[cfg(feature = "plugin")]
          Argument::value("plugin", "PATH", "Absolute path to plugin process to run under crosvm."),
          #[cfg(feature = "plugin")]
          Argument::value("plugin-root", "PATH", "Absolute path to a directory that will become root filesystem for the plugin process."),
          #[cfg(feature = "plugin")]
          Argument::value("plugin-mount", "PATH:PATH:BOOL", "Path to be mounted into the plugin's root filesystem.  Can be given more than once."),
          #[cfg(feature = "plugin")]
          Argument::value("plugin-mount-file", "PATH", "Path to the file listing paths be mounted into the plugin's root filesystem.  Can be given more than once."),
          #[cfg(feature = "plugin")]
          Argument::value("plugin-gid-map", "GID:GID:INT", "Supplemental GIDs that should be mapped in plugin jail.  Can be given more than once."),
          #[cfg(feature = "plugin")]
          Argument::value("plugin-gid-map-file", "PATH", "Path to the file listing supplemental GIDs that should be mapped in plugin jail.  Can be given more than once."),
          Argument::flag("vhost-net", "Use vhost for networking."),
          Argument::value("tap-fd",
                          "fd",
                          "File descriptor for configured tap device. A different virtual network card will be added each time this argument is given."),
          #[cfg(feature = "gpu")]
          Argument::flag_or_value("gpu",
                                  "[width=INT,height=INT]",
                                  "(EXPERIMENTAL) Comma separated key=value pairs for setting up a virtio-gpu device
                                  Possible key values:
                                  backend=(2d|3d|gfxstream) - Which backend to use for virtio-gpu (determining rendering protocol)
                                  width=INT - The width of the virtual display connected to the virtio-gpu.
                                  height=INT - The height of the virtual display connected to the virtio-gpu.
                                  egl[=true|=false] - If the virtio-gpu backend should use a EGL context for rendering.
                                  glx[=true|=false] - If the virtio-gpu backend should use a GLX context for rendering.
                                  surfaceless[=true|=false] - If the virtio-gpu backend should use a surfaceless context for rendering.
                                  "),
          #[cfg(feature = "tpm")]
          Argument::flag("software-tpm", "enable a software emulated trusted platform module device"),
          Argument::value("evdev", "PATH", "Path to an event device node. The device will be grabbed (unusable from the host) and made available to the guest with the same configuration it shows on the host"),
          Argument::value("single-touch", "PATH:WIDTH:HEIGHT", "Path to a socket from where to read single touch input events (such as those from a touchscreen) and write status updates to, optionally followed by width and height (defaults to 800x1280)."),
          Argument::value("trackpad", "PATH:WIDTH:HEIGHT", "Path to a socket from where to read trackpad input events and write status updates to, optionally followed by screen width and height (defaults to 800x1280)."),
          Argument::value("mouse", "PATH", "Path to a socket from where to read mouse input events and write status updates to."),
          Argument::value("keyboard", "PATH", "Path to a socket from where to read keyboard input events and write status updates to."),
          #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
          Argument::flag("split-irqchip", "(EXPERIMENTAL) enable split-irqchip support"),
          Argument::value("bios", "PATH", "Path to BIOS/firmware ROM"),
          Argument::value("vfio", "PATH", "Path to sysfs of pass through or mdev device"),
          Argument::short_flag('h', "help", "Print help message.")];

    let mut cfg = Config::default();
    let match_res = set_arguments(args, &arguments[..], |name, value| {
        set_argument(&mut cfg, name, value)
    })
    .and_then(|_| validate_arguments(&mut cfg));

    match match_res {
        #[cfg(feature = "plugin")]
        Ok(()) if executable_is_plugin(&cfg.executable_path) => {
            match crosvm::plugin::run_config(cfg) {
                Ok(_) => {
                    info!("crosvm and plugin have exited normally");
                    Ok(())
                }
                Err(e) => {
                    error!("{}", e);
                    Err(())
                }
            }
        }
        Ok(()) => match linux::run_config(cfg) {
            Ok(_) => {
                info!("crosvm has exited normally");
                Ok(())
            }
            Err(e) => {
                error!("{}", e);
                Err(())
            }
        },
        Err(argument::Error::PrintHelp) => {
            print_help("crosvm run", "KERNEL", &arguments[..]);
            Ok(())
        }
        Err(e) => {
            error!("{}", e);
            Err(())
        }
    }
}

fn handle_request(
    request: &VmRequest,
    args: std::env::Args,
) -> std::result::Result<VmResponse, ()> {
    let mut return_result = Err(());
    for socket_path in args {
        match UnixSeqpacket::connect(&socket_path) {
            Ok(s) => {
                let socket: VmControlRequestSocket = MsgSocket::new(s);
                if let Err(e) = socket.send(request) {
                    error!(
                        "failed to send request to socket at '{}': {}",
                        socket_path, e
                    );
                    return_result = Err(());
                    continue;
                }
                match socket.recv() {
                    Ok(response) => return_result = Ok(response),
                    Err(e) => {
                        error!(
                            "failed to send request to socket at2 '{}': {}",
                            socket_path, e
                        );
                        return_result = Err(());
                        continue;
                    }
                }
            }
            Err(e) => {
                error!("failed to connect to socket at '{}': {}", socket_path, e);
                return_result = Err(());
            }
        }
    }

    return_result
}

fn vms_request(request: &VmRequest, args: std::env::Args) -> std::result::Result<(), ()> {
    let response = handle_request(request, args)?;
    info!("request response was {}", response);
    Ok(())
}

fn stop_vms(args: std::env::Args) -> std::result::Result<(), ()> {
    if args.len() == 0 {
        print_help("crosvm stop", "VM_SOCKET...", &[]);
        println!("Stops the crosvm instance listening on each `VM_SOCKET` given.");
        return Err(());
    }
    vms_request(&VmRequest::Exit, args)
}

fn suspend_vms(args: std::env::Args) -> std::result::Result<(), ()> {
    if args.len() == 0 {
        print_help("crosvm suspend", "VM_SOCKET...", &[]);
        println!("Suspends the crosvm instance listening on each `VM_SOCKET` given.");
        return Err(());
    }
    vms_request(&VmRequest::Suspend, args)
}

fn resume_vms(args: std::env::Args) -> std::result::Result<(), ()> {
    if args.len() == 0 {
        print_help("crosvm resume", "VM_SOCKET...", &[]);
        println!("Resumes the crosvm instance listening on each `VM_SOCKET` given.");
        return Err(());
    }
    vms_request(&VmRequest::Resume, args)
}

fn balloon_vms(mut args: std::env::Args) -> std::result::Result<(), ()> {
    if args.len() < 2 {
        print_help("crosvm balloon", "SIZE VM_SOCKET...", &[]);
        println!("Set the ballon size of the crosvm instance to `SIZE` bytes.");
        return Err(());
    }
    let num_bytes = match args.next().unwrap().parse::<u64>() {
        Ok(n) => n,
        Err(_) => {
            error!("Failed to parse number of bytes");
            return Err(());
        }
    };

    let command = BalloonControlCommand::Adjust { num_bytes };
    vms_request(&VmRequest::BalloonCommand(command), args)
}

fn balloon_stats(args: std::env::Args) -> std::result::Result<(), ()> {
    if args.len() != 1 {
        print_help("crosvm balloon_stats", "VM_SOCKET", &[]);
        println!("Prints virtio balloon statistics for a `VM_SOCKET`.");
        return Err(());
    }
    let command = BalloonControlCommand::Stats {};
    let request = &VmRequest::BalloonCommand(command);
    let response = handle_request(request, args)?;
    println!("{}", response);
    Ok(())
}

fn create_qcow2(args: std::env::Args) -> std::result::Result<(), ()> {
    let arguments = [
        Argument::positional("PATH", "where to create the qcow2 image"),
        Argument::positional("[SIZE]", "the expanded size of the image"),
        Argument::value(
            "backing_file",
            "path/to/file",
            " the file to back the image",
        ),
    ];
    let mut positional_index = 0;
    let mut file_path = String::from("");
    let mut size: Option<u64> = None;
    let mut backing_file: Option<String> = None;
    set_arguments(args, &arguments[..], |name, value| {
        match (name, positional_index) {
            ("", 0) => {
                // NAME
                positional_index += 1;
                file_path = value.unwrap().to_owned();
            }
            ("", 1) => {
                // [SIZE]
                positional_index += 1;
                size = Some(value.unwrap().parse::<u64>().map_err(|_| {
                    argument::Error::InvalidValue {
                        value: value.unwrap().to_owned(),
                        expected: String::from("SIZE should be a nonnegative integer"),
                    }
                })?);
            }
            ("", _) => {
                return Err(argument::Error::TooManyArguments(
                    "Expected at most 2 positional arguments".to_owned(),
                ));
            }
            ("backing_file", _) => {
                backing_file = value.map(|x| x.to_owned());
            }
            _ => unreachable!(),
        };
        Ok(())
    })
    .map_err(|e| {
        error!("Unable to parse command line arguments: {}", e);
    })?;
    if file_path.is_empty() || !(size.is_some() ^ backing_file.is_some()) {
        print_help("crosvm create_qcow2", "PATH [SIZE]", &arguments);
        println!(
            "Create a new QCOW2 image at `PATH` of either the specified `SIZE` in bytes or
with a '--backing_file'."
        );
        return Err(());
    }

    let file = OpenOptions::new()
        .create(true)
        .read(true)
        .write(true)
        .truncate(true)
        .open(&file_path)
        .map_err(|e| {
            error!("Failed opening qcow file at '{}': {}", file_path, e);
        })?;

    match (size, backing_file) {
        (Some(size), None) => QcowFile::new(file, size).map_err(|e| {
            error!("Failed to create qcow file at '{}': {}", file_path, e);
        })?,
        (None, Some(backing_file)) => {
            QcowFile::new_from_backing(file, &backing_file).map_err(|e| {
                error!("Failed to create qcow file at '{}': {}", file_path, e);
            })?
        }
        _ => unreachable!(),
    };
    Ok(())
}

fn disk_cmd(mut args: std::env::Args) -> std::result::Result<(), ()> {
    if args.len() < 2 {
        print_help("crosvm disk", "SUBCOMMAND VM_SOCKET...", &[]);
        println!("Manage attached virtual disk devices.");
        println!("Subcommands:");
        println!("  resize DISK_INDEX NEW_SIZE VM_SOCKET");
        return Err(());
    }
    let subcommand: &str = &args.next().unwrap();

    let request = match subcommand {
        "resize" => {
            let disk_index = match args.next().unwrap().parse::<usize>() {
                Ok(n) => n,
                Err(_) => {
                    error!("Failed to parse disk index");
                    return Err(());
                }
            };

            let new_size = match args.next().unwrap().parse::<u64>() {
                Ok(n) => n,
                Err(_) => {
                    error!("Failed to parse disk size");
                    return Err(());
                }
            };

            VmRequest::DiskCommand {
                disk_index,
                command: DiskControlCommand::Resize { new_size },
            }
        }
        _ => {
            error!("Unknown disk subcommand '{}'", subcommand);
            return Err(());
        }
    };

    vms_request(&request, args)
}

enum ModifyUsbError {
    ArgMissing(&'static str),
    ArgParse(&'static str, String),
    ArgParseInt(&'static str, String, ParseIntError),
    FailedFdValidate(sys_util::Error),
    PathDoesNotExist(PathBuf),
    SocketFailed,
    UnexpectedResponse(VmResponse),
    UnknownCommand(String),
    UsbControl(UsbControlResult),
}

impl fmt::Display for ModifyUsbError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::ModifyUsbError::*;

        match self {
            ArgMissing(a) => write!(f, "argument missing: {}", a),
            ArgParse(name, value) => {
                write!(f, "failed to parse argument {} value `{}`", name, value)
            }
            ArgParseInt(name, value, e) => write!(
                f,
                "failed to parse integer argument {} value `{}`: {}",
                name, value, e
            ),
            FailedFdValidate(e) => write!(f, "failed to validate file descriptor: {}", e),
            PathDoesNotExist(p) => write!(f, "path `{}` does not exist", p.display()),
            SocketFailed => write!(f, "socket failed"),
            UnexpectedResponse(r) => write!(f, "unexpected response: {}", r),
            UnknownCommand(c) => write!(f, "unknown command: `{}`", c),
            UsbControl(e) => write!(f, "{}", e),
        }
    }
}

type ModifyUsbResult<T> = std::result::Result<T, ModifyUsbError>;

fn parse_bus_id_addr(v: &str) -> ModifyUsbResult<(u8, u8, u16, u16)> {
    debug!("parse_bus_id_addr: {}", v);
    let mut ids = v.split(':');
    match (ids.next(), ids.next(), ids.next(), ids.next()) {
        (Some(bus_id), Some(addr), Some(vid), Some(pid)) => {
            let bus_id = bus_id
                .parse::<u8>()
                .map_err(|e| ModifyUsbError::ArgParseInt("bus_id", bus_id.to_owned(), e))?;
            let addr = addr
                .parse::<u8>()
                .map_err(|e| ModifyUsbError::ArgParseInt("addr", addr.to_owned(), e))?;
            let vid = u16::from_str_radix(&vid, 16)
                .map_err(|e| ModifyUsbError::ArgParseInt("vid", vid.to_owned(), e))?;
            let pid = u16::from_str_radix(&pid, 16)
                .map_err(|e| ModifyUsbError::ArgParseInt("pid", pid.to_owned(), e))?;
            Ok((bus_id, addr, vid, pid))
        }
        _ => Err(ModifyUsbError::ArgParse(
            "BUS_ID_ADDR_BUS_NUM_DEV_NUM",
            v.to_owned(),
        )),
    }
}

fn raw_fd_from_path(path: &Path) -> ModifyUsbResult<RawFd> {
    if !path.exists() {
        return Err(ModifyUsbError::PathDoesNotExist(path.to_owned()));
    }
    let raw_fd = path
        .file_name()
        .and_then(|fd_osstr| fd_osstr.to_str())
        .map_or(
            Err(ModifyUsbError::ArgParse(
                "USB_DEVICE_PATH",
                path.to_string_lossy().into_owned(),
            )),
            |fd_str| {
                fd_str.parse::<libc::c_int>().map_err(|e| {
                    ModifyUsbError::ArgParseInt("USB_DEVICE_PATH", fd_str.to_owned(), e)
                })
            },
        )?;
    validate_raw_fd(raw_fd).map_err(ModifyUsbError::FailedFdValidate)
}

fn usb_attach(mut args: std::env::Args) -> ModifyUsbResult<UsbControlResult> {
    let val = args
        .next()
        .ok_or(ModifyUsbError::ArgMissing("BUS_ID_ADDR_BUS_NUM_DEV_NUM"))?;
    let (bus, addr, vid, pid) = parse_bus_id_addr(&val)?;
    let dev_path = PathBuf::from(
        args.next()
            .ok_or(ModifyUsbError::ArgMissing("usb device path"))?,
    );
    let usb_file: Option<File> = if dev_path == Path::new("-") {
        None
    } else if dev_path.parent() == Some(Path::new("/proc/self/fd")) {
        // Special case '/proc/self/fd/*' paths. The FD is already open, just use it.
        // Safe because we will validate |raw_fd|.
        Some(unsafe { File::from_raw_fd(raw_fd_from_path(&dev_path)?) })
    } else {
        Some(
            OpenOptions::new()
                .read(true)
                .write(true)
                .open(&dev_path)
                .map_err(|_| ModifyUsbError::UsbControl(UsbControlResult::FailedToOpenDevice))?,
        )
    };

    let request = VmRequest::UsbCommand(UsbControlCommand::AttachDevice {
        bus,
        addr,
        vid,
        pid,
        fd: usb_file.map(MaybeOwnedFd::Owned),
    });
    let response = handle_request(&request, args).map_err(|_| ModifyUsbError::SocketFailed)?;
    match response {
        VmResponse::UsbResponse(usb_resp) => Ok(usb_resp),
        r => Err(ModifyUsbError::UnexpectedResponse(r)),
    }
}

fn usb_detach(mut args: std::env::Args) -> ModifyUsbResult<UsbControlResult> {
    let port: u8 = args
        .next()
        .map_or(Err(ModifyUsbError::ArgMissing("PORT")), |p| {
            p.parse::<u8>()
                .map_err(|e| ModifyUsbError::ArgParseInt("PORT", p.to_owned(), e))
        })?;
    let request = VmRequest::UsbCommand(UsbControlCommand::DetachDevice { port });
    let response = handle_request(&request, args).map_err(|_| ModifyUsbError::SocketFailed)?;
    match response {
        VmResponse::UsbResponse(usb_resp) => Ok(usb_resp),
        r => Err(ModifyUsbError::UnexpectedResponse(r)),
    }
}

fn usb_list(args: std::env::Args) -> ModifyUsbResult<UsbControlResult> {
    let mut ports: [u8; USB_CONTROL_MAX_PORTS] = Default::default();
    for (index, port) in ports.iter_mut().enumerate() {
        *port = index as u8
    }
    let request = VmRequest::UsbCommand(UsbControlCommand::ListDevice { ports });
    let response = handle_request(&request, args).map_err(|_| ModifyUsbError::SocketFailed)?;
    match response {
        VmResponse::UsbResponse(usb_resp) => Ok(usb_resp),
        r => Err(ModifyUsbError::UnexpectedResponse(r)),
    }
}

fn modify_usb(mut args: std::env::Args) -> std::result::Result<(), ()> {
    if args.len() < 2 {
        print_help("crosvm usb",
                   "[attach BUS_ID:ADDR:VENDOR_ID:PRODUCT_ID [USB_DEVICE_PATH|-] | detach PORT | list] VM_SOCKET...", &[]);
        return Err(());
    }

    // This unwrap will not panic because of the above length check.
    let command = args.next().unwrap();
    let result = match command.as_ref() {
        "attach" => usb_attach(args),
        "detach" => usb_detach(args),
        "list" => usb_list(args),
        other => Err(ModifyUsbError::UnknownCommand(other.to_owned())),
    };
    match result {
        Ok(response) => {
            println!("{}", response);
            Ok(())
        }
        Err(e) => {
            println!("error {}", e);
            Err(())
        }
    }
}

fn print_usage() {
    print_help("crosvm", "[stop|run]", &[]);
    println!("Commands:");
    println!("    stop - Stops crosvm instances via their control sockets.");
    println!("    run  - Start a new crosvm instance.");
    println!("    create_qcow2  - Create a new qcow2 disk image file.");
    println!("    disk - Manage attached virtual disk devices.");
    println!("    usb - Manage attached virtual USB devices.");
    println!("    version - Show package version.");
}

fn pkg_version() -> std::result::Result<(), ()> {
    const VERSION: Option<&'static str> = option_env!("CARGO_PKG_VERSION");
    const PKG_VERSION: Option<&'static str> = option_env!("PKG_VERSION");

    print!("crosvm {}", VERSION.unwrap_or("UNKNOWN"));
    match PKG_VERSION {
        Some(v) => println!("-{}", v),
        None => println!(),
    }
    Ok(())
}

fn crosvm_main() -> std::result::Result<(), ()> {
    if let Err(e) = syslog::init() {
        println!("failed to initialize syslog: {}", e);
        return Err(());
    }

    panic_hook::set_panic_hook();

    let mut args = std::env::args();
    if args.next().is_none() {
        error!("expected executable name");
        return Err(());
    }

    // Past this point, usage of exit is in danger of leaking zombie processes.
    let ret = match args.next().as_ref().map(|a| a.as_ref()) {
        None => {
            print_usage();
            Ok(())
        }
        Some("stop") => stop_vms(args),
        Some("suspend") => suspend_vms(args),
        Some("resume") => resume_vms(args),
        Some("run") => run_vm(args),
        Some("balloon") => balloon_vms(args),
        Some("balloon_stats") => balloon_stats(args),
        Some("create_qcow2") => create_qcow2(args),
        Some("disk") => disk_cmd(args),
        Some("usb") => modify_usb(args),
        Some("version") => pkg_version(),
        Some(c) => {
            println!("invalid subcommand: {:?}", c);
            print_usage();
            Err(())
        }
    };

    // Reap exit status from any child device processes. At this point, all devices should have been
    // dropped in the main process and told to shutdown. Try over a period of 100ms, since it may
    // take some time for the processes to shut down.
    if !wait_all_children() {
        // We gave them a chance, and it's too late.
        warn!("not all child processes have exited; sending SIGKILL");
        if let Err(e) = kill_process_group() {
            // We're now at the mercy of the OS to clean up after us.
            warn!("unable to kill all child processes: {}", e);
        }
    }

    // WARNING: Any code added after this point is not guaranteed to run
    // since we may forcibly kill this process (and its children) above.
    ret
}

fn main() {
    std::process::exit(if crosvm_main().is_ok() { 0 } else { 1 });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crosvm::{DEFAULT_TOUCH_DEVICE_HEIGHT, DEFAULT_TOUCH_DEVICE_WIDTH};

    #[test]
    fn parse_cpu_set_single() {
        assert_eq!(parse_cpu_set("123").expect("parse failed"), vec![123]);
    }

    #[test]
    fn parse_cpu_set_list() {
        assert_eq!(
            parse_cpu_set("0,1,2,3").expect("parse failed"),
            vec![0, 1, 2, 3]
        );
    }

    #[test]
    fn parse_cpu_set_range() {
        assert_eq!(
            parse_cpu_set("0-3").expect("parse failed"),
            vec![0, 1, 2, 3]
        );
    }

    #[test]
    fn parse_cpu_set_list_of_ranges() {
        assert_eq!(
            parse_cpu_set("3-4,7-9,18").expect("parse failed"),
            vec![3, 4, 7, 8, 9, 18]
        );
    }

    #[test]
    fn parse_cpu_set_repeated() {
        // For now, allow duplicates - they will be handled gracefully by the vec to cpu_set_t conversion.
        assert_eq!(parse_cpu_set("1,1,1").expect("parse failed"), vec![1, 1, 1]);
    }

    #[test]
    fn parse_cpu_set_negative() {
        // Negative CPU numbers are not allowed.
        parse_cpu_set("-3").expect_err("parse should have failed");
    }

    #[test]
    fn parse_cpu_set_reverse_range() {
        // Ranges must be from low to high.
        parse_cpu_set("5-2").expect_err("parse should have failed");
    }

    #[test]
    fn parse_cpu_set_open_range() {
        parse_cpu_set("3-").expect_err("parse should have failed");
    }

    #[test]
    fn parse_cpu_set_extra_comma() {
        parse_cpu_set("0,1,2,").expect_err("parse should have failed");
    }

    #[test]
    fn parse_ac97_vaild() {
        parse_ac97_options("backend=cras").expect("parse should have succeded");
    }

    #[test]
    fn parse_ac97_null_vaild() {
        parse_ac97_options("backend=null").expect("parse should have succeded");
    }

    #[test]
    fn parse_ac97_dup_effect_vaild() {
        parse_ac97_options("backend=cras,capture=true,capture_effects=aec|aec")
            .expect("parse should have succeded");
    }

    #[test]
    fn parse_ac97_effect_invaild() {
        parse_ac97_options("backend=cras,capture=true,capture_effects=abc")
            .expect_err("parse should have failed");
    }

    #[test]
    fn parse_ac97_effect_vaild() {
        parse_ac97_options("backend=cras,capture=true,capture_effects=aec")
            .expect("parse should have succeded");
    }

    #[test]
    fn parse_serial_vaild() {
        parse_serial_options("type=syslog,num=1,console=true,stdin=true")
            .expect("parse should have succeded");
    }

    #[test]
    fn parse_serial_valid_no_num() {
        parse_serial_options("type=syslog").expect("parse should have succeded");
    }

    #[test]
    fn parse_serial_invalid_type() {
        parse_serial_options("type=wormhole,num=1").expect_err("parse should have failed");
    }

    #[test]
    fn parse_serial_invalid_num_upper() {
        parse_serial_options("type=syslog,num=5").expect_err("parse should have failed");
    }

    #[test]
    fn parse_serial_invalid_num_lower() {
        parse_serial_options("type=syslog,num=0").expect_err("parse should have failed");
    }

    #[test]
    fn parse_serial_invalid_num_string() {
        parse_serial_options("type=syslog,num=number3").expect_err("parse should have failed");
    }

    #[test]
    fn parse_serial_invalid_option() {
        parse_serial_options("type=syslog,speed=lightspeed").expect_err("parse should have failed");
    }

    #[test]
    fn parse_serial_invalid_two_stdin() {
        let mut config = Config::default();
        set_argument(&mut config, "serial", Some("num=1,type=stdout,stdin=true"))
            .expect("should parse the first serial argument");
        set_argument(&mut config, "serial", Some("num=2,type=stdout,stdin=true"))
            .expect_err("should fail to parse a second serial port connected to stdin");
    }

    #[test]
    fn parse_plugin_mount_valid() {
        let mut config = Config::default();
        set_argument(
            &mut config,
            "plugin-mount",
            Some("/dev/null:/dev/zero:true"),
        )
        .expect("parse should succeed");
        assert_eq!(config.plugin_mounts[0].src, PathBuf::from("/dev/null"));
        assert_eq!(config.plugin_mounts[0].dst, PathBuf::from("/dev/zero"));
        assert_eq!(config.plugin_mounts[0].writable, true);
    }

    #[test]
    fn parse_plugin_mount_valid_shorthand() {
        let mut config = Config::default();
        set_argument(&mut config, "plugin-mount", Some("/dev/null")).expect("parse should succeed");
        assert_eq!(config.plugin_mounts[0].dst, PathBuf::from("/dev/null"));
        assert_eq!(config.plugin_mounts[0].writable, false);
        set_argument(&mut config, "plugin-mount", Some("/dev/null:/dev/zero"))
            .expect("parse should succeed");
        assert_eq!(config.plugin_mounts[1].dst, PathBuf::from("/dev/zero"));
        assert_eq!(config.plugin_mounts[1].writable, false);
        set_argument(&mut config, "plugin-mount", Some("/dev/null::true"))
            .expect("parse should succeed");
        assert_eq!(config.plugin_mounts[2].dst, PathBuf::from("/dev/null"));
        assert_eq!(config.plugin_mounts[2].writable, true);
    }

    #[test]
    fn parse_plugin_mount_invalid() {
        let mut config = Config::default();
        set_argument(&mut config, "plugin-mount", Some("")).expect_err("parse should fail");
        set_argument(
            &mut config,
            "plugin-mount",
            Some("/dev/null:/dev/null:true:false"),
        )
        .expect_err("parse should fail because too many arguments");
        set_argument(&mut config, "plugin-mount", Some("null:/dev/null:true"))
            .expect_err("parse should fail because source is not absolute");
        set_argument(&mut config, "plugin-mount", Some("/dev/null:null:true"))
            .expect_err("parse should fail because source is not absolute");
        set_argument(&mut config, "plugin-mount", Some("/dev/null:null:blah"))
            .expect_err("parse should fail because flag is not boolean");
    }

    #[test]
    fn parse_plugin_gid_map_valid() {
        let mut config = Config::default();
        set_argument(&mut config, "plugin-gid-map", Some("1:2:3")).expect("parse should succeed");
        assert_eq!(config.plugin_gid_maps[0].inner, 1);
        assert_eq!(config.plugin_gid_maps[0].outer, 2);
        assert_eq!(config.plugin_gid_maps[0].count, 3);
    }

    #[test]
    fn parse_plugin_gid_map_valid_shorthand() {
        let mut config = Config::default();
        set_argument(&mut config, "plugin-gid-map", Some("1")).expect("parse should succeed");
        assert_eq!(config.plugin_gid_maps[0].inner, 1);
        assert_eq!(config.plugin_gid_maps[0].outer, 1);
        assert_eq!(config.plugin_gid_maps[0].count, 1);
        set_argument(&mut config, "plugin-gid-map", Some("1:2")).expect("parse should succeed");
        assert_eq!(config.plugin_gid_maps[1].inner, 1);
        assert_eq!(config.plugin_gid_maps[1].outer, 2);
        assert_eq!(config.plugin_gid_maps[1].count, 1);
        set_argument(&mut config, "plugin-gid-map", Some("1::3")).expect("parse should succeed");
        assert_eq!(config.plugin_gid_maps[2].inner, 1);
        assert_eq!(config.plugin_gid_maps[2].outer, 1);
        assert_eq!(config.plugin_gid_maps[2].count, 3);
    }

    #[test]
    fn parse_plugin_gid_map_invalid() {
        let mut config = Config::default();
        set_argument(&mut config, "plugin-gid-map", Some("")).expect_err("parse should fail");
        set_argument(&mut config, "plugin-gid-map", Some("1:2:3:4"))
            .expect_err("parse should fail because too many arguments");
        set_argument(&mut config, "plugin-gid-map", Some("blah:2:3"))
            .expect_err("parse should fail because inner is not a number");
        set_argument(&mut config, "plugin-gid-map", Some("1:blah:3"))
            .expect_err("parse should fail because outer is not a number");
        set_argument(&mut config, "plugin-gid-map", Some("1:2:blah"))
            .expect_err("parse should fail because count is not a number");
    }

    #[test]
    fn single_touch_spec_and_track_pad_spec_default_size() {
        let mut config = Config::default();
        config
            .executable_path
            .replace(Executable::Kernel(PathBuf::from("kernel")));
        set_argument(&mut config, "single-touch", Some("/dev/single-touch-test")).unwrap();
        set_argument(&mut config, "trackpad", Some("/dev/single-touch-test")).unwrap();
        validate_arguments(&mut config).unwrap();
        assert_eq!(
            config.virtio_single_touch.unwrap().get_size(),
            (DEFAULT_TOUCH_DEVICE_WIDTH, DEFAULT_TOUCH_DEVICE_HEIGHT)
        );
        assert_eq!(
            config.virtio_trackpad.unwrap().get_size(),
            (DEFAULT_TOUCH_DEVICE_WIDTH, DEFAULT_TOUCH_DEVICE_HEIGHT)
        );
    }

    #[cfg(feature = "gpu")]
    #[test]
    fn single_touch_spec_default_size_from_gpu() {
        let width = 12345u32;
        let height = 54321u32;
        let mut config = Config::default();
        config
            .executable_path
            .replace(Executable::Kernel(PathBuf::from("kernel")));
        set_argument(&mut config, "single-touch", Some("/dev/single-touch-test")).unwrap();
        set_argument(
            &mut config,
            "gpu",
            Some(&format!("width={},height={}", width, height)),
        )
        .unwrap();
        validate_arguments(&mut config).unwrap();
        assert_eq!(
            config.virtio_single_touch.unwrap().get_size(),
            (width, height)
        );
    }

    #[test]
    fn single_touch_spec_and_track_pad_spec_with_size() {
        let width = 12345u32;
        let height = 54321u32;
        let mut config = Config::default();
        config
            .executable_path
            .replace(Executable::Kernel(PathBuf::from("kernel")));
        set_argument(
            &mut config,
            "single-touch",
            Some(&format!("/dev/single-touch-test:{}:{}", width, height)),
        )
        .unwrap();
        set_argument(
            &mut config,
            "trackpad",
            Some(&format!("/dev/single-touch-test:{}:{}", width, height)),
        )
        .unwrap();
        validate_arguments(&mut config).unwrap();
        assert_eq!(
            config.virtio_single_touch.unwrap().get_size(),
            (width, height)
        );
        assert_eq!(config.virtio_trackpad.unwrap().get_size(), (width, height));
    }

    #[cfg(feature = "gpu")]
    #[test]
    fn single_touch_spec_with_size_independent_from_gpu() {
        let touch_width = 12345u32;
        let touch_height = 54321u32;
        let display_width = 1234u32;
        let display_height = 5432u32;
        let mut config = Config::default();
        config
            .executable_path
            .replace(Executable::Kernel(PathBuf::from("kernel")));
        set_argument(
            &mut config,
            "single-touch",
            Some(&format!(
                "/dev/single-touch-test:{}:{}",
                touch_width, touch_height
            )),
        )
        .unwrap();
        set_argument(
            &mut config,
            "gpu",
            Some(&format!(
                "width={},height={}",
                display_width, display_height
            )),
        )
        .unwrap();
        validate_arguments(&mut config).unwrap();
        assert_eq!(
            config.virtio_single_touch.unwrap().get_size(),
            (touch_width, touch_height)
        );
    }
}
