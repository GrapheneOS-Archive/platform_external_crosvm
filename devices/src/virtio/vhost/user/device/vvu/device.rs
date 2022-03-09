// Copyright 2021 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

//! Implement a struct that works as a `vmm_vhost`'s backend.

use std::fs::File;
use std::io::{IoSlice, IoSliceMut};
use std::mem;
use std::os::unix::io::RawFd;
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::Arc;
use std::thread;

use anyhow::{bail, Context, Result};
use base::{error, Event};
use cros_async::{EventAsync, Executor};
use futures::{pin_mut, select, FutureExt};
use sync::Mutex;
use vmm_vhost::connection::vfio::Device as VfioDeviceTrait;

use crate::vfio::VfioDevice;
use crate::virtio::vhost::user::device::vvu::{
    pci::{QueueNotifier, QueueType, VvuPciDevice},
    queue::UserQueue,
};

async fn process_rxq(
    evt: EventAsync,
    mut rxq: UserQueue,
    rxq_sender: Sender<Vec<u8>>,
    rxq_evt: Event,
) -> Result<()> {
    loop {
        if let Err(e) = evt.next_val().await {
            error!("Failed to read the next queue event: {}", e);
            continue;
        }

        while let Some(slice) = rxq.read_data()? {
            let mut buf = vec![0; slice.size()];
            slice.copy_to(&mut buf);
            rxq_sender.send(buf)?;
            rxq_evt.write(1).context("process_rxq")?;
        }
    }
}

async fn process_txq(evt: EventAsync, txq: Arc<Mutex<UserQueue>>) -> Result<()> {
    loop {
        if let Err(e) = evt.next_val().await {
            error!("Failed to read the next queue event: {}", e);
            continue;
        }

        txq.lock().ack_used()?;
    }
}

fn run_worker(
    ex: Executor,
    rx_queue: UserQueue,
    rx_irq: Event,
    rx_sender: Sender<Vec<u8>>,
    rx_evt: Event,
    tx_queue: Arc<Mutex<UserQueue>>,
    tx_irq: Event,
) -> Result<()> {
    let rx_irq = EventAsync::new(rx_irq.0, &ex).context("failed to create async event")?;
    let rxq = process_rxq(rx_irq, rx_queue, rx_sender, rx_evt);
    pin_mut!(rxq);

    let tx_irq = EventAsync::new(tx_irq.0, &ex).context("failed to create async event")?;
    let txq = process_txq(tx_irq, Arc::clone(&tx_queue));
    pin_mut!(txq);

    let done = async {
        select! {
            res = rxq.fuse() => res.context("failed to handle rxq"),
            res = txq.fuse() => res.context("failed to handle txq"),
        }
    };

    match ex.run_until(done) {
        Ok(_) => Ok(()),
        Err(e) => {
            bail!("failed to process virtio-vhost-user queues: {}", e);
        }
    }
}

enum DeviceState {
    Initialized {
        // TODO(keiichiw): Update `VfioDeviceTrait::start()` to take `VvuPciDevice` so that we can
        // drop this field.
        device: Arc<Mutex<VvuPciDevice>>,
    },
    Running {
        vfio: Arc<VfioDevice>,

        rxq_notifier: Arc<Mutex<QueueNotifier>>,
        rxq_receiver: Receiver<Vec<u8>>,
        /// Store data that was provided by rxq_receiver but not consumed yet.
        rxq_buf: Vec<u8>,

        txq: Arc<Mutex<UserQueue>>,
        txq_notifier: Arc<Mutex<QueueNotifier>>,
    },
}

pub struct VvuDevice {
    state: DeviceState,
    rxq_evt: Event,
}

impl VvuDevice {
    pub fn new(device: Arc<Mutex<VvuPciDevice>>) -> Self {
        Self {
            state: DeviceState::Initialized { device },
            rxq_evt: Event::new().expect("failed to create VvuDevice's rxq_evt"),
        }
    }
}

impl VfioDeviceTrait for VvuDevice {
    fn event(&self) -> &sys_util::EventFd {
        &self.rxq_evt.0
    }

    fn start(&mut self) -> Result<()> {
        let device = match &self.state {
            DeviceState::Initialized { device } => Arc::clone(device),
            DeviceState::Running { .. } => {
                bail!("VvuDevice has already started");
            }
        };
        let ex = Executor::new().expect("Failed to create an executor");

        let mut dev = device.lock();
        let mut irqs = mem::take(&mut dev.irqs);
        let mut queues = mem::take(&mut dev.queues);
        let mut queue_notifiers = mem::take(&mut dev.queue_notifiers);
        let vfio = Arc::clone(&dev.vfio_dev);
        drop(dev);

        let rxq = queues.remove(0);
        let rxq_irq = irqs.remove(0);
        let rxq_notifier = Arc::new(Mutex::new(queue_notifiers.remove(0)));
        // TODO: Can we use async channel instead so we don't need `rxq_evt`?
        let (rxq_sender, rxq_receiver) = channel();
        let rxq_evt = self.rxq_evt.try_clone().expect("rxq_evt clone");

        let txq = Arc::new(Mutex::new(queues.remove(0)));
        let txq_cloned = Arc::clone(&txq);
        let txq_irq = irqs.remove(0);
        let txq_notifier = Arc::new(Mutex::new(queue_notifiers.remove(0)));

        thread::Builder::new()
            .name("virtio-vhost-user driver".to_string())
            .spawn(move || {
                device.lock().start().expect("failed to start device");
                if let Err(e) =
                    run_worker(ex, rxq, rxq_irq, rxq_sender, rxq_evt, txq_cloned, txq_irq)
                {
                    error!("worker thread exited with error: {}", e);
                }
            })?;

        self.state = DeviceState::Running {
            vfio,
            rxq_notifier,
            rxq_receiver,
            rxq_buf: vec![],
            txq,
            txq_notifier,
        };

        Ok(())
    }

    fn send_bufs(&mut self, iovs: &[IoSlice], fds: Option<&[RawFd]>) -> Result<usize> {
        if fds.is_some() {
            bail!("cannot send FDs");
        }

        let (txq, txq_notifier, vfio) = match &mut self.state {
            DeviceState::Initialized { .. } => {
                bail!("VvuDevice hasn't started yet");
            }
            DeviceState::Running {
                vfio,
                txq,
                txq_notifier,
                ..
            } => (txq, txq_notifier, vfio),
        };

        let size = iovs.iter().map(|v| v.len()).sum();
        let data: Vec<u8> = iovs.iter().map(|v| v.to_vec()).flatten().collect();

        txq.lock().write(&data).context("Failed to send data")?;
        txq_notifier.lock().notify(vfio, QueueType::Tx as u16);

        Ok(size)
    }

    fn recv_into_bufs(&mut self, bufs: &mut [IoSliceMut]) -> Result<(usize, Option<Vec<File>>)> {
        let (rxq_receiver, rxq_notifier, rxq_buf, vfio) = match &mut self.state {
            DeviceState::Initialized { .. } => {
                bail!("VvuDevice hasn't started yet");
            }
            DeviceState::Running {
                rxq_receiver,
                rxq_notifier,
                rxq_buf,
                vfio,
                ..
            } => (rxq_receiver, rxq_notifier, rxq_buf, vfio),
        };

        let mut size = 0;
        for buf in bufs {
            let len = buf.len();

            while rxq_buf.len() < len {
                let mut data = rxq_receiver.recv().context("failed to receive data")?;
                rxq_buf.append(&mut data);
            }

            buf.clone_from_slice(&rxq_buf[..len]);

            rxq_buf.drain(0..len);
            size += len;

            rxq_notifier.lock().notify(vfio, QueueType::Rx as u16);
        }

        Ok((size, None))
    }
}
