// Copyright 2020 <盏一 w@hidva.com>
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::{syscall2rust, OwnedFd};
use crate::park::{Park, Unpark};
pub(crate) use kernel::*;
use libc::{c_long, c_void};
use parking_lot::lock_api::RawMutex as RawMutexTrait;
use parking_lot::{Mutex, RawMutex};
use std::collections::VecDeque;
use std::future::Future;
use std::mem::size_of;
use std::os::unix::prelude::{AsRawFd, FromRawFd};
use std::ptr::NonNull;
use std::sync::atomic::Ordering::{AcqRel, Acquire, Release, SeqCst};
use std::sync::atomic::{AtomicBool, AtomicU32};
use std::sync::Arc;
use std::task::{Context, Poll, Waker};
use std::time::Duration;

mod kernel;

#[derive(Debug)]
struct MmapGuard {
    mmap_ptr: NonNull<c_void>,
    mmap_sz: usize,
}

impl MmapGuard {
    fn new(p: NonNull<c_void>, s: usize) -> Self {
        Self {
            mmap_sz: s,
            mmap_ptr: p,
        }
    }
}

impl Drop for MmapGuard {
    fn drop(&mut self) {
        let _ = unsafe { libc::munmap(self.mmap_ptr.as_ptr(), self.mmap_sz) };
    }
}

#[derive(Debug)]
struct SqCq {
    // Sq
    sq_khead: NonNull<AtomicU32>,
    sq_ktail: NonNull<AtomicU32>,
    sq_kflags: NonNull<AtomicU32>,
    sq_array: NonNull<u32>,
    sqes_mmap: MmapGuard,

    #[cfg(debug_assertions)]
    sq_kdropped: NonNull<AtomicU32>,

    // Cq
    cq_khead: NonNull<AtomicU32>,
    cq_ktail: NonNull<AtomicU32>,
    cqes: NonNull<io_uring_cqe>,

    #[cfg(debug_assertions)]
    cq_koverflow: NonNull<AtomicU32>,

    // Common
    mask: u32,
    _sqcq_mmap: MmapGuard,
}

fn read<T: Copy>(p: NonNull<c_void>, off: u32) -> T {
    unsafe { std::ptr::read(offset(p, off).as_ptr()) }
}

fn offset<T>(p: NonNull<c_void>, off: u32) -> NonNull<T> {
    // size_of::<c_void> == 1!
    let np = unsafe { p.as_ptr().offset(off as isize) } as *mut T;
    debug_assert!(!np.is_null());
    unsafe { NonNull::new_unchecked(np) }
}

impl SqCq {
    #[cfg(debug_assertions)]
    fn sq_dropped(&self) -> u32 {
        unsafe { self.sq_kdropped.as_ref() }.load(SeqCst)
    }

    #[cfg(debug_assertions)]
    fn cq_overflow(&self) -> u32 {
        unsafe { self.cq_koverflow.as_ref() }.load(SeqCst)
    }

    fn new(fd: i32, p: &io_uring_params) -> std::io::Result<SqCq> {
        assert!((p.features & IORING_FEAT_SINGLE_MMAP) != 0);
        debug_assert_eq!(p.cq_entries, p.sq_entries);

        let sq_ring_sz = p.sq_off.array as usize + p.sq_entries as usize * size_of::<u32>();
        let cq_ring_sz = p.cq_off.cqes as usize + p.cq_entries as usize * size_of::<io_uring_cqe>();
        let mmap_sz = std::cmp::max(sq_ring_sz, cq_ring_sz);
        let sqcq_mmap = uring_mmap(fd, IORING_OFF_SQ_RING as i64, mmap_sz)?;
        let mmap_ptr = sqcq_mmap.mmap_ptr;

        debug_assert_eq!(
            read::<u32>(mmap_ptr, p.sq_off.ring_entries),
            read::<u32>(mmap_ptr, p.cq_off.ring_entries)
        );
        debug_assert_eq!(read::<u32>(mmap_ptr, p.sq_off.ring_entries), p.cq_entries);
        let mask: u32 = read(mmap_ptr, p.sq_off.ring_mask);
        debug_assert_eq!(mask, read(mmap_ptr, p.cq_off.ring_mask));

        let sqes_sz = p.sq_entries as usize * size_of::<io_uring_sqe>();
        return Ok(SqCq {
            // SQ
            sq_khead: offset(mmap_ptr, p.sq_off.head),
            sq_ktail: offset(mmap_ptr, p.sq_off.tail),
            sq_kflags: offset(mmap_ptr, p.sq_off.flags),

            #[cfg(debug_assertions)]
            sq_kdropped: offset(mmap_ptr, p.sq_off.dropped),

            sq_array: offset(mmap_ptr, p.sq_off.array),
            sqes_mmap: uring_mmap(fd, IORING_OFF_SQES as i64, sqes_sz)?,

            // CQ
            cq_khead: offset(mmap_ptr, p.cq_off.head),
            cq_ktail: offset(mmap_ptr, p.cq_off.tail),
            cqes: offset(mmap_ptr, p.cq_off.cqes),

            #[cfg(debug_assertions)]
            cq_koverflow: offset(mmap_ptr, p.cq_off.overflow),

            // Common
            mask,
            _sqcq_mmap: sqcq_mmap,
        });
    }
    // SAFETY: This function is only called by the thread responsible for modifying cq_khead.
    fn cq_head(&self) -> u32 {
        unsafe {
            let mutself = &mut *(self as *const Self as *mut Self);
            *mutself.cq_khead.as_mut().get_mut()
        }
    }

    fn cq_tail(&self) -> u32 {
        unsafe { self.cq_ktail.as_ref() }.load(Acquire)
    }

    // SAFETY: This function is only called by the thread responsible for modifying cq_khead.
    fn cq_is_empty(&self) -> bool {
        self.cq_head() >= self.cq_tail()
    }

    fn set_cq_head(&self, n: u32) {
        unsafe { self.cq_khead.as_ref() }.store(n, Release);
    }

    fn cqe_at(&self, idx: isize) -> io_uring_cqe {
        unsafe { *self.cqes.as_ptr().offset(idx) }
    }

    fn sq_flags(&self) -> u32 {
        // According to https://github.com/tokio-rs/tokio/issues/1768,
        // 这里使用 fetch_add(0, SeqCst) 来获取到 sq_flags 的最新值.
        unsafe { self.sq_kflags.as_ref() }.fetch_add(0, SeqCst)
    }

    fn need_wakeup(&self) -> bool {
        (self.sq_flags() & IORING_SQ_NEED_WAKEUP) != 0
    }

    fn set_sq_tail(&self, n: u32) {
        unsafe { self.sq_ktail.as_ref() }.store(n, Release);
    }

    fn sq_head(&self) -> u32 {
        return unsafe { self.sq_khead.as_ref() }.load(Acquire);
    }

    fn sq_tail(&self) -> u32 {
        // SAFETY#1:
        // All modifications to the sq_ktail occur in user mode,
        // and modifications will be serialized by sq_mux.
        unsafe {
            let mutself = &mut *(self as *const SqCq as *mut SqCq);
            *mutself.sq_ktail.as_mut().get_mut()
        }
    }

    fn set_sq_array_at(&self, tail: u32, v: u32) {
        // See SAFETY#1
        let idx = tail & self.mask;
        unsafe { *self.sq_array.as_ptr().offset(idx as isize) = v };
        return;
    }

    fn sq_size(&self) -> u32 {
        // 见 SAFETY#1, 这里我们没有使用 sq_mux 保护, 意味着我们拿到的 sqtail 可能不是
        // 最新值.
        // 意味着 sqtail < sqhead 可能成立, 即该函数可能会返回一个无意义的值, 但没关系,
        // 内核会帮我们兜底, 此时内核会 io_uring_enter() 会提交 sq buffer 中内核看到的
        // 所有 sqe,
        let sqtail = unsafe { self.sq_ktail.as_ref() }.load(Acquire);
        return sqtail - self.sq_head();
    }

    // ONLY USE IN DEBUG
    fn sqes_cap(&self) -> usize {
        return self.sqes_mmap.mmap_sz / size_of::<io_uring_sqe>();
    }

    fn sqes_ptr(&self) -> NonNull<io_uring_sqe> {
        return self.sqes_mmap.mmap_ptr.cast();
    }

    fn sqe_at(&self, idx: isize) -> &mut io_uring_sqe {
        debug_assert!(idx >= 0 && idx < self.sqes_cap() as isize);
        unsafe { &mut *self.sqes_ptr().as_ptr().offset(idx) }
    }
}

#[derive(Debug)]
struct Promise {
    res: Option<i32>,
    waker: Option<Waker>, // waker is None when discard is true!
    discard: bool,
}

impl Promise {
    fn do_set_value(&mut self, res: i32) {
        self.res = Some(res);
        if let Some(waker) = self.waker.take() {
            waker.wake();
        }
    }
}

// ONLY USE IN DEBUG
fn slot_check(slot: NonNull<PromiseSlot>) -> bool {
    unsafe {
        let p = &slot.as_ref().p;
        debug_assert!(!p.is_locked());
        let g = p.try_lock().unwrap();
        debug_assert!(g.waker.is_none());
        debug_assert!(!g.discard);
        debug_assert!(g.res.is_none());
    }
    return true;
}

impl Default for Promise {
    fn default() -> Self {
        Self {
            res: None,
            waker: None,
            discard: false,
        }
    }
}

#[derive(Debug)]
struct PromiseSlot {
    p: Mutex<Promise>,
    next: Option<NonNull<PromiseSlot>>,
}

impl Default for PromiseSlot {
    fn default() -> Self {
        PromiseSlot {
            p: Mutex::default(),
            next: None,
        }
    }
}

// shutdown = true, 则外界将无法再次获取到 PromiseSlot, 也无法挂载到 wait 上.
#[derive(Debug)]
struct FreeList {
    head: Option<NonNull<PromiseSlot>>,
    wait: VecDeque<Waker>,
    shutdown: bool,
}

impl FreeList {
    fn new(head: Option<NonNull<PromiseSlot>>) -> Self {
        Self {
            head,
            wait: VecDeque::new(),
            shutdown: false,
        }
    }

    fn shutdown(&mut self) {
        self.shutdown = true;
        while let Some(wait) = self.wait.pop_front() {
            wait.wake();
        }
    }

    fn mark_free(&mut self, mut slot: NonNull<PromiseSlot>) {
        debug_assert!(slot_check(slot));
        unsafe {
            slot.as_mut().next = self.head;
        }
        self.head = Some(slot);
        // 如果这里 shutdown = true, 则 self.wait 一定为空.
        if let Some(wait) = self.wait.pop_front() {
            wait.wake();
        }
    }

    // 若返回 is_shutdown = true, 则表明 io driver shutdown 了. 若为 false:
    // 若当前有空闲 slot, 则返回 Some, 此时忽略 waker.
    // 否则, 返回 None, 同时将 waker 保存在 wait 中.
    fn get_slot(
        &mut self,
        waker: &Waker,
    ) -> (bool /* is_shutdown */, Option<NonNull<PromiseSlot>>) {
        if self.shutdown {
            return (true, None);
        }
        if let Some(slot) = self.head {
            self.head = unsafe { slot.as_ref().next };
            return (false, Some(slot));
        } else {
            self.wait.push_back(waker.clone());
            return (false, None);
        };
    }
}

struct Inner {
    // sqe_push_lock just be used when adding a new sq entry.
    sqe_push_lock: RawMutex,
    sqcq: SqCq,
    slots: Vec<PromiseSlot>,
    free: Mutex<FreeList>,
    fd: OwnedFd,
    // 若 unparked = false, 则表明 unpark nop slot 并未在用.
    unparked: AtomicBool,
    // sqpoll = true, 意味着启用了 SQ_POLL.
    sqpoll: bool,
}

impl std::fmt::Debug for Inner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Inner")
            .field("sqcq", &self.sqcq)
            .field("slots", &self.slots)
            .field("free", &self.free)
            .field("fd", &self.fd)
            .field("unparked", &self.unparked)
            .finish()
    }
}

impl Inner {
    fn new(uring_entries: u32, uring_sq_thread_idle: Option<u32>) -> std::io::Result<Self> {
        let mut params = io_uring_params::zeroed();
        params.cq_entries = uring_entries;
        params.flags = IORING_SETUP_CQSIZE;
        if let Some(idle) = uring_sq_thread_idle {
            params.sq_thread_idle = idle;
            params.flags |= IORING_SETUP_SQPOLL;
        }
        let fd = io_uring_setup(uring_entries, &mut params)?;
        let sqcq = SqCq::new(fd.as_raw_fd(), &params)?;
        debug_assert!(params.sq_entries > 1);
        // Reserve a slot for Unpark.
        let (slots, free) = alloc_slots((params.sq_entries as usize) - 1);
        return Ok(Inner {
            sqe_push_lock: RawMutex::INIT,
            sqcq,
            slots,
            free: Mutex::new(FreeList::new(free)),
            fd,
            unparked: AtomicBool::new(false),
            sqpoll: uring_sq_thread_idle.is_some(),
        });
    }

    fn unpark_slot_idx(&self) -> u32 {
        return self.slots.len() as u32;
    }

    fn shutdown(&self) {
        self.free.lock().shutdown();
    }

    fn set_unparked(&self) -> bool {
        self.unparked
            .compare_exchange(false, true, AcqRel, Acquire)
            .is_ok()
    }

    fn unset_unparked(&self) {
        self.unparked
            .compare_exchange(true, false, AcqRel, Acquire)
            .expect("unset_unparked failed");
    }

    fn mark_free(&self, slot: NonNull<PromiseSlot>) {
        self.free.lock().mark_free(slot);
    }

    fn get_slot(&self, waker: &Waker) -> (bool, Option<NonNull<PromiseSlot>>) {
        self.free.lock().get_slot(waker)
    }

    fn slot_idx(&self, slot: NonNull<PromiseSlot>) -> u32 {
        let first = self.slots.as_ptr();
        let idx = unsafe { slot.as_ptr().offset_from(first) };
        debug_assert!(idx >= 0);
        debug_assert!(idx <= u32::MAX as isize);
        return idx as u32;
    }

    // 返回 Some 意味着提交成功. 返回 None 意味着当前没有空闲 slot, 此时会保存 waker 到
    // wait list 中, 并在有空闲 slot 时唤醒.
    fn submit(
        &self,
        usqe: &io_uring_sqe,
        waker: &Waker,
        enter: bool,
    ) -> (bool, Option<NonNull<PromiseSlot>>) {
        let slotres = self.get_slot(waker);
        if slotres.0 {
            return (true, None);
        }
        let slot = if let Some(slot) = slotres.1 {
            slot
        } else {
            return (false, None);
        };
        #[cfg(debug_assertions)]
        debug_assert!(slot_check(slot));
        debug_assert_eq!(size_of::<usize>(), size_of::<u64>());
        let idx = self.slot_idx(slot);
        let slotp = slot.as_ptr() as usize as u64;
        // See tagged_ptr_ptrcompression.hpp in boost
        debug_assert!(slotp <= ((1u64 << 48) - 1));
        self.do_submit(usqe, idx, slotp, enter);
        return (false, Some(slot));
    }

    fn poll(&self, slot: NonNull<PromiseSlot>, waker: &Waker) -> Poll<i32> {
        #[cfg(debug_assertions)]
        debug_assert_eq!(self.sqcq.sq_dropped(), 0);
        #[cfg(debug_assertions)]
        debug_assert_eq!(self.sqcq.cq_overflow(), 0);
        let mut p = unsafe { slot.as_ref() }.p.lock();
        // Inner::poll is only invoked in CQEFuture::poll, and discard is only set when CQEFuture is dropped.
        // So discard must be false here.
        debug_assert!(!p.discard);
        if let Some(res) = p.res {
            // At this point, promise.p.lock() will never be invoked in the poll thread.
            p.res = None;
            debug_assert!(p.waker.is_none());
            drop(p); // unlock

            self.mark_free(slot);
            return Poll::Ready(res);
        } else {
            if let Some(waker) = &p.waker {
                if !waker.will_wake(waker) {
                    p.waker = Some(waker.clone());
                }
            } else {
                p.waker = Some(waker.clone());
            }
            return Poll::Pending;
        }
    }

    fn do_submit(&self, usqe: &io_uring_sqe, idx: u32, ud: u64, enter: bool) {
        let sqe = self.sqcq.sqe_at(idx as isize);
        *sqe = *usqe;
        sqe.user_data |= ud;

        {
            self.sqe_push_lock.lock(); // REMEBER!!! UNLOCK
            let sq_tail = self.sqcq.sq_tail();
            debug_assert!(self.sqcq.sq_head() <= sq_tail);
            debug_assert!(sq_tail - self.sqcq.sq_head() < self.sqcq.sqes_cap() as u32);
            self.sqcq.set_sq_array_at(sq_tail, idx);
            self.sqcq.set_sq_tail(sq_tail + 1);
            unsafe { self.sqe_push_lock.unlock() }; // UNLOCK!!
        }

        if self.sqpoll {
            if self.sqcq.need_wakeup() {
                wakeup_sq_poll_thread(self.fd.as_raw_fd()).expect("wakeup sq poll thread failed");
            }
        } else if enter {
            // enter=true, 意味着需要将 sqes buffer 中所有 sqes 提交到内核,
            // 此时直接另 to_submit 等于 max 告诉内核提交所有 sqe.
            io_uring_enter(self.fd.as_raw_fd(), i32::MAX as i64, 0, None)
                .expect("do_submit.io_uring_enter failed");
        }
    }
}

unsafe impl Sync for Inner {}
unsafe impl Send for Inner {}

#[derive(Debug)]
pub(crate) struct Driver {
    inner: Arc<Inner>,
}

impl Driver {
    pub(crate) fn handle(&self) -> Handle {
        Handle {
            inner: self.inner.clone(),
        }
    }

    pub(crate) fn new(
        uring_entries: u32,
        uring_sq_thread_idle: Option<u32>,
    ) -> std::io::Result<Driver> {
        Inner::new(uring_entries, uring_sq_thread_idle).map(|v| Driver { inner: Arc::new(v) })
    }

    fn enter(&self, max_wait: Option<Duration>) -> std::io::Result<()> {
        // 如 sq_size() 注释所示, 此时 to_submit 可能大于 sq buffer 中实际 sqe 的数量.
        // 如 SYSCALL io_uring_enter 实现所示, 此时内核会忽略 GETEVENTS flag.
        // 意味着本轮 turn() 只是提交 sqe, 并未拿到任何 cqe,
        let to_submit = if self.inner.sqpoll {
            0
        } else {
            self.inner.sqcq.sq_size()
        } as i64;
        let flag = if self.inner.sqcq.cq_is_empty() {
            IORING_ENTER_GETEVENTS
        } else {
            0
        } as i64;
        let fd = self.inner.fd.as_raw_fd();
        let dur = max_wait.map(|v| duration_ts(v));
        let res = io_uring_enter(fd, to_submit, flag, dur.as_ref());
        if let Err(e) = res {
            if let Some(errno) = e.raw_os_error() {
                if errno == libc::ETIME || errno == libc::EINTR {
                    // 这些错误视为正常情况
                    return Ok(());
                }
            }
            return Err(e);
        }
        return Ok(());
    }

    fn turn(&mut self, max_wait: Option<Duration>) -> std::io::Result<()> {
        self.enter(max_wait)?;

        let mut cqhead = self.inner.sqcq.cq_head();
        while cqhead < self.inner.sqcq.cq_tail() {
            let cqe = self
                .inner
                .sqcq
                .cqe_at((cqhead & self.inner.sqcq.mask) as isize);
            cqhead += 1;
            self.inner.sqcq.set_cq_head(cqhead);

            let (cqflags, cqslot) = unpack(cqe.user_data);
            if cqflags != 0 {
                // Unpark
                self.inner.unset_unparked();
                continue;
            }

            let mut promise = unsafe { cqslot.as_ref() }.p.lock();
            if promise.discard {
                promise.discard = false;
                debug_assert!(promise.res.is_none());
                debug_assert!(promise.waker.is_none());
                drop(promise); // unlock
                self.inner.mark_free(cqslot);
                continue;
            }

            promise.do_set_value(cqe.res);
        }
        return Ok(());
    }
}

impl Park for Driver {
    type Unpark = Handle;
    type Error = std::io::Error;

    fn unpark(&self) -> Self::Unpark {
        self.handle()
    }

    fn park(&mut self) -> Result<(), Self::Error> {
        self.turn(None)
    }

    fn park_timeout(&mut self, duration: std::time::Duration) -> Result<(), Self::Error> {
        self.turn(Some(duration))
    }

    fn shutdown(&mut self) {
        self.inner.shutdown();
        for slot in &self.inner.slots {
            let mut promise = slot.p.lock();
            if !promise.discard && promise.res.is_none() {
                promise.do_set_value(ERRNO_FOR_SHUTDOWN);
            }
        }
    }
}

// 暂时没想到更好的错误码==
const ERRNO_FOR_SHUTDOWN: i32 = -libc::EINVAL;

#[derive(Debug, Clone)]
pub(crate) struct Handle {
    inner: Arc<Inner>,
}

impl Handle {
    fn current() -> (bool, Self) {
        let (is_current, handle) = crate::runtime::context::io_handle();
        (is_current, handle.expect("A Tokio 1.x context was found, but IO is disabled. Call `enable_io` on the runtime builder to enable IO."))
    }
}

impl Unpark for Handle {
    fn unpark(&self) {
        let add_nop = self.inner.set_unparked();
        if !add_nop {
            return;
        }

        let mut sqe = io_uring_sqe::zeroed();
        sqe.opcode = IORING_OP_NOP as u8;
        sqe.user_data = (1 as u64) << 48;
        let slotidx = self.inner.unpark_slot_idx();
        self.inner.do_submit(&sqe, slotidx, 0x7f, true);
        return;
    }
}

#[derive(Debug)]
enum State {
    Init(io_uring_sqe),
    Wait(Arc<Inner>, NonNull<PromiseSlot>),
    Done(i32),
}

unsafe impl Send for State {}

#[derive(Debug)]
pub(crate) struct CQEFuture {
    state: State,
}

impl CQEFuture {
    pub(crate) fn new(sqe: &io_uring_sqe) -> Self {
        CQEFuture {
            state: State::Init(*sqe),
        }
    }
}

impl Drop for CQEFuture {
    fn drop(&mut self) {
        if let State::Wait(inner, slot) = &self.state {
            let mut p = unsafe { slot.as_ref() }.p.lock();
            debug_assert!(!p.discard);
            if let Some(_res) = p.res {
                p.res = None;
                debug_assert!(p.waker.is_none());
                drop(p); // unlock

                inner.mark_free(*slot);
            } else {
                let _waker = p.waker.take(); // drop Waker
                p.discard = true;
            }
        }
    }
}

impl Future for CQEFuture {
    type Output = i32;

    fn poll(self: std::pin::Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let future = self.get_mut();
        match &future.state {
            State::Init(sqe) => {
                let (is_current, handle) = Handle::current();
                let waker = cx.waker();
                let submitres = handle.inner.submit(sqe, waker, !is_current);
                if submitres.0 {
                    future.state = State::Done(ERRNO_FOR_SHUTDOWN);
                    return Poll::Ready(ERRNO_FOR_SHUTDOWN);
                }
                if let Some(slot) = submitres.1 {
                    if let Poll::Ready(res) = handle.inner.poll(slot, waker) {
                        future.state = State::Done(res);
                        return Poll::Ready(res);
                    }
                    future.state = State::Wait(handle.inner, slot);
                    return Poll::Pending;
                }
                return Poll::Pending;
            }
            State::Wait(inner, slot) => {
                let res = ready!(inner.poll(*slot, cx.waker()));
                future.state = State::Done(res);
                return Poll::Ready(res);
            }
            &State::Done(ret) => {
                return Poll::Ready(ret);
            }
        }
    }
}

#[cfg(target_os = "linux")]
const IO_URING_SETUP_SYS: i64 = libc::SYS_io_uring_setup;
#[cfg(target_os = "macos")] // just make rustc happy
const IO_URING_SETUP_SYS: i32 = 0;

#[cfg(target_os = "linux")]
const IO_URING_ENTER_SYS: i64 = libc::SYS_io_uring_enter;
#[cfg(target_os = "macos")]
const IO_URING_ENTER_SYS: i32 = 0;

fn wakeup_sq_poll_thread(fd: i32) -> std::io::Result<i32> {
    let ret = unsafe {
        libc::syscall(
            IO_URING_ENTER_SYS,
            i64::from(fd),
            i64::from(1),
            i64::from(0),
            i64::from(IORING_ENTER_SQ_WAKEUP),
            0,
            size_of::<libc::sigset_t>() as c_long,
        ) as i32
    };
    return syscall2rust(ret);
}

fn io_uring_enter(
    fd: i32,
    to_submit: i64,
    flag: i64,
    duration: Option<&__kernel_timespec>,
) -> std::io::Result<i32> {
    let args = io_uring_getevents_arg {
        sigmask: 0,
        // look like size_of(libc::sigset_t) != sizeof(kernel::sigset_t)...
        // Currently, the kernel will ignore sigmask_sz when sigmask is NULL, so, it's fine.
        sigmask_sz: size_of::<libc::sigset_t>() as _,
        pad: 0,
        ts: duration.map_or(0, |v| v as *const _ as usize as u64),
    };
    let ret = unsafe {
        libc::syscall(
            IO_URING_ENTER_SYS,
            i64::from(fd),
            to_submit,
            i64::from(1),
            i64::from(IORING_ENTER_EXT_ARG) | flag,
            &args as *const _ as usize as c_long,
            size_of::<io_uring_getevents_arg>() as c_long,
        ) as i32
    };
    return syscall2rust(ret);
}

fn io_uring_setup(entries: u32, p: &mut io_uring_params) -> std::io::Result<OwnedFd> {
    let p = p as *mut _;
    let ret: i32 = unsafe { libc::syscall(IO_URING_SETUP_SYS, entries as i64, p as c_long) as i32 };
    return syscall2rust(ret).map(|v| unsafe { OwnedFd::from_raw_fd(v) });
}

fn duration_ts(dur: Duration) -> __kernel_timespec {
    __kernel_timespec {
        tv_sec: dur.as_secs() as _,
        tv_nsec: dur.subsec_nanos() as _,
    }
}

// 仅当 flags: u16 == 0 时, promise slot 才有效.
fn unpack(data: u64) -> (u16, NonNull<PromiseSlot>) {
    let flags = data >> 48;
    let ptr = (data & ((1u64 << 48) - 1)) as usize as *mut PromiseSlot;
    debug_assert!(!ptr.is_null());
    let ptr = unsafe { NonNull::new_unchecked(ptr) };
    return (flags as u16, ptr);
}

#[cfg(target_os = "linux")]
const MMAP_MAP_POPULATE: i32 = libc::MAP_POPULATE;
#[cfg(target_os = "macos")]
const MMAP_MAP_POPULATE: i32 = 0;

fn uring_mmap(fd: i32, offset: i64, size: usize) -> std::io::Result<MmapGuard> {
    let ptr = unsafe {
        libc::mmap(
            std::ptr::null_mut(),
            size,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_SHARED | MMAP_MAP_POPULATE,
            fd,
            offset,
        )
    };

    if ptr == libc::MAP_FAILED {
        Err(std::io::Error::last_os_error())
    } else {
        // The portable way to create a mapping is to specify addr as 0
        // (NULL), and omit MAP_FIXED from flags.  In this case, the system
        // chooses the address for the mapping; the address is chosen so as
        // not to conflict with any existing mapping, and will not be 0.
        debug_assert!(!ptr.is_null());
        Ok(MmapGuard::new(unsafe { NonNull::new_unchecked(ptr) }, size))
    }
}

fn alloc_slots(cap: usize) -> (Vec<PromiseSlot>, Option<NonNull<PromiseSlot>>) {
    assert!(cap >= 1);
    let mut slots = Vec::<PromiseSlot>::with_capacity(cap);
    slots.resize_with(cap, Default::default);
    let mut next = None;
    for item in slots.iter_mut().rev() {
        item.next = next;
        next = Some(item.into());
    }
    let free = slots.first().map(|v| v.into());
    debug_assert!(free.is_some());
    return (slots, free);
}
