//! Thread local runtime context
use crate::runtime::{Handle, TryCurrentError};

use crate::runtime::thread_pool::{current_worker_io_handle, current_worker_time_handle};
use std::cell::RefCell;

thread_local! {
    static CONTEXT: RefCell<Option<Handle>> = RefCell::new(None)
}

pub(crate) fn try_current() -> Result<Handle, crate::runtime::TryCurrentError> {
    match CONTEXT.try_with(|ctx| ctx.borrow().clone()) {
        Ok(Some(handle)) => Ok(handle),
        Ok(None) => Err(TryCurrentError::new_no_context()),
        Err(_access_error) => Err(TryCurrentError::new_thread_local_destroyed()),
    }
}

pub(crate) fn current() -> Handle {
    match try_current() {
        Ok(handle) => handle,
        Err(e) => panic!("{}", e),
    }
}

// bool = true, 意味着返回的是当前线程的 handle. 否则返回的是其他线程的 handle.
#[cfg(any(feature = "net", feature = "process", all(unix, feature = "signal")))]
pub(crate) fn io_handle() -> (bool, crate::runtime::driver::IoHandle) {
    if let Some(handle) = current_worker_io_handle() {
        return (true, handle);
    }

    match CONTEXT.try_with(|ctx| {
        let ctx = ctx.borrow();
        ctx.as_ref()
            .expect(crate::util::error::CONTEXT_MISSING_ERROR)
            .as_inner()
            .io_handle
            .clone()
    }) {
        Ok(io_handle) => (false, io_handle),
        Err(_) => panic!("{}", crate::util::error::THREAD_LOCAL_DESTROYED_ERROR),
    }
}

cfg_signal_internal! {
    #[cfg(unix)]
    pub(crate) fn signal_handle() -> crate::runtime::driver::SignalHandle {
        match CONTEXT.try_with(|ctx| {
            let ctx = ctx.borrow();
            ctx.as_ref().expect(crate::util::error::CONTEXT_MISSING_ERROR).as_inner().signal_handle.clone()
        }) {
            Ok(signal_handle) => signal_handle,
            Err(_) => panic!("{}", crate::util::error::THREAD_LOCAL_DESTROYED_ERROR),
        }
    }
}

cfg_time! {
    pub(crate) fn time_handle() -> crate::runtime::driver::TimeHandle {
        if let Some(handle) = current_worker_time_handle() {
            return handle;
        }

        match CONTEXT.try_with(|ctx| {
            let ctx = ctx.borrow();
            ctx.as_ref().expect(crate::util::error::CONTEXT_MISSING_ERROR).as_inner().time_handle.clone()
        }) {
            Ok(time_handle) => time_handle,
            Err(_) => panic!("{}", crate::util::error::THREAD_LOCAL_DESTROYED_ERROR),
        }
    }

    cfg_test_util! {
        pub(crate) fn clock() -> Option<crate::runtime::driver::Clock> {
            // 这里也应该返回 current_worker_clock() 之类的, 但我懒得改了.
            match CONTEXT.try_with(|ctx| (*ctx.borrow()).as_ref().map(|ctx| ctx.as_inner().clock.clone())) {
                Ok(clock) => clock,
                Err(_) => panic!("{}", crate::util::error::THREAD_LOCAL_DESTROYED_ERROR),
            }
        }
    }
}

cfg_rt! {
    pub(crate) fn spawn_handle() -> Option<crate::runtime::Spawner> {
        match CONTEXT.try_with(|ctx| (*ctx.borrow()).as_ref().map(|ctx| ctx.spawner.clone())) {
            Ok(spawner) => spawner,
            Err(_) => panic!("{}", crate::util::error::THREAD_LOCAL_DESTROYED_ERROR),
        }
    }
}

/// Sets this [`Handle`] as the current active [`Handle`].
///
/// [`Handle`]: Handle
pub(crate) fn enter(new: Handle) -> EnterGuard {
    match try_enter(new) {
        Some(guard) => guard,
        None => panic!("{}", crate::util::error::THREAD_LOCAL_DESTROYED_ERROR),
    }
}

/// Sets this [`Handle`] as the current active [`Handle`].
///
/// [`Handle`]: Handle
pub(crate) fn try_enter(new: Handle) -> Option<EnterGuard> {
    CONTEXT
        .try_with(|ctx| {
            let old = ctx.borrow_mut().replace(new);
            EnterGuard(old)
        })
        .ok()
}

#[derive(Debug)]
pub(crate) struct EnterGuard(Option<Handle>);

impl Drop for EnterGuard {
    fn drop(&mut self) {
        CONTEXT.with(|ctx| {
            *ctx.borrow_mut() = self.0.take();
        });
    }
}
