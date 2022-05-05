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

pub(crate) mod driver;

use std::os::unix::io::{AsRawFd, FromRawFd, RawFd};

// COPY FROM STD. REMOVE WHEN std::os::unix::io::OwnedFd is stable.
#[derive(Debug)]
pub(crate) struct OwnedFd {
    fd: RawFd,
}

impl Drop for OwnedFd {
    fn drop(&mut self) {
        let _ = unsafe { libc::close(self.fd) };
    }
}

impl AsRawFd for OwnedFd {
    #[inline]
    fn as_raw_fd(&self) -> RawFd {
        self.fd
    }
}

impl FromRawFd for OwnedFd {
    #[inline]
    unsafe fn from_raw_fd(fd: RawFd) -> Self {
        Self { fd }
    }
}

pub(crate) fn syscall2rust(ret: i32) -> std::io::Result<i32> {
    if ret < 0 {
        let err = std::io::Error::last_os_error();
        return Err(err);
    } else {
        return Ok(ret);
    }
}

pub(crate) fn cqeres2rust(res: i32) -> std::io::Result<i32> {
    if res < 0 {
        return Err(std::io::Error::from_raw_os_error(-res));
    } else {
        return Ok(res);
    }
}
