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
use crate::io::kbio::driver::{io_uring_sqe, CQEFuture, IORING_OP_ACCEPT};
use crate::io::kbio::{cqeres2rust, OwnedFd};
use crate::net::kbio_tcp::stream::TcpStream;
use crate::net::tinymio::to_socket_addr;
use crate::net::{to_socket_addrs, ToSocketAddrs};
use libc::{sockaddr_storage, socklen_t};
use std::io;
use std::mem::{size_of, MaybeUninit};
use std::net as stdnet;
use std::os::unix::io::{AsRawFd, FromRawFd, IntoRawFd};

/// TcpListener
#[derive(Debug)]
pub struct TcpListener(OwnedFd);

// Working in blocking mode.
impl TcpListener {
    /// bind
    pub async fn bind<A: ToSocketAddrs>(addr: A) -> io::Result<TcpListener> {
        let addrs = to_socket_addrs(addr).await?;
        let mut last_err = None;

        for addr in addrs {
            match TcpListener::bind_addr(&addr) {
                Ok(listener) => return Ok(listener),
                Err(e) => last_err = Some(e),
            }
        }

        Err(last_err.unwrap_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "could not resolve to any address",
            )
        }))
    }

    fn bind_addr(addr: &stdnet::SocketAddr) -> io::Result<TcpListener> {
        let stdlistener = stdnet::TcpListener::bind(addr)?;
        return Ok(stdlistener2kbio(stdlistener));
    }

    /// accept
    pub async fn accept(&self) -> io::Result<(TcpStream, stdnet::SocketAddr)> {
        let mut addr: MaybeUninit<sockaddr_storage> = MaybeUninit::uninit();
        let mut addrlen = size_of::<sockaddr_storage>() as socklen_t;
        let mut sqe = io_uring_sqe::zeroed();
        sqe.opcode = IORING_OP_ACCEPT as u8;
        sqe.fd = self.0.as_raw_fd();
        sqe.__bindgen_anon_2.addr = addr.as_mut_ptr() as usize as u64;
        sqe.__bindgen_anon_1.addr2 = (&mut addrlen) as *mut _ as usize as u64;
        sqe.__bindgen_anon_3.accept_flags = libc::SOCK_NONBLOCK as u32;
        let sockfd = cqeres2rust(CQEFuture::new(&sqe).await)?;
        let stream = TcpStream::new(unsafe { OwnedFd::from_raw_fd(sockfd) });
        let sockaddr = to_socket_addr(unsafe { addr.assume_init_ref() })?;
        return Ok((stream, sockaddr));
    }

    /// from_std
    pub fn from_std(stdlistener: stdnet::TcpListener) -> io::Result<TcpListener> {
        // Non blocking mode causes the accept SQE to end immediately with error 11
        // (Resource temporarily unavailable)
        stdlistener.set_nonblocking(false)?;
        return Ok(stdlistener2kbio(stdlistener));
    }
}

fn stdlistener2kbio(stdlistener: stdnet::TcpListener) -> TcpListener {
    let fd = unsafe { OwnedFd::from_raw_fd(stdlistener.into_raw_fd()) };
    return TcpListener(fd);
}
