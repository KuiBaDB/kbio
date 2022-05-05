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
use crate::io::kbio::driver::{io_uring_sqe, CQEFuture, IORING_OP_CONNECT};
use crate::io::kbio::driver::{
    IORING_OP_RECV, IORING_OP_SHUTDOWN, IORING_OP_WRITE, IORING_OP_WRITEV,
};
use crate::io::kbio::{cqeres2rust, syscall2rust, OwnedFd};
use crate::io::{AsyncRead, AsyncWrite, ReadBuf};
use crate::net::tinymio::{new_ip_socket, socket_addr};
use crate::net::{to_socket_addrs, ToSocketAddrs};
use libc::{c_int, c_void, socklen_t};
use std::future::Future;
use std::io::{self, IoSlice};
use std::mem::size_of;
use std::net as stdnet;
use std::os::unix::io::AsRawFd;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::Duration;

fn setsockopt<T>(fd: c_int, opt: c_int, val: c_int, payload: T) -> io::Result<()> {
    unsafe {
        let payload = &payload as *const T as *const c_void;
        syscall2rust(libc::setsockopt(
            fd,
            opt,
            val,
            payload,
            size_of::<T>() as socklen_t,
        ))?;
        Ok(())
    }
}

#[derive(Debug)]
struct OPFuture {
    fut: CQEFuture,
    #[cfg(debug_assertions)]
    bufaddr: u64,
    #[cfg(debug_assertions)]
    buflen: u32,
}

/// TcpStream
#[derive(Debug)]
pub struct TcpStream {
    fd: OwnedFd,
    read_fut: Option<OPFuture>,
    write_fut: Option<OPFuture>,
    shutdown_fut: Option<OPFuture>,
}

impl TcpStream {
    /// set_nodelay
    pub fn set_nodelay(&self, nodelay: bool) -> io::Result<()> {
        setsockopt(
            self.fd.as_raw_fd(),
            libc::IPPROTO_TCP,
            libc::TCP_NODELAY,
            nodelay as c_int,
        )
    }

    /// set_linger
    pub fn set_linger(&self, dur: Option<Duration>) -> io::Result<()> {
        let linger = if let Some(dur) = dur {
            libc::linger {
                l_onoff: 1,
                l_linger: dur.as_secs() as c_int,
            }
        } else {
            libc::linger {
                l_onoff: 0,
                l_linger: 0,
            }
        };

        setsockopt(
            self.fd.as_raw_fd(),
            libc::SOL_SOCKET,
            libc::SO_LINGER,
            linger,
        )
    }

    /// connect
    pub async fn connect<A: ToSocketAddrs>(addr: A) -> io::Result<TcpStream> {
        let addrs = to_socket_addrs(addr).await?;

        let mut last_err = None;

        for addr in addrs {
            match TcpStream::connect_addr(&addr).await {
                Ok(stream) => return Ok(stream),
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

    async fn connect_addr(addr: &stdnet::SocketAddr) -> io::Result<TcpStream> {
        let fd = new_ip_socket(addr, libc::SOCK_STREAM)?;
        let (raw_addr, raw_addr_length) = socket_addr(addr);
        let mut sqe = io_uring_sqe::zeroed();
        sqe.opcode = IORING_OP_CONNECT as u8;
        sqe.fd = fd.as_raw_fd();
        sqe.__bindgen_anon_2.addr = raw_addr.as_ptr() as usize as u64;
        sqe.__bindgen_anon_1.off = raw_addr_length as u64;
        cqeres2rust(CQEFuture::new(&sqe).await)?;
        return Ok(TcpStream::new(fd));
    }

    // fd is nonblocking.
    pub(super) fn new(fd: OwnedFd) -> Self {
        Self {
            fd,
            read_fut: None,
            write_fut: None,
            shutdown_fut: None,
        }
    }
}

/*
fn readbuf_as_bytes<'a>(buf: &'a mut ReadBuf<'_>) -> &'a mut [u8] {
    unsafe { &mut *(buf.unfilled_mut() as *mut _ as *mut [u8]) }
}
*/
macro_rules! readbuf_as_bytes {
    ($buf: ident) => {
        unsafe { &mut *($buf.unfilled_mut() as *mut _ as *mut [u8]) }
    };
}

fn recv_fut(fd: i32, buf: &mut [u8]) -> CQEFuture {
    let mut sqe = io_uring_sqe::zeroed();
    sqe.opcode = IORING_OP_RECV as u8;
    sqe.fd = fd;
    sqe.__bindgen_anon_2.addr = buf.as_ptr() as usize as u64;
    sqe.len = buf.len() as u32;
    return CQEFuture::new(&sqe);
}

impl AsyncRead for TcpStream {
    fn poll_read(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        fn on_ready(res: i32, buf: &mut ReadBuf<'_>) -> Poll<io::Result<()>> {
            let res = cqeres2rust(res).map(|n| {
                let n = n as usize;
                unsafe { buf.assume_init(n) };
                buf.advance(n);
                return ();
            });
            return Poll::Ready(res);
        }

        #[cfg(debug_assertions)]
        let bufaddr = readbuf_as_bytes!(buf).as_ptr() as usize as u64;
        #[cfg(debug_assertions)]
        let buflen = readbuf_as_bytes!(buf).len() as u32;
        match &mut self.read_fut {
            None => {
                // SAFETY#1
                // Using readbuf_as_bytes(buf) will cause the error:
                // cannot infer an appropriate lifetime for lifetime parameter..
                //
                // if we use readbuf_as_bytes(), the type of buff is `&'l4`,
                // the type of fut and opfut are `CQEFuture<min('u, 'l4)>`,
                // and code at '#1' requires that opfut outlives self.read_fut whose type is `CQEFuture<'u>`,
                // which means that `min('u, 'l4)` should outlive `'a`, and 'l4 should outlive `'a`.
                //
                // If we specify `'l4: 'a`, we will get an error:
                // lifetimes do not match method in trait!
                let buff = readbuf_as_bytes!(buf);
                /*if let Poll::Ready(res) = recv(self.fd.as_raw_fd(), buff) {
                    let res = cqeres2rust64(res).map(|n| {
                        unsafe { buf.assume_init(n) };
                        buf.advance(n);
                        return ();
                    });
                    return Poll::Ready(res);
                }*/
                let mut fut = recv_fut(self.fd.as_raw_fd(), buff);
                match Pin::new(&mut fut).poll(cx) {
                    Poll::Pending => {
                        let opfut = OPFuture {
                            fut,
                            #[cfg(debug_assertions)]
                            bufaddr,
                            #[cfg(debug_assertions)]
                            buflen,
                        };
                        self.read_fut = Some(opfut); // #1
                        return Poll::Pending;
                    }
                    Poll::Ready(res) => {
                        return on_ready(res, buf);
                    }
                }
            }
            Some(fut) => {
                #[cfg(debug_assertions)]
                {
                    debug_assert_eq!(bufaddr, fut.bufaddr);
                    debug_assert_eq!(buflen, fut.buflen);
                }
                let res = ready!(Pin::new(&mut fut.fut).poll(cx));
                self.read_fut = None;
                return on_ready(res, buf);
            }
        }
    }
}

fn write_fut(fd: i32, buf: &[u8]) -> CQEFuture {
    let mut sqe = io_uring_sqe::zeroed();
    sqe.opcode = IORING_OP_WRITE as u8;
    sqe.fd = fd;
    sqe.__bindgen_anon_2.addr = buf.as_ptr() as usize as u64;
    sqe.len = buf.len() as u32;
    return CQEFuture::new(&sqe);
}

fn shutdown_fut(fd: i32, how: stdnet::Shutdown) -> CQEFuture {
    let mut sqe = io_uring_sqe::zeroed();
    sqe.opcode = IORING_OP_SHUTDOWN as u8;
    sqe.fd = fd;
    sqe.len = how as u32;
    return CQEFuture::new(&sqe);
}

fn writev_fut(fd: i32, bufs: &[IoSlice<'_>], offset: i64) -> CQEFuture {
    let mut sqe = io_uring_sqe::zeroed();
    sqe.opcode = IORING_OP_WRITEV as u8;
    sqe.fd = fd;
    sqe.__bindgen_anon_2.addr = bufs.as_ptr() as usize as u64;
    sqe.__bindgen_anon_1.off = offset as u64;
    sqe.len = bufs.len() as u32;
    return CQEFuture::new(&sqe);
}

impl AsyncWrite for TcpStream {
    fn poll_write(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<io::Result<usize>> {
        #[cfg(debug_assertions)]
        let bufaddr = buf.as_ptr() as usize as u64;
        #[cfg(debug_assertions)]
        let buflen = buf.len() as u32;
        fn on_ready(res: i32) -> Poll<io::Result<usize>> {
            Poll::Ready(cqeres2rust(res).map(|v| v as usize))
        }
        match &mut self.write_fut {
            None => {
                // SAFETY: See SAFETY#1
                let buf = unsafe { &*(buf as *const _) };
                /*if let Poll::Ready(res) = write(self.fd.as_raw_fd(), buf) {
                    return Poll::Ready(cqeres2rust64(res));
                }*/
                let mut fut = write_fut(self.fd.as_raw_fd(), buf);
                match Pin::new(&mut fut).poll(cx) {
                    Poll::Pending => {
                        let opfut = OPFuture {
                            fut,
                            #[cfg(debug_assertions)]
                            bufaddr,
                            #[cfg(debug_assertions)]
                            buflen,
                        };
                        self.write_fut = Some(opfut);
                        return Poll::Pending;
                    }
                    Poll::Ready(res) => {
                        return on_ready(res);
                    }
                }
            }
            Some(fut) => {
                #[cfg(debug_assertions)]
                {
                    debug_assert_eq!(bufaddr, fut.bufaddr);
                    debug_assert_eq!(buflen, fut.buflen);
                }
                let res = ready!(Pin::new(&mut fut.fut).poll(cx));
                self.write_fut = None;
                return on_ready(res);
            }
        }
    }

    fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        // Stream has no buffer.
        Poll::Ready(Ok(()))
    }

    fn poll_shutdown(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        fn on_ready(res: i32) -> Poll<io::Result<()>> {
            Poll::Ready(cqeres2rust(res).map(|_v| ()))
        }
        match &mut self.shutdown_fut {
            None => {
                let mut fut = shutdown_fut(self.fd.as_raw_fd(), stdnet::Shutdown::Write);
                match Pin::new(&mut fut).poll(cx) {
                    Poll::Pending => {
                        let opfut = OPFuture {
                            fut,
                            #[cfg(debug_assertions)]
                            bufaddr: 0,
                            #[cfg(debug_assertions)]
                            buflen: 0,
                        };
                        self.shutdown_fut = Some(opfut);
                        return Poll::Pending;
                    }
                    Poll::Ready(res) => {
                        return on_ready(res);
                    }
                }
            }
            Some(fut) => {
                let res = ready!(Pin::new(&mut fut.fut).poll(cx));
                self.shutdown_fut = None;
                return on_ready(res);
            }
        }
    }

    fn poll_write_vectored(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        bufs: &[IoSlice<'_>],
    ) -> Poll<io::Result<usize>> {
        fn on_ready(res: i32) -> Poll<io::Result<usize>> {
            Poll::Ready(cqeres2rust(res).map(|v| v as usize))
        }
        let bufaddr = bufs.as_ptr() as usize;
        let buflen = bufs.len();
        match &mut self.write_fut {
            None => {
                // SAFETY: See SAFETY#1
                let buf = unsafe { std::slice::from_raw_parts(bufaddr as *const _, buflen) };
                /*if let Poll::Ready(res) = writev(self.fd.as_raw_fd(), buf, 0) {
                    return Poll::Ready(cqeres2rust64(res));
                }*/
                let mut fut = writev_fut(self.fd.as_raw_fd(), buf, 0);
                match Pin::new(&mut fut).poll(cx) {
                    Poll::Pending => {
                        let opfut = OPFuture {
                            fut,
                            #[cfg(debug_assertions)]
                            bufaddr: bufaddr as u64,
                            #[cfg(debug_assertions)]
                            buflen: buflen as u32,
                        };
                        self.write_fut = Some(opfut);
                        return Poll::Pending;
                    }
                    Poll::Ready(res) => {
                        return on_ready(res);
                    }
                }
            }
            Some(fut) => {
                #[cfg(debug_assertions)]
                {
                    debug_assert_eq!(bufaddr as u64, fut.bufaddr);
                    debug_assert_eq!(buflen as u32, fut.buflen);
                }
                let res = ready!(Pin::new(&mut fut.fut).poll(cx));
                self.write_fut = None;
                return on_ready(res);
            }
        }
    }

    fn is_write_vectored(&self) -> bool {
        true
    }
}
