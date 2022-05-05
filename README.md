
KBIO, add some experimental features to tokio. Currently, kbio is just used in [KuiBaDB](https://hidva.com/g?u=https://github.com/KuiBaDB/KuiBaDB), it is only a prototype and has not been tested fully. Our experience using C++20 coroutines in [Hologres](https://hidva.com/g?u=https://www.aliyun.com/product/bigdata/hologram) tells us that Worker Steal is very necessary. So we build kbio based on tokio.

-   We run one IO-Uring instance per Worker. Before that, all Workers in Tokio used an Epoll instance, mainly because once a file descriptor is bound to an Epoll instance in Tokio, then the file descriptor will never switch to other Epoll instances, which will affect the effect of Worker Steal.

-   Add [sysmon](https://github.com/tokio-rs/tokio/pull/4407)

# Usage

Most of them are fully compatible with tokio. See [integrate kbio into memc](https://hidva.com/g?u=https://github.com/memc-rs/memc-rs/discussions/7) for another example.

# Benchmark

We use [monoio-benchmark](https://hidva.com/g?u=https://github.com/hidva/monoio-benchmark) to do the benchmark, See [integrate kbio into memc](https://hidva.com/g?u=https://github.com/memc-rs/memc-rs/discussions/7) for another example.
