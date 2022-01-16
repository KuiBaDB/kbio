use hdrhistogram;
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering::Relaxed};
use std::thread::sleep;
use std::time::{Duration, Instant};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;
use tokio::runtime::Builder;

const CONN_NUM: usize = 64;

const LOOPCNT: [u64; CONN_NUM] = [
    10000, 10000, 10000, 10000, 10000, 10000, 10000, 10000, 1000000000, 1000000000, 10000, 10000,
    10000, 10000, 10000, 10000, 10000, 10000, 1000000000, 1000000000, 10000, 10000, 10000, 10000,
    10000, 10000, 10000, 10000, 1000000000, 1000000000, 10000, 10000, 10000, 10000, 10000, 10000,
    10000, 10000, 1000000000, 1000000000, 10000, 10000, 10000, 10000, 10000, 10000, 10000, 10000,
    1000000000, 1000000000, 10000, 10000, 10000, 10000, 10000, 10000, 10000, 10000, 1000000000,
    1000000000, 10000, 10000, 10000, 10000,
];

const RUNTIME: u64 = 30; // seconds
const WORKLOAD_SERVER: &str = "172.30.173.30:33733";

static TERM: AtomicBool = AtomicBool::new(false);

type Histogram = hdrhistogram::Histogram<u64>;

async fn conn_main(idx: usize) -> Histogram {
    let mut timehdr = Histogram::new_with_bounds(1, 128000000000 /* 128 seconds */, 5).unwrap();
    let mut conn = TcpStream::connect(WORKLOAD_SERVER).await.unwrap();
    let mesg = LOOPCNT[idx];
    while !TERM.load(Relaxed) {
        let now = Instant::now();
        conn.write_u64_le(mesg).await.unwrap();
        conn.read_u64_le().await.unwrap();
        let d = now.elapsed().as_nanos() as u64;
        timehdr.record(d).unwrap();
    }
    return timehdr;
}

fn main() {
    let rt = Builder::new_multi_thread()
        .worker_threads(1)
        .enable_all()
        .build()
        .unwrap();

    let mut timehdrfut = Vec::with_capacity(CONN_NUM);
    for idx in 0..CONN_NUM {
        timehdrfut.push(rt.spawn(conn_main(idx)));
    }

    sleep(Duration::from_secs(RUNTIME));
    TERM.store(true, Relaxed);

    let mut timehdrs = Vec::with_capacity(CONN_NUM);
    for hdrfut in timehdrfut {
        timehdrs.push(rt.block_on(hdrfut).unwrap());
    }

    let mut timehdr_groupby: HashMap<u64, Histogram> = HashMap::new();
    for (idx, timehdr) in timehdrs.into_iter().enumerate() {
        if let Some(total_timehdr) = timehdr_groupby.get_mut(&LOOPCNT[idx]) {
            total_timehdr.add(timehdr).unwrap();
        } else {
            timehdr_groupby.insert(LOOPCNT[idx], timehdr);
        }
    }

    for (cnt, hdr) in timehdr_groupby {
        println!(
            "{},{},{},{},{},{},{},{}",
            cnt,
            hdr.min(),
            hdr.max(),
            hdr.value_at_quantile(0.9),
            hdr.value_at_quantile(0.95),
            hdr.value_at_quantile(0.99),
            hdr.value_at_quantile(0.999),
            hdr.value_at_quantile(0.9999),
        )
    }
    return;
}
