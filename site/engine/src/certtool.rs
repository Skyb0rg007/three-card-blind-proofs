//! The certificate table for the site, and native checks of certified play.
//!
//!   cert-tool pack < Data.v > table.bin
//!       Convert proofs/bfirst/Data.v (decompressed) to the site's binary
//!       form (the site serves it gzipped).
//!   cert-tool same Data.v table.bin
//!       Check that the binary holds exactly Data.v's arrays and constants.
//!   cert-tool check-all TABLE [THREADS [LO HI]]
//!       Run the port of Rocq's check on every record (or [LO, HI)).
//!   cert-tool trace TABLE START STEP COUNT CAP
//!       Print the checker's search from records START, START+STEP, ...
//!       (compared with test/cert-ocaml.ml, the extracted Rocq model).
//!   cert-tool selfplay TABLE ADV GAMES SEED [THREADS]
//!       Certified B against A = random | bias | rank | val | searchMS.
//!       TCB_DUMP=FILE writes the game records to FILE.
//!   cert-tool replay < GAMES
//!       Every position of each game record with its legal moves
//!       (compared with test/cert-ocaml.ml replay).
//!
//! TABLE is a binary table or a Data.v file.

use std::io::{Read, Write};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;
use tcb_engine::cert::{self, Table};
use tcb_engine::certtest::{self, Adversary, Summary};
use tcb_engine::model::*;

fn read_table(path: &str) -> Table {
    let t0 = Instant::now();
    let bytes = std::fs::read(path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let t = if bytes.starts_with(b"TCBWIN") {
        Table::from_bytes(&bytes)
    } else {
        Table::parse_data_v(std::str::from_utf8(&bytes).expect("Data.v is not UTF-8"))
    }
    .unwrap_or_else(|e| panic!("{path}: {e}"));
    eprintln!(
        "{path}: {} records, H={} ott={} tt={} fuel={}, checksum {:016x} ({:.1}s)",
        t.len(),
        t.h,
        t.ott,
        t.tt,
        t.fuel,
        t.checksum(),
        t0.elapsed().as_secs_f64()
    );
    t
}

fn arg<T: std::str::FromStr>(args: &[String], i: usize, d: T) -> T {
    args.get(i).and_then(|x| x.parse().ok()).unwrap_or(d)
}

/// `BFirst.v`: the opening's record of rank 587 asks for 17 life.
fn opening(t: &Table) {
    let k = t.key(&init(Player::B));
    let v = t.lookup(&k, cert::OPENING_RANK);
    assert_eq!(v, Some(cert::OPENING_VAL), "opening record");
    let pick = t.pick_record(&init(Player::B));
    eprintln!("opening: lookup rank {} = {:?}; B plays from {:?} (rank, value)", cert::OPENING_RANK, v, pick);
}

fn check_all(t: &Table, threads: usize, lo: usize, hi: usize) {
    opening(t);
    let t0 = Instant::now();
    let next = AtomicUsize::new(lo);
    let done = AtomicUsize::new(0);
    const CHUNK: usize = 2000;
    let results: Vec<(usize, u64, Vec<usize>, u64)> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..threads)
            .map(|_| {
                sc.spawn(|| {
                    let (mut n, mut nodes, mut bad, mut worst) = (0usize, 0u64, vec![], 0u64);
                    loop {
                        let a = next.fetch_add(CHUNK, Ordering::Relaxed);
                        if a >= hi {
                            break;
                        }
                        for j in a..(a + CHUNK).min(hi) {
                            let mut k = 0;
                            if !t.record_ok(j, &mut k) {
                                bad.push(j);
                            }
                            nodes += k;
                            worst = worst.max(k);
                            n += 1;
                        }
                        let d = done.fetch_add(CHUNK, Ordering::Relaxed) + CHUNK;
                        if d % 100_000 < CHUNK {
                            eprintln!("  {d} records, {:.0}s", t0.elapsed().as_secs_f64());
                        }
                    }
                    (n, nodes, bad, worst)
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let n: usize = results.iter().map(|r| r.0).sum();
    let nodes: u64 = results.iter().map(|r| r.1).sum();
    let worst = results.iter().map(|r| r.3).max().unwrap_or(0);
    let mut bad: Vec<usize> = results.into_iter().flat_map(|r| r.2).collect();
    bad.sort();
    println!(
        "check-all [{lo}, {hi}): {n} records checked, {} fail; {nodes} nodes (max {worst} for one record); {:.1}s on {threads} threads",
        bad.len(),
        t0.elapsed().as_secs_f64()
    );
    for j in bad.iter().take(20) {
        println!("  FAIL record {j}: rank {} val {}", t.rank_of(*j), t.val_of(*j));
    }
    if !bad.is_empty() || n != hi - lo {
        std::process::exit(1);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        Some("pack") => {
            let mut text = String::new();
            std::io::stdin().read_to_string(&mut text).unwrap();
            let t = Table::parse_data_v(&text).unwrap_or_else(|e| panic!("Data.v: {e}"));
            opening(&t);
            let b = t.to_bytes();
            assert_eq!(Table::from_bytes(&b).map(|u| u.checksum()), Ok(t.checksum()), "round trip");
            std::io::stdout().write_all(&b).unwrap();
            eprintln!("packed {} records into {} bytes, checksum {:016x}", t.len(), b.len(), t.checksum());
        }
        Some("same") => {
            let a = read_table(&args[2]);
            let b = read_table(&args[3]);
            let same = (a.h, a.ott, a.tt, a.fuel) == (b.h, b.ott, b.tt, b.fuel) && a.k1 == b.k1 && a.k2 == b.k2 && a.rv == b.rv;
            println!("same: {same}");
            if !same {
                std::process::exit(1);
            }
        }
        Some("check-all") => {
            let t = read_table(&args[2]);
            let threads = arg(&args, 3, 3usize);
            let lo = arg(&args, 4, 0usize);
            let hi = arg(&args, 5, t.len()).min(t.len());
            check_all(&t, threads, lo, hi);
        }
        Some("trace") => {
            let t = read_table(&args[2]);
            let (start, step, count, cap) = (arg(&args, 3, 0usize), arg(&args, 4, 1usize), arg(&args, 5, 1usize), arg(&args, 6, 1000usize));
            let mut out = std::io::BufWriter::new(std::io::stdout());
            for k in 0..count {
                let j = start + k * step;
                if j >= t.len() {
                    break;
                }
                out.write_all(certtest::trace_record(&t, j, cap).as_bytes()).unwrap();
            }
        }
        Some("mutants") => {
            // The check is not vacuous: weaken records and count rejections.
            let t = read_table(&args[2]);
            let stride = arg(&args, 3, 100usize);
            let (mut n, mut less_life, mut life_tried, mut rank0, mut nodes) = (0, 0, 0, 0, 0u64);
            for j in (0..t.len()).step_by(stride) {
                let s = t.record_state(j).unwrap();
                n += 1;
                if t.val_of(j) > 0 {
                    life_tried += 1;
                    let weaker = cert::entry(&s, t.val_of(j) - 1);
                    less_life += !t.check_win(t.rank_of(j), t.fuel, true, &weaker, &mut nodes) as u32;
                }
                rank0 += !t.check_win(0, t.fuel, true, &s, &mut nodes) as u32;
            }
            println!(
                "mutants over {n} records: one life less rejected {less_life} of {life_tried}; rank 0 rejected {rank0} of {n}"
            );
        }
        Some("replay") => {
            let mut input = String::new();
            std::io::stdin().read_to_string(&mut input).unwrap();
            let mut out = std::io::BufWriter::new(std::io::stdout());
            for line in input.lines().filter(|l| !l.trim().is_empty()) {
                let rec: Vec<u32> = line.split_whitespace().map(|x| x.parse().unwrap()).collect();
                let (_, mvs) = tcb_engine::replay_all(&rec);
                assert_eq!(mvs.len(), rec.len() - 3, "illegal move in record");
                out.write_all(certtest::replay_text(&rec).as_bytes()).unwrap();
            }
        }
        Some("selfplay") => {
            let t = read_table(&args[2]);
            let adv = Adversary::parse(&args[3]).expect("adversary: random | bias | rank | val | searchMS");
            let games = arg(&args, 4, 100u64);
            let seed = arg(&args, 5, 1u64);
            let threads = arg(&args, 6, 3u64).max(1);
            let t0 = Instant::now();
            let parts: Vec<Summary> = std::thread::scope(|sc| {
                let hs: Vec<_> = (0..threads)
                    .map(|k| {
                        let t = &t;
                        sc.spawn(move || {
                            let n = games / threads + u64::from(k < games % threads);
                            certtest::selfplay(t, adv, n, seed.wrapping_add(k.wrapping_mul(0x1234_5678_9abc_def1)))
                        })
                    })
                    .collect();
                hs.into_iter().map(|h| h.join().unwrap()).collect()
            });
            let mut all = Summary::default();
            for p in &parts {
                all.add(p);
            }
            println!(
                "selfplay {adv:?}: {} games ({} distinct), B won {}; turns mean {:.1} max {}; decisions A {} B {}; {} plans, {} checker nodes, {} turn starts ({} on the record's life); {:.1}s",
                all.games,
                all.records.iter().collect::<std::collections::HashSet<_>>().len(),
                all.b_wins,
                all.turns_total as f64 / all.games.max(1) as f64,
                all.turns_max,
                all.decisions_a,
                all.decisions_b,
                all.plans,
                all.nodes,
                all.segments,
                all.record_life,
                t0.elapsed().as_secs_f64()
            );
            if let Ok(path) = std::env::var("TCB_DUMP") {
                std::fs::write(&path, all.records.join("\n") + "\n").unwrap();
            }
            for f in all.failures.iter().take(20) {
                println!("  FAIL {f}");
            }
            if all.b_wins != all.games || !all.failures.is_empty() {
                std::process::exit(1);
            }
        }
        _ => {
            eprintln!("usage: see the top of site/engine/src/certtool.rs");
            std::process::exit(2);
        }
    }
}
