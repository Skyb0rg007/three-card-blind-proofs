//! Exploration, compilation and the level-by-level fixed point
//! (Fix.reach and Fix.solve), with threads instead of forked workers. The
//! directory layout is the OCaml solver's: dig, keys, vals, meta.

use crate::fix::{self, Cfg, Line, INF, LINF, LNINF, NINF, SENT};
use crate::model::*;
use memmap2::{Mmap, MmapMut};
use rustc_hash::FxHashMap as HashMap;
use std::fs::{self, File, OpenOptions};
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicI32, AtomicU32, AtomicU64, AtomicUsize, Ordering::Relaxed};
use std::sync::Mutex;
use std::time::Instant;

const RSIZE: usize = 32;

pub fn jobs() -> usize {
    std::env::var("TCB_JOBS")
        .ok()
        .and_then(|j| j.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |n| n.get()))
        .max(1)
}

/// The k-th of w near-equal slices of [0, n) (Par.chunk).
fn chunk(n: usize, w: usize, k: usize) -> (usize, usize) {
    (k * n / w, (k + 1) * n / w)
}

pub struct Solver {
    pub dir: PathBuf,
    pub n: usize,
    pub nb: usize,
    pub nl: usize,
    pub pinned: bool,
    pub dig: Vec<i64>,
    pub keys: Vec<[u8; RSIZE]>,
    vals_map: MmapMut,
}

impl Solver {
    fn vals(&self) -> &[AtomicI32] {
        // the map is page-aligned and holds n int32s
        unsafe { std::slice::from_raw_parts(self.vals_map.as_ptr() as *const AtomicI32, self.n) }
    }
    pub fn get(&self, i: usize) -> i64 {
        fix::of32(self.vals()[i].load(Relaxed))
    }
    pub fn set(&self, i: usize, v: i64) {
        self.vals()[i].store(fix::to32(v), Relaxed)
    }
    pub fn base_key(&self, b: usize) -> &[u8] {
        let r = &self.keys[b];
        &r[1..1 + r[0] as usize]
    }
    fn life_of_slot(&self, k: usize) -> u32 {
        if self.pinned { 20 } else { k as u32 + 1 }
    }
    pub fn key_at(&self, i: usize) -> Vec<u8> {
        fix::with_life(self.base_key(i % self.nb), self.life_of_slot(i / self.nb))
    }
    pub fn find(&self, d: i64) -> Option<usize> {
        self.dig.binary_search(&d).ok()
    }
    pub fn id(&self, k: &[u8]) -> Option<usize> {
        let slot = if self.pinned { 0 } else { k[1] as usize - 1 };
        self.find(fix::digest_key(&fix::base_of(k))).map(|b| slot * self.nb + b)
    }
}

/// The bases reachable from s0's, breadth first, each compiled as it is
/// expanded. A turn start is given an id when first reached (from a sharded
/// map shared by the workers), and programs refer to turn starts by id;
/// afterwards the bases are put in digest order, with `perm` mapping ids to
/// them. Turns are compiled with A on SENT life, so their successors with
/// less than 20 damage to A are exactly those with A on 20.
pub fn reach(c: &Cfg, s0: &State, dir: &Path) -> (Solver, Programs) {
    fs::create_dir_all(dir).unwrap();
    let t0 = Instant::now();
    let k0 = fix::base_of(&fix::key_gen(c.full_a, s0));
    const SHARDS: usize = 256;
    let shards: Vec<Mutex<HashMap<i64, u32>>> = (0..SHARDS).map(|_| Mutex::new(HashMap::default())).collect();
    let shard = |d: i64| &shards[(d as u64 >> 56) as usize];
    let count = AtomicU32::new(1);
    shard(fix::digest_key(&k0)).lock().unwrap().insert(fix::digest_key(&k0), 0);
    // (id, digest, key) of every base
    let mut all: Vec<(u32, i64, Vec<u8>)> = vec![(0, fix::digest_key(&k0), k0.clone())];
    let mut layer: Vec<(u32, Vec<u8>)> = vec![(0, k0)];
    let w = jobs();
    let mut outs: Vec<Out> = (0..w)
        .map(|k| Out {
            file: BufWriter::with_capacity(1 << 20, File::create(dir.join(format!("prog-{k}"))).unwrap()),
            bytes: 0,
            words: 0,
            at: vec![],
        })
        .collect();
    let mut depth = 0;
    while !layer.is_empty() {
        let next = AtomicUsize::new(0);
        let found: Vec<Vec<(u32, i64, Vec<u8>)>> = std::thread::scope(|sc| {
            let hs: Vec<_> = outs
                .iter_mut()
                .map(|out| {
                    let (layer, next, shard, count) = (&layer, &next, &shard, &count);
                    sc.spawn(move || {
                        let new = std::cell::RefCell::new(vec![]);
                        let tgt = |s: &State| -> i64 {
                            let u = SENT as i64 - s.side_a.life as i64;
                            assert!(u >= 0);
                            // damage of 20 or more kills A at every level: a
                            // placeholder the guard always decides
                            if u >= 20 {
                                return 31;
                            }
                            let b = fix::base_of(&fix::key_gen(c.full_a, s));
                            let d = fix::digest_key(&b);
                            let mut m = shard(d).lock().unwrap();
                            let id = *m.entry(d).or_insert_with(|| {
                                let id = count.fetch_add(1, Relaxed);
                                new.borrow_mut().push((id, d, b));
                                id
                            });
                            assert!(id < 1 << 26);
                            ((id as i64) << 5) | u
                        };
                        loop {
                            let i = next.fetch_add(1, Relaxed);
                            if i >= layer.len() {
                                break;
                            }
                            let (id, key) = &layer[i];
                            let s = fix::of_key(&fix::with_life(key, SENT));
                            let (prog, nn) = fix::compile(c, &tgt, &s);
                            let p = fix::pack(&prog, nn, c.big);
                            out.at.push((*id, out.bytes));
                            out.file.write_all(&p).unwrap();
                            out.bytes += p.len() as u64;
                            out.words += prog.len() as u64;
                        }
                        new.into_inner()
                    })
                })
                .collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let expanded = layer.len();
        layer = vec![];
        for f in found {
            for (id, d, k) in f {
                layer.push((id, k.clone()));
                all.push((id, d, k));
            }
        }
        depth += 1;
        println!("  reach: layer {depth}, {expanded} expanded, {} found ({:.1}s)", all.len(), t0.elapsed().as_secs_f64());
    }
    drop(shards);
    all.sort_unstable_by_key(|(_, d, _)| *d);
    let nb = all.len();
    let nl = if c.full_a { 1 } else { s0.side_a.life as usize };
    let n = nl * nb;
    let mut dig = Vec::with_capacity(nb);
    let mut keys = Vec::with_capacity(nb);
    let mut perm = vec![0u32; nb];
    {
        let mut dw = BufWriter::new(File::create(dir.join("dig")).unwrap());
        let mut kw = BufWriter::new(File::create(dir.join("keys")).unwrap());
        for (b, (id, d, k)) in all.into_iter().enumerate() {
            assert!(k.len() < RSIZE);
            let mut r = [0u8; RSIZE];
            r[0] = k.len() as u8;
            r[1..1 + k.len()].copy_from_slice(&k);
            dw.write_all(&d.to_le_bytes()).unwrap();
            kw.write_all(&r).unwrap();
            dig.push(d);
            keys.push(r);
            perm[id as usize] = b as u32;
        }
    }
    let mut part = vec![0u16; nb];
    let mut off = vec![0u64; nb];
    let (mut words, mut bytes) = (0u64, 0u64);
    let mut maps = vec![];
    for (k, mut out) in outs.into_iter().enumerate() {
        out.file.flush().unwrap();
        for &(id, o) in &out.at {
            part[id as usize] = k as u16;
            off[id as usize] = o;
        }
        words += out.words;
        bytes += out.bytes;
        let f = File::open(dir.join(format!("prog-{k}"))).unwrap();
        maps.push(if out.bytes == 0 { None } else { Some(unsafe { Mmap::map(&f).unwrap() }) });
    }
    let f = OpenOptions::new().read(true).write(true).create(true).truncate(true).open(dir.join("vals")).unwrap();
    f.set_len(4 * n as u64).unwrap();
    let vals_map = unsafe { MmapMut::map_mut(&f).unwrap() };
    println!("  reach: {depth} layers; compiled {nb} turns, {words} program words, packed into {bytes} bytes");
    let sv = Solver { dir: dir.to_path_buf(), n, nb, nl, pinned: c.full_a, dig, keys, vals_map };
    (sv, Programs { maps, part, off, perm })
}

/// The compiled turns, packed (`fix::pack`): per worker a program file, and
/// per id (discovery order) its file and byte offset.
pub struct Programs {
    maps: Vec<Option<Mmap>>, // None for a file with no bytes
    part: Vec<u16>,
    off: Vec<u64>,
    // turn starts are referenced by their id in discovery order, and the
    // solve works in id order: the base of each id
    perm: Vec<u32>,
}

impl Programs {
    fn prog(&self, j: usize) -> &[u8] {
        let Some(m) = &self.maps[self.part[j] as usize] else { return &[] };
        &m[self.off[j] as usize..]
    }
}

/// A worker's output file during exploration.
struct Out {
    file: BufWriter<File>,
    bytes: u64,
    words: u64,
    // (id, offset) of each turn written
    at: Vec<(u32, u64)>,
}

/// For each id, the ids whose turns read it at the same A-life level
/// (turn starts reached with no damage to A; with A's life pinned, all of
/// them), in compressed rows.
struct Deps {
    start: Vec<u64>,
    list: Vec<u32>,
}

impl Deps {
    fn of(&self, b: usize) -> &[u32] {
        &self.list[self.start[b] as usize..self.start[b + 1] as usize]
    }

    /// Two passes over the programs (count, then fill), so that no
    /// (target, reader) pairs are held in memory. A row's order depends on
    /// the threads, which only changes the order readers are marked dirty.
    fn build(sv: &Solver, progs: &Programs, w: usize) -> Deps {
        let t0 = Instant::now();
        let nb = sv.nb;
        // the distinct same-level targets of reader j, into ts
        let targets = |j: usize, ts: &mut Vec<u32>| {
            ts.clear();
            for x in fix::packed_targets(progs.prog(j)) {
                if (x & 31) < 20 && (sv.pinned || x & 31 == 0) {
                    ts.push((x >> 5) as u32);
                }
            }
            ts.sort_unstable();
            ts.dedup();
        };
        let fill: Vec<AtomicU64> = (0..nb + 1).map(|_| AtomicU64::new(0)).collect();
        std::thread::scope(|sc| {
            for k in 0..w {
                let (fill, targets) = (&fill, &targets);
                sc.spawn(move || {
                    let (lo, hi) = chunk(nb, w, k);
                    let mut ts = vec![];
                    for j in lo..hi {
                        targets(j, &mut ts);
                        for &t in &ts {
                            fill[t as usize + 1].fetch_add(1, Relaxed);
                        }
                    }
                });
            }
        });
        let mut start = vec![0u64; nb + 1];
        for b in 0..nb {
            start[b + 1] = start[b] + fill[b + 1].load(Relaxed);
        }
        for b in 0..=nb {
            fill[b].store(start[b], Relaxed);
        }
        let list: Vec<AtomicU32> = (0..start[nb]).map(|_| AtomicU32::new(0)).collect();
        std::thread::scope(|sc| {
            for k in 0..w {
                let (fill, targets, list) = (&fill, &targets, &list);
                sc.spawn(move || {
                    let (lo, hi) = chunk(nb, w, k);
                    let mut ts = vec![];
                    for j in lo..hi {
                        targets(j, &mut ts);
                        for &t in &ts {
                            list[fill[t as usize].fetch_add(1, Relaxed) as usize].store(j as u32, Relaxed);
                        }
                    }
                });
            }
        });
        drop(fill);
        let list: Vec<u32> = list.into_iter().map(|x| x.into_inner()).collect();
        println!("  dependencies: {} ({:.1}s)", list.len(), t0.elapsed().as_secs_f64());
        Deps { start, list }
    }
}

/// Iterate to the fixed point from `start`, one A-life level at a time,
/// lowest first (Fix.solve without ranks or warm starts).
/// Sort the rank log by position: `hidx` holds n + 1 offsets (u64) into
/// `hrec`, whose records are (round u32, value i32) in increasing round
/// order. A position's last record is its final value.
fn index_hist(sv: &Solver, nrec: u64, start: i64) {
    let raw = unsafe { Mmap::map(&File::open(sv.dir.join("hist-raw")).unwrap()).unwrap() };
    let rec = |k: usize| {
        let b = &raw[16 * k..16 * k + 16];
        (u64::from_le_bytes(b[0..8].try_into().unwrap()) as usize, &b[8..16])
    };
    let mut off = vec![0u64; sv.n + 1];
    for k in 0..nrec as usize {
        off[rec(k).0 + 1] += 1;
    }
    for i in 0..sv.n {
        off[i + 1] += off[i];
    }
    let f = OpenOptions::new().read(true).write(true).create(true).truncate(true).open(sv.dir.join("hrec")).unwrap();
    f.set_len(8 * nrec).unwrap();
    let mut out = unsafe { MmapMut::map_mut(&f).unwrap() };
    let mut pos = off.clone();
    for k in 0..nrec as usize {
        let (i, b) = rec(k);
        let p = pos[i] as usize;
        out[8 * p..8 * p + 8].copy_from_slice(b);
        pos[i] += 1;
    }
    out.flush().unwrap();
    // the last record of each position is its final value
    for i in 0..sv.n {
        let v = if off[i + 1] > off[i] {
            let p = off[i + 1] as usize - 1;
            fix::of32(i32::from_le_bytes(out[8 * p + 4..8 * p + 8].try_into().unwrap()))
        } else {
            start
        };
        assert_eq!(v, sv.get(i), "rank log disagrees with the value of position {i}");
    }
    let mut w = BufWriter::new(File::create(sv.dir.join("hidx")).unwrap());
    for o in &off {
        w.write_all(&o.to_le_bytes()).unwrap();
    }
    drop(raw);
    let _ = fs::remove_file(sv.dir.join("hist-raw"));
    println!("  ranks: {nrec} records");
}

pub fn solve(c: &Cfg, sv: &Solver, progs: Programs, start: i64) {
    let t0 = Instant::now();
    let n = sv.n;
    let nb = sv.nb;
    // values in id order while solving (a turn's inputs sit close
    // together), copied to the table's digest order at the end
    let work: Vec<AtomicI32> = (0..n).map(|_| AtomicI32::new(fix::to32(start))).collect();
    let wget = |i: usize| fix::of32(work[i].load(Relaxed));
    let wset = |i: usize, v: i64| work[i].store(fix::to32(v), Relaxed);
    let win = start == c.lose();
    let keep = |a: i64, b: i64| if win { c.best(a, b) } else { c.worst(a, b) };
    let bounds = std::env::var("TCB_NOBOUND").ok().as_deref() != Some("1");
    let lower_is_far = win == c.up();
    let extreme = if win { if c.up() { 1 } else { INF } } else if c.up() { INF } else { NINF };
    let w = jobs().min(nb.max(1));
    let deps = Deps::build(sv, &progs, w);
    let dirty: Vec<AtomicBool> = (0..nb).map(|_| AtomicBool::new(false)).collect();
    let mut evals = 0u64;
    // With ranks (TCB_RANKS=1), each level is solved in rounds: a round
    // reads only the previous round's values, and every change is logged as
    // (position, round, value) for win certificates (WinCert.v).
    let ranks = std::env::var("TCB_RANKS").ok().as_deref() == Some("1");
    let mut hist = ranks.then(|| BufWriter::new(File::create(sv.dir.join("hist-raw")).unwrap()));
    let mut nhist = 0u64;
    for slot in 0..sv.nl {
        let l = sv.life_of_slot(slot) as i64;
        let first = slot * nb;
        let below = bounds && slot > 0 && !sv.pinned;
        let far = |j: usize| -> i64 {
            if below && lower_is_far {
                wget(first - nb + j)
            } else if bounds {
                extreme
            } else {
                i64::MAX
            }
        };
        let fin = |j: usize| wget(first + j) == far(j);
        if below && !lower_is_far {
            for j in 0..nb {
                wset(first + j, keep(wget(first + j), wget(first - nb + j)));
            }
        }
        let value = |x: i64| -> i64 {
            let b = (x >> 5) as usize;
            let u = x & 31;
            if sv.pinned {
                wget(b)
            } else if l - u < 1 {
                c.lose()
            } else {
                wget(((l - u - 1) as usize) * nb + b)
            }
        };
        // Worklist sweeps: a position is evaluated when it is dirty, and a
        // change marks the positions that read it dirty. Its flag is cleared
        // before it is evaluated, so a change to one of its inputs during or
        // after the evaluation always leads to another one; when a sweep
        // finds nothing dirty, every value is a fixed point of its turn.
        for j in 0..nb {
            dirty[j].store(!fin(j), Relaxed);
        }
        let mut sweeps = 0;
        loop {
            sweeps += 1;
            let forward = sweeps & 1 == 1;
            let r: Vec<(u64, Vec<(usize, i64)>)> = std::thread::scope(|sc| {
                let hs: Vec<_> = (0..w)
                    .map(|k| {
                        let (value, fin, progs, keep, dirty, deps, wget, wset) = (&value, &fin, &progs, &keep, &dirty, &deps, &wget, &wset);
                        sc.spawn(move || {
                            let (lo, hi) = chunk(nb, w, k);
                            let (mut nv, mut tv) = (Vec::new(), Vec::new());
                            let mut ev = 0u64;
                            let mut upd: Vec<(usize, i64)> = Vec::new();
                            for x in lo..hi {
                                let j = if forward { x } else { lo + hi - 1 - x };
                                if !dirty[j].swap(false, Relaxed) || fin(j) {
                                    continue;
                                }
                                ev += 1;
                                let v = c.norm(fix::run_packed(c, l, value, progs.prog(j), &mut nv, &mut tv));
                                let old = wget(first + j);
                                let v = keep(old, v);
                                if v != old {
                                    if ranks {
                                        upd.push((j, v));
                                        continue;
                                    }
                                    wset(first + j, v);
                                    for &d in deps.of(j) {
                                        dirty[d as usize].store(true, Relaxed);
                                    }
                                }
                            }
                            (ev, upd)
                        })
                    })
                    .collect();
                hs.into_iter().map(|h| h.join().unwrap()).collect()
            });
            let mut ev = 0u64;
            for (e, upd) in r {
                ev += e;
                for (j, v) in upd {
                    wset(first + j, v);
                    for &d in deps.of(j) {
                        dirty[d as usize].store(true, Relaxed);
                    }
                    let h = hist.as_mut().unwrap();
                    h.write_all(&((first + progs.perm[j] as usize) as u64).to_le_bytes()).unwrap();
                    h.write_all(&(sweeps as u32).to_le_bytes()).unwrap();
                    h.write_all(&fix::to32(v).to_le_bytes()).unwrap();
                    nhist += 1;
                }
            }
            evals += ev;
            if ev == 0 {
                break;
            }
        }
        let good = (0..nb).filter(|&j| wget(first + j) != c.lose()).count();
        println!(
            "  A life {l}: {nb} positions ({good} not lost for the protagonist), {sweeps} sweeps, {evals} evaluations so far ({:.1}s)",
            t0.elapsed().as_secs_f64()
        );
    }
    for slot in 0..sv.nl {
        for (id, &b) in progs.perm.iter().enumerate() {
            sv.set(slot * nb + b as usize, wget(slot * nb + id));
        }
    }
    drop(work);
    if let Some(h) = hist.take() {
        drop(h);
        index_hist(sv, nhist, start);
    }
    let files = progs.maps.len();
    drop(progs);
    for k in 0..files {
        let _ = fs::remove_file(sv.dir.join(format!("prog-{k}")));
    }
    // spot check: the compiled turns agree with direct evaluation
    let bad = AtomicUsize::new(0);
    let next = AtomicUsize::new(0);
    std::thread::scope(|sc| {
        for _ in 0..w {
            sc.spawn(|| loop {
                let i = next.fetch_add(500, Relaxed);
                if i >= n {
                    break;
                }
                let mut lookup = |k: &[u8]| sv.get(sv.id(k).expect("turn start not in the table"));
                let v = c.norm(fix::eval_turn(c, &mut lookup, &fix::of_key(&sv.key_at(i))));
                if v != sv.get(i) {
                    bad.fetch_add(1, Relaxed);
                }
            });
        }
    });
    let bad = bad.into_inner();
    if bad > 0 {
        println!("  SPOT CHECK FAILED at {bad} positions");
    } else {
        println!("  spot check passed");
    }
}

/// A normalised line in one atomic 32-bit word: 16c + b, with INF and
/// NINF as the int32 extremes (c is within +-lmax and b within 0..=BMAX).
fn lenc(v: Line) -> i32 {
    if v.c >= INF {
        i32::MAX
    } else if v.c <= NINF {
        i32::MIN
    } else {
        debug_assert!((0..=fix::BMAX).contains(&v.b) && v.c.abs() < 1 << 26);
        (16 * v.c + v.b) as i32
    }
}
fn ldec(x: i32) -> Line {
    match x {
        i32::MAX => LINF,
        i32::MIN => LNINF,
        _ => Line { c: (x >> 4) as i64, b: (x & 15) as i64 },
    }
}

/// The fixed point in BIG mode (`TCB_BIG=1`): values are lines
/// (`fix::Line`) and every position starts at INF.
///
/// A-safe: each evaluation keeps the componentwise min of the old line and
/// the new one, so values only decrease. When a sweep finds nothing dirty,
/// every evaluated position has v <= F(v): the table justifies itself. A
/// position equal to its value one A-life level down is final, as in
/// `solve` (that value is sound for the higher level by A-life
/// monotonicity).
///
/// B-win: a new line replaces the old one only if it is strictly smaller
/// in B's choice order (`fix::lpick_low`: c + b * bigref, then c, then b).
/// (A componentwise min of two B-win lines would not be an upper bound.)
/// Soundness is by induction on time, not on monotonicity: every line
/// ever stored was computed by one evaluation from lines stored earlier
/// (or from lower A-life levels, finished earlier), each of which is by
/// induction a sound upper bound, and an evaluation turns sound upper
/// bounds into a sound upper bound. The initial INF claims nothing. So every
/// stored line is a true B win, with a finite strategy (follow the
/// evaluation's choices into lines stored earlier). Values only decrease
/// in a total order on a finite set, so this terminates. Stopping at the
/// value one level down (`fin`) only stops improvements.
///
/// Writes c to the table's values and returns b per position (digest
/// order).
pub fn solve_big(c: &Cfg, sv: &Solver, progs: Programs) -> Vec<i8> {
    let t0 = Instant::now();
    let (n, nb) = (sv.n, sv.nb);
    assert!(c.big && !sv.pinned && c.lmax < 1 << 26);
    let up = c.up();
    let lost = if up { LINF } else { LNINF };
    // the old line or the new one (see above)
    let keep = |old: Line, new: Line| if up { fix::lpick_low(c.bigref, old, new) } else { fix::lmin(old, new) };
    let work: Vec<AtomicI32> = (0..n).map(|_| AtomicI32::new(lenc(LINF))).collect();
    let wget = |i: usize| ldec(work[i].load(Relaxed));
    let wset = |i: usize, v: Line| work[i].store(lenc(v), Relaxed);
    let bounds = std::env::var("TCB_NOBOUND").ok().as_deref() != Some("1");
    let w = jobs().min(nb.max(1));
    let deps = Deps::build(sv, &progs, w);
    let dirty: Vec<AtomicBool> = (0..nb).map(|_| AtomicBool::new(false)).collect();
    let mut evals = 0u64;
    for slot in 0..sv.nl {
        let l = sv.life_of_slot(slot) as i64;
        let first = slot * nb;
        // the best value possible: one level down, or at the lowest level
        // A losing (A-safe) or B needing 1 life (B-win)
        let floor = |j: usize| if slot > 0 { wget(first - nb + j) } else if up { Line { c: 1, b: 0 } } else { LNINF };
        let fin = |j: usize| bounds && wget(first + j) == floor(j);
        let value = |x: i64| -> Line {
            let b = (x >> 5) as usize;
            let u = x & 31;
            // (A dead: the guard has decided; as in `solve`)
            if l - u < 1 { lost } else { wget(((l - u - 1) as usize) * nb + b) }
        };
        for j in 0..nb {
            dirty[j].store(!fin(j), Relaxed);
        }
        let mut sweeps = 0;
        loop {
            sweeps += 1;
            let forward = sweeps & 1 == 1;
            let ev: u64 = std::thread::scope(|sc| {
                let hs: Vec<_> = (0..w)
                    .map(|k| {
                        let (value, fin, progs, dirty, deps, wget, wset, keep) = (&value, &fin, &progs, &dirty, &deps, &wget, &wset, &keep);
                        sc.spawn(move || {
                            let (lo, hi) = chunk(nb, w, k);
                            let (mut nv, mut tv) = (Vec::new(), Vec::new());
                            let mut ev = 0u64;
                            for x in lo..hi {
                                let j = if forward { x } else { lo + hi - 1 - x };
                                if !dirty[j].swap(false, Relaxed) || fin(j) {
                                    continue;
                                }
                                ev += 1;
                                let v = c.norm_big(fix::run_packed_big(c, l, value, progs.prog(j), &mut nv, &mut tv));
                                let old = wget(first + j);
                                let v = keep(old, v);
                                if v != old {
                                    wset(first + j, v);
                                    for &d in deps.of(j) {
                                        dirty[d as usize].store(true, Relaxed);
                                    }
                                }
                            }
                            ev
                        })
                    })
                    .collect();
                hs.into_iter().map(|h| h.join().unwrap()).sum()
            });
            evals += ev;
            if ev == 0 {
                break;
            }
        }
        let good = (0..nb).filter(|&j| wget(first + j) != lost).count();
        println!(
            "  A life {l}: {nb} positions ({good} not lost for the protagonist), {sweeps} sweeps, {evals} evaluations so far ({:.1}s)",
            t0.elapsed().as_secs_f64()
        );
    }
    // unmap the programs before the table's values are written
    drop((deps, dirty));
    let Programs { maps, perm, .. } = progs;
    let files = maps.len();
    drop(maps);
    for k in 0..files {
        let _ = fs::remove_file(sv.dir.join(format!("prog-{k}")));
    }
    let mut beta = vec![0i8; n];
    for slot in 0..sv.nl {
        for (id, &b) in perm.iter().enumerate() {
            let v = wget(slot * nb + id);
            sv.set(slot * nb + b as usize, v.c);
            beta[slot * nb + b as usize] = v.b as i8;
        }
    }
    beta
}

/// The spot check of `solve_big`, against direct evaluation (every 500th
/// position): keeping v against F(v) leaves v (A-safe: v <= F(v)
/// componentwise, the certificate condition; B-win: F(v) is not strictly
/// better), except possibly at positions equal to their value one level
/// down; and how often v = F(v).
pub fn spot_check_big(c: &Cfg, sv: &Solver, beta: &[i8]) {
    let (n, nb) = (sv.n, sv.nb);
    let w = jobs().min(nb.max(1));
    let bounds = std::env::var("TCB_NOBOUND").ok().as_deref() != Some("1");
    let line = |i: usize| Line { c: sv.get(i), b: beta[i] as i64 };
    let up = c.up();
    let keep = |old: Line, new: Line| if up { fix::lpick_low(c.bigref, old, new) } else { fix::lmin(old, new) };
    let (bad, badfin, eq, tot) = (AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0));
    let next = AtomicUsize::new(0);
    std::thread::scope(|sc| {
        for _ in 0..w {
            sc.spawn(|| loop {
                let i = next.fetch_add(500, Relaxed);
                if i >= n {
                    break;
                }
                let mut lookup = |k: &[u8]| line(sv.id(k).expect("turn start not in the table"));
                let f = c.norm_big(fix::eval_turn_big(c, &mut lookup, &fix::of_key(&sv.key_at(i))));
                let v = line(i);
                tot.fetch_add(1, Relaxed);
                if f == v {
                    eq.fetch_add(1, Relaxed);
                }
                if keep(v, f) != v {
                    if bounds && i >= nb && line(i - nb) == v {
                        badfin.fetch_add(1, Relaxed);
                    } else {
                        let k = bad.fetch_add(1, Relaxed);
                        if k < 5 {
                            println!("  spot check: position {i}: value {v:?}, one step {f:?}");
                        }
                    }
                }
            });
        }
    });
    let (bad, badfin, eq, tot) = (bad.into_inner(), badfin.into_inner(), eq.into_inner(), tot.into_inner());
    println!("  spot check: {tot} positions, v = F(v) at {eq}, keeping v fails at {bad} (and at {badfin} final from the level below)");
    if bad > 0 {
        println!("  SPOT CHECK FAILED at {bad} positions");
    } else {
        println!("  spot check passed");
    }
}

/// BIG-mode statistics: positions with a BIG Walker, the distribution of
/// b, and how many BIG positions have c >= 20; at every A-life level and at
/// A life 20, with a breakdown at A life 20 by B's Walker and Thopters.
pub fn big_stats(c: &Cfg, sv: &Solver, beta: &[i8]) {
    let nb = sv.nb;
    let k = c.big_k();
    let st = |b: usize| fix::of_key(&fix::with_life(sv.base_key(b), 20));
    let isbig: Vec<bool> = (0..nb).map(|b| st(b).side_a.bf.iter().any(|w| w.counters == k)).collect();
    let nbig = isbig.iter().filter(|&&x| x).count();
    println!("BIG: K = {k}; {nbig} of {nb} bases have a BIG Walker");
    let up = c.up();
    let lose = c.lose();
    // the position's line at n = 0 settles B life 20 in the protagonist's
    // favour
    let at20 = |v: i64| if up { v <= 20 } else { v >= 20 };
    let (lbl20, lblinf) = if up { ("c <= 20", "B wins with any life") } else { ("c >= 20 (or any)", "safe at any B life") };
    for (name, lo) in [("all levels", 0), ("A life 20", sv.nl - 1)] {
        let mut hist = [0u64; fix::BMAX as usize + 1];
        let (mut pos, mut lost, mut inf, mut c20) = (0u64, 0u64, 0u64, 0u64);
        let (mut nonbig, mut nonbig_lost, mut nonbig_beta) = (0u64, 0u64, 0u64);
        for slot in lo..sv.nl {
            for b in 0..nb {
                let i = slot * nb + b;
                let v = sv.get(i);
                if !isbig[b] {
                    nonbig += 1;
                    nonbig_beta += (beta[i] != 0) as u64;
                    nonbig_lost += (v == lose) as u64;
                    continue;
                }
                pos += 1;
                if v == lose {
                    lost += 1;
                    continue;
                }
                if (!up && v >= INF) || (up && v <= 1 && beta[i] == 0) {
                    inf += 1;
                } else {
                    hist[beta[i] as usize] += 1;
                }
                c20 += at20(v) as u64;
            }
        }
        let h: Vec<String> = hist.iter().enumerate().map(|(b, x)| format!("{b}:{x}")).collect();
        println!(
            "BIG ({name}): {pos} BIG positions, {lost} lost for the protagonist, {inf} {lblinf}; beta of the rest {}; {lbl20} at {c20}",
            h.join(" ")
        );
        println!("BIG ({name}): {nonbig} non-BIG positions, {nonbig_lost} lost, {nonbig_beta} with beta != 0");
    }
    // A life 20, BIG positions: (positions, lost, settled at 20) by B's
    // Walker and by B's Thopters
    let slot = sv.nl - 1;
    let huge = c.ot + 1;
    let mut by_w: std::collections::BTreeMap<String, (u64, u64, u64)> = Default::default();
    let mut by_t: std::collections::BTreeMap<u32, (u64, u64, u64)> = Default::default();
    for b in 0..nb {
        if !isbig[b] {
            continue;
        }
        let v = sv.get(slot * nb + b);
        let s = &st(b);
        let bw = match s.side_b.bf.first() {
            None => "none".to_string(),
            Some(w) if w.counters >= huge => "huge".to_string(),
            Some(w) => format!("{:02}", w.counters),
        };
        let bt = s.side_b.thop_u + s.side_b.thop_t;
        for e in [by_w.entry(bw).or_default(), by_t.entry(bt).or_default()] {
            e.0 += 1;
            if v == lose {
                e.1 += 1;
            } else if at20(v) {
                e.2 += 1;
            }
        }
    }
    println!("BIG at A life 20, by B's Walker: (positions, lost, {lbl20})");
    for (k, v) in &by_w {
        println!("  B Walker {k}: {v:?}");
    }
    println!("BIG at A life 20, by B's Thopters: (positions, lost, {lbl20})");
    for (k, v) in &by_t {
        println!("  B Thopters {k}: {v:?}");
    }
}

pub fn save_meta(sv: &Solver, header: &[(String, String)]) {
    let mut f = BufWriter::new(File::create(sv.dir.join("meta")).unwrap());
    writeln!(f, "TCBFIX 3").unwrap();
    writeln!(f, "n={}", sv.n).unwrap();
    writeln!(f, "nb={}", sv.nb).unwrap();
    writeln!(f, "nl={}", sv.nl).unwrap();
    for (k, v) in header {
        writeln!(f, "{k}={v}").unwrap();
    }
}
