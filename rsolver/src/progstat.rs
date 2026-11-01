//! Measurements for the program encoding: compile turns at turn starts
//! sampled by random play under a configuration, and report how many words
//! each candidate change to the format would save.

use crate::fix::{self, Cfg, SENT};
use crate::model::*;
use rustc_hash::FxHashMap as HashMap;

struct Node {
    h: i32,
    kids: Vec<(i32, i32)>,
}

fn parse(prog: &[i32], nodes: usize) -> Vec<Node> {
    let mut pc = 0;
    (0..nodes)
        .map(|_| {
            let h = prog[pc];
            let cnt = ((h >> 1) & 0x7fff) as usize;
            let kids = (0..cnt).map(|i| (prog[pc + 1 + 2 * i], prog[pc + 2 + 2 * i])).collect();
            pc += 1 + 2 * cnt;
            Node { h, kids }
        })
        .collect()
}

#[derive(Default)]
struct Tally {
    turns: u64,
    words: u64,
    nodes: u64,
    kids: u64,
    kid_d0: u64,
    kid_kind: [u64; 3],
    single: u64,
    guard: u64,
    consed_nodes: u64,
    consed_words: u64,
    flat_words: u64,
    packed: u64,
    packed_consed: u64,
}

fn tally(t: &mut Tally, ns: &[Node]) {
    t.turns += 1;
    t.nodes += ns.len() as u64;
    let words = |n: &Node| 1 + 2 * n.kids.len() as u64;
    t.words += ns.iter().map(words).sum::<u64>();
    for n in ns {
        if (n.h >> 16) > 0 {
            t.guard += 1;
        }
        if n.kids.len() == 1 {
            t.single += 1;
        }
        for &(_, kd) in &n.kids {
            t.kids += 1;
            t.kid_kind[(kd & 3) as usize] += 1;
            if kd >> 2 == 0 {
                t.kid_d0 += 1;
            }
        }
    }
    // hash-consing: identical nodes (after renaming children) share one copy
    let mut canon: Vec<i32> = vec![0; ns.len()];
    let mut seen: HashMap<(i32, Vec<(i32, i32)>), i32> = HashMap::default();
    for (i, n) in ns.iter().enumerate() {
        let mut ks: Vec<(i32, i32)> = n.kids.iter().map(|&(x, kd)| if kd & 3 == 1 { (canon[x as usize], kd) } else { (x, kd) }).collect();
        ks.sort();
        ks.dedup();
        let next = seen.len() as i32;
        let id = *seen.entry((n.h, ks.clone())).or_insert_with(|| {
            t.consed_words += 1 + 2 * ks.len() as u64;
            next
        });
        canon[i] = id;
    }
    t.consed_nodes += seen.len() as u64;
    // flattening: a child node used once, with no life change, no guard and
    // the same operator, merges into its parent
    let mut uses = vec![0u32; ns.len()];
    for n in ns {
        for &(x, kd) in &n.kids {
            if kd & 3 == 1 {
                uses[x as usize] += 1;
            }
        }
    }
    let mut saved = 0u64;
    for n in ns {
        for &(x, kd) in &n.kids {
            if kd == 1 {
                let c = &ns[x as usize];
                if uses[x as usize] == 1 && (c.h >> 16) == 0 && (c.h & 1) == (n.h & 1) && c.kids.len() > 1 {
                    saved += 3; // the child's header and the parent's reference
                }
            }
        }
    }
    t.flat_words += t.words.min(saved);
    // the packed format: guard nodes folded into the reference to them; a
    // reference is one word unless it carries d, u or a guard
    let is_guard = |n: &Node| (n.h >> 16) > 0 && n.kids.len() == 1;
    let cost = |x: i32, kd: i32| -> (u64, (i32, i32, i32)) {
        let (mut x, mut kd, mut g) = (x, kd, 0);
        if kd & 3 == 1 && is_guard(&ns[x as usize]) {
            g = ns[x as usize].h >> 16;
            (x, kd) = ns[x as usize].kids[0];
        }
        let ext = kd >> 2 != 0 || g != 0 || (kd & 3 == 2 && x & 31 != 0);
        (if ext { 2 } else { 1 }, (x, kd, g))
    };
    let root = ns.len() - 1;
    let mut seen2: HashMap<(i32, Vec<(i32, i32, i32)>), i32> = HashMap::default();
    let mut canon2: Vec<i32> = vec![0; ns.len()];
    for (i, n) in ns.iter().enumerate() {
        if is_guard(n) && i != root {
            continue;
        }
        let mut w = 1;
        let mut ks = vec![];
        for &(x, kd) in &n.kids {
            let (c, (x2, kd2, g)) = cost(x, kd);
            w += c;
            ks.push((if kd2 & 3 == 1 { canon2[x2 as usize] } else { x2 }, kd2, g));
        }
        t.packed += w;
        ks.sort();
        ks.dedup();
        let next = seen2.len() as i32;
        let id = *seen2.entry((n.h & 1, ks)).or_insert_with(|| {
            t.packed_consed += w;
            next
        });
        canon2[i] = id;
    }
}

/// `samples` turn starts from random play (seeded), each compiled with a
/// stand-in target numbering.
fn stand_in(c: &Cfg) -> impl Fn(&State) -> i64 + '_ {
    move |s: &State| -> i64 {
        let u = SENT as i64 - s.side_a.life as i64;
        if u >= 20 {
            31
        } else {
            let d = fix::digest_key(&fix::base_of(&fix::key_gen(c.full_a, s)));
            ((d & 0x3ff_ffff) << 5) | u
        }
    }
}

/// Every `every`-th base of a solved table (its `keys` file).
pub fn run_table(c: &Cfg, dir: &str, every: usize) {
    let keys = std::fs::read(std::path::Path::new(dir).join("keys")).unwrap();
    let by_key = std::env::var("TCB_RANK").ok().as_deref() == Some("key");
    let mut order: Vec<&[u8]> = keys.chunks(32).map(|r| &r[1..1 + r[0] as usize]).collect();
    order.sort();
    let rank: HashMap<i64, i64> = order.iter().enumerate().map(|(i, k)| (fix::digest_key(k), i as i64)).collect();
    let si = stand_in(c);
    let tgt = |s: &State| -> i64 {
        let v = si(s);
        if !by_key || v == 31 {
            v
        } else {
            let d = fix::digest_key(&fix::base_of(&fix::key_gen(c.full_a, s)));
            (rank[&d] << 5) | (v & 31)
        }
    };
    let mut t = Tally::default();
    let (mut pb, mut tb, mut ntt) = (0u64, 0u64, 0u64);
    let (mut ct, mut pt) = (0f64, 0f64);
    for r in keys.chunks(32).step_by(every) {
        let base = &r[1..1 + r[0] as usize];
        let st = fix::of_key(&fix::with_life(base, SENT));
        let t1 = std::time::Instant::now();
        let (prog, nn) = fix::compile(c, &tgt, &st);
        ct += t1.elapsed().as_secs_f64();
        let t1 = std::time::Instant::now();
        let p = fix::pack(&prog, nn, c.big);
        pt += t1.elapsed().as_secs_f64();
        tally(&mut t, &parse(&prog, nn));
        let nt = fix::packed_targets(&p).count() as u64;
        // bytes of the turn-start table: its varint differences
        let mut tbytes = 0;
        let mut x = 0;
        for t in fix::packed_targets(&p) {
            let mut dd = (t - x) as u64;
            x = t;
            loop {
                tbytes += 1;
                if dd < 0x80 {
                    break;
                }
                dd >>= 7;
            }
        }
        pb += p.len() as u64;
        tb += tbytes;
        ntt += nt;
    }
    report(&t);
    println!("compile {ct:.2}s, pack {pt:.2}s");
    println!("packed bytes {pb} ({:.0}/turn, {:.1}% of words*4); turn-start tables {tb} bytes ({:.1}%), {:.1} targets/turn", pb as f64 / t.turns as f64, 100.0 * pb as f64 / (4 * t.words) as f64, 100.0 * tb as f64 / pb as f64, ntt as f64 / t.turns as f64);
}

pub fn run(c: &Cfg, s0: &State, samples: usize, seed: u64) {
    let tgt = stand_in(c);
    let mut t = Tally::default();
    let mut x = seed;
    let next = |x: u64| x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    let mut s = s0.clone();
    let mut seen: HashMap<Vec<u8>, ()> = HashMap::default();
    while t.turns < samples as u64 {
        let ms = c.moves_for(&s);
        let restart = winner(&s).is_some() || ms.is_empty() || c.too_many(&s);
        if restart {
            s = s0.clone();
            continue;
        }
        if is_turn_start(&s) {
            let k = fix::key_gen(c.full_a, &s);
            let base = fix::base_of(&k);
            if seen.insert(base.clone(), ()).is_none() {
                let st = fix::of_key(&fix::with_life(&base, SENT));
                let (prog, nn) = fix::compile(c, &tgt, &st);
                tally(&mut t, &parse(&prog, nn));
            }
        }
        x = next(x);
        let m = &ms[((x >> 33) % ms.len() as u64) as usize];
        if c.huge_event(&s, m) {
            s = s0.clone();
            continue;
        }
        let mut s2 = step(&s, m);
        c.clamp(&mut s2);
        s = s2;
    }
    report(&t);
}

fn report(t: &Tally) {
    let pct = |a: u64, b: u64| 100.0 * a as f64 / b.max(1) as f64;
    println!("{} turns, {} words ({:.0}/turn), {} nodes ({:.0}/turn)", t.turns, t.words, t.words as f64 / t.turns as f64, t.nodes, t.nodes as f64 / t.turns as f64);
    println!("children: {} ({:.1}/node); d = 0: {:.1}%; const/node/turn-start: {:.1}/{:.1}/{:.1}%", t.kids, t.kids as f64 / t.nodes as f64, pct(t.kid_d0, t.kids), pct(t.kid_kind[0], t.kids), pct(t.kid_kind[1], t.kids), pct(t.kid_kind[2], t.kids));
    println!("single-child nodes {:.1}%, guard nodes {:.1}%", pct(t.single, t.nodes), pct(t.guard, t.nodes));
    let one_word = t.nodes + t.kids + (t.kids - t.kid_d0);
    println!("one-word children (second word only when d != 0): {} words ({:.1}%)", one_word, pct(one_word, t.words));
    println!("hash-consed: {} nodes, {} words ({:.1}%)", t.consed_nodes, t.consed_words, pct(t.consed_words, t.words));
    println!("packed (guards folded, one-word references): {} words ({:.1}%); also hash-consed: {} ({:.1}%)", t.packed, pct(t.packed, t.words), t.packed_consed, pct(t.packed_consed, t.words));
    println!("flattening single-use same-operator children saves {} words ({:.1}%)", t.flat_words, pct(t.flat_words, t.words));
}

/// Size of each turn's search tree without memoisation (capped), against
/// the memoised node count: what a checker without a memo table would
/// visit.
pub fn tree_sizes(c: &Cfg, dir: &str, every: usize) {
    fn count(c: &Cfg, s: &State, root: bool, budget: &mut u64) -> u64 {
        if *budget == 0 {
            return 0;
        }
        *budget -= 1;
        if winner(s).is_some() || (!root && is_turn_start(s)) {
            return 1;
        }
        let mut n = 1;
        let one = to_move(s) == c.prot && std::env::var("TCB_ONEB").is_ok();
        for m in c.moves_for(s) {
            if one && n > 1 {
                break;
            }
            if c.huge_event(s, &m) {
                continue;
            }
            let mut s2 = step(s, &m);
            c.clamp(&mut s2);
            if c.too_many(&s2) {
                continue;
            }
            n += count(c, &s2, false, budget);
        }
        n
    }
    let keys = std::fs::read(std::path::Path::new(dir).join("keys")).unwrap();
    let mut sizes = vec![];
    for r in keys.chunks(32).step_by(every) {
        let base = &r[1..1 + r[0] as usize];
        let st = fix::of_key(&fix::with_life(base, 20));
        let mut budget = 10_000_000u64;
        sizes.push(count(c, &st, true, &mut budget));
    }
    sizes.sort();
    let n = sizes.len();
    let total: u64 = sizes.iter().sum();
    println!("{n} turns: tree nodes mean {:.0}, median {}, p90 {}, p99 {}, max {} (cap 1e7)", total as f64 / n as f64, sizes[n / 2], sizes[n * 9 / 10], sizes[n * 99 / 100], sizes[n - 1]);
}
