//! Tests of certified play, shared by the native tool (`cert-tool`) and
//! the WASM build (`cert_selfplay`): self-play of certified B against
//! several A players, and the trace of the checker's search that
//! `test/cert-ocaml.ml` reproduces with the extracted Rocq model.

use crate::cert::{self, Failure, Table};
use crate::model::*;
use crate::search::Search;
use crate::walk;
use std::fmt::Write;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Adversary {
    /// Uniformly random legal moves.
    Random,
    /// Random, but two draws in three avoid Pass and pumps when there is
    /// another move (as `rsolver walk ... bias`), to reach more combat.
    RandomBias,
    /// The site's heuristic search (`search.rs`) with this budget in ms,
    /// and one decision in eight random.
    Search(u32),
    /// Maximise the next record B must play from: by rank, then value.
    Rank,
    /// The same, by value, then rank.
    Val,
}

impl Adversary {
    pub fn parse(s: &str) -> Option<Adversary> {
        Some(match s {
            "random" => Adversary::Random,
            "bias" => Adversary::RandomBias,
            "rank" => Adversary::Rank,
            "val" => Adversary::Val,
            _ => Adversary::Search(s.strip_prefix("search")?.parse().ok()?),
        })
    }
    pub fn code(n: u32) -> Option<Adversary> {
        Some(match n {
            0 => Adversary::Random,
            1 => Adversary::RandomBias,
            2 => Adversary::Rank,
            3 => Adversary::Val,
            n if n >= 1000 => Adversary::Search(n - 1000),
            _ => return None,
        })
    }
}

fn next(x: &mut u64) -> u64 {
    *x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    *x >> 33
}

/// The worst next record A can force for B, playing against B's
/// certified moves: `check_win`'s search, where A's nodes take the
/// maximum of their children and B's nodes follow the first child that
/// passes (B's actual move). `None` exactly when `check_win` fails.
/// Scores compare as (primary, secondary); a B win scores lowest.
fn worst(t: &Table, adv: Adversary, r: u32, fuel: u32, root: bool, s: &State) -> Option<(i64, i64)> {
    if fuel == 0 {
        return None;
    }
    match winner(s) {
        Some(Player::B) => Some((i64::MIN, i64::MIN)),
        Some(Player::A) => None,
        None => {
            if !root && cert::is_turn_start(s) {
                let k = t.key(s);
                match t.below(&k, r) {
                    Some(r2) if r2 < r => match t.lookup(&k, r2) {
                        Some(v) if v <= s.side_b.life => {
                            let (rk, val) = t.pick_record(s)?;
                            let (rk, val) = (rk as i64, val as i64);
                            Some(if adv == Adversary::Val { (val, rk) } else { (rk, val) })
                        }
                        _ => None,
                    },
                    _ => None,
                }
            } else if t.huge_event(s) {
                None
            } else {
                let child = |m: &Move| {
                    let s2 = step(s, m);
                    if t.too_many(&s2) { None } else { worst(t, adv, r, fuel - 1, false, &s2) }
                };
                let ms = moves(s);
                match to_move(s) {
                    Player::B => ms.iter().find_map(child),
                    Player::A => {
                        let mut best = None;
                        for m in &ms {
                            let v = child(m)?;
                            best = best.max(Some(v));
                        }
                        best
                    }
                }
            }
        }
    }
}

#[derive(Default, Debug, Clone)]
pub struct Summary {
    pub games: u64,
    pub b_wins: u64,
    pub turns_total: u64,
    pub turns_max: u64,
    pub decisions_a: u64,
    pub decisions_b: u64,
    pub plans: u64,
    pub nodes: u64,
    pub segments: u64,
    pub record_life: u64,
    pub failures: Vec<String>,
    /// Game records "starter lifeA lifeB m1 m2 ..." (move indices).
    pub records: Vec<String>,
}

impl Summary {
    pub fn to_json(&self) -> String {
        format!(
            "{{\"games\":{},\"bWins\":{},\"turnsTotal\":{},\"turnsMax\":{},\"decisionsA\":{},\"decisionsB\":{},\"plans\":{},\"nodes\":{},\"segments\":{},\"recordLife\":{},\"failures\":[{}]}}",
            self.games,
            self.b_wins,
            self.turns_total,
            self.turns_max,
            self.decisions_a,
            self.decisions_b,
            self.plans,
            self.nodes,
            self.segments,
            self.record_life,
            self.failures.iter().map(|f| format!("{f:?}")).collect::<Vec<_>>().join(",")
        )
    }
    pub fn add(&mut self, o: &Summary) {
        self.games += o.games;
        self.b_wins += o.b_wins;
        self.turns_total += o.turns_total;
        self.turns_max = self.turns_max.max(o.turns_max);
        self.decisions_a += o.decisions_a;
        self.decisions_b += o.decisions_b;
        self.plans += o.plans;
        self.nodes += o.nodes;
        self.segments += o.segments;
        self.record_life += o.record_life;
        self.failures.extend(o.failures.iter().cloned());
        self.records.extend(o.records.iter().cloned());
    }
}

/// A's move: an index into `moves` of the last state.
fn a_move(t: &Table, adv: Adversary, states: &[State], mvs: &[Move], rng: &mut u64, search: &mut Search) -> Result<usize, String> {
    let s = states.last().unwrap();
    let ms = moves(s);
    Ok(match adv {
        Adversary::Random => next(rng) as usize % ms.len(),
        Adversary::RandomBias => {
            let others: Vec<usize> = (0..ms.len()).filter(|&i| !matches!(ms[i], Move::Pass | Move::Pump(_))).collect();
            if !others.is_empty() && next(rng) % 3 != 0 {
                others[next(rng) as usize % others.len()]
            } else {
                next(rng) as usize % ms.len()
            }
        }
        // One decision in eight is random, so that games differ.
        Adversary::Search(budget) => {
            if next(rng) % 8 == 0 {
                next(rng) as usize % ms.len()
            } else {
                search.think(s, budget as f64, 40).index
            }
        }
        Adversary::Rank | Adversary::Val => {
            // Every A move must stay inside the certificate: check them all.
            let mut stats = cert::Stats::default();
            let (seg, _) = t.segment_at(states, mvs, &mut stats).map_err(|e| format!("A to move outside the certificate: {e:?}"))?;
            let mut best: Option<((i64, i64), Vec<usize>)> = None;
            for (i, m) in ms.iter().enumerate() {
                let mut sg = seg.clone();
                t.follow(&mut sg, m).map_err(|e| format!("A's move {} leaves the certificate: {e}", walk::mv(m)))?;
                let v = worst(t, adv, sg.rank, sg.fuel, false, &sg.abs)
                    .ok_or_else(|| format!("A's move {} leaves the certificate", walk::mv(m)))?;
                match &mut best {
                    Some((bv, is)) if *bv == v => is.push(i),
                    Some((bv, _)) if *bv > v => {}
                    _ => best = Some((v, vec![i])),
                }
            }
            let is = best.unwrap().1;
            is[next(rng) as usize % is.len()]
        }
    })
}

/// One game from the B-first opening: certified B against `adv`. Every B
/// decision goes through `cert::plan`, replaying the game so far, as the
/// site's worker does.
pub fn play_game(t: &Table, adv: Adversary, seed: u64, search: &mut Search) -> Summary {
    let mut sum = Summary { games: 1, ..Default::default() };
    let mut rng = seed;
    let mut states = vec![init(Player::B)];
    let mut mvs: Vec<Move> = vec![];
    let mut turns = 0u64;
    let mut rec: Vec<usize> = vec![1, 20, 20];
    let fail = |sum: &mut Summary, msg: String| {
        sum.failures.push(format!("seed {seed}: {msg}"));
    };
    loop {
        let s = states.last().unwrap().clone();
        if let Some(w) = winner(&s) {
            if w == Player::B {
                sum.b_wins = 1;
            } else {
                fail(&mut sum, "A won".into());
            }
            break;
        }
        if mvs.len() > 200_000 || turns > 2000 {
            fail(&mut sum, "game did not end".into());
            break;
        }
        if to_move(&s) == Player::B {
            match cert::plan(t, &states, &mvs) {
                Ok(p) => {
                    sum.plans += 1;
                    sum.nodes += p.stats.nodes;
                    sum.segments += p.stats.segments;
                    sum.record_life += p.stats.record_life;
                    if p.moves.is_empty() {
                        fail(&mut sum, "empty plan".into());
                        break;
                    }
                    for i in p.moves {
                        rec.push(i);
                        let cur = states.last().unwrap();
                        let m = moves(cur)[i].clone();
                        let n = step(cur, &m);
                        if cert::is_turn_start(&n) {
                            turns += 1;
                        }
                        states.push(n);
                        mvs.push(m);
                        sum.decisions_b += 1;
                    }
                }
                Err(Failure::Uncovered(m)) => {
                    let at = t.diagnose(&states, &mvs);
                    fail(&mut sum, format!("uncovered: {m} (lost after move {at:?})"));
                    break;
                }
                Err(Failure::Bug(m)) => {
                    fail(&mut sum, format!("bug: {m}"));
                    break;
                }
            }
        } else {
            match a_move(t, adv, &states, &mvs, &mut rng, search) {
                Ok(i) => {
                    rec.push(i);
                    let m = moves(&s)[i].clone();
                    let n = step(&s, &m);
                    if cert::is_turn_start(&n) {
                        turns += 1;
                    }
                    states.push(n);
                    mvs.push(m);
                    sum.decisions_a += 1;
                }
                Err(e) => {
                    fail(&mut sum, e);
                    break;
                }
            }
        }
    }
    sum.turns_total = turns;
    sum.turns_max = turns;
    sum.records.push(rec.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" "));
    sum
}

pub fn selfplay(t: &Table, adv: Adversary, games: u64, seed: u64) -> Summary {
    let mut all = Summary::default();
    for g in 0..games {
        let mut search = Search::new();
        let mut x = seed ^ g.wrapping_mul(0x9e37_79b9_7f4a_7c15);
        next(&mut x);
        all.add(&play_game(t, adv, x, &mut search));
    }
    all
}

// ---- the checker's search, as text (compared with test/cert-ocaml.ml) ----

/// The nodes `check_win` visits from record `j`, in order, up to `cap`
/// lines, then `R j <result>`. At a node that searches moves: the state
/// and all its moves; at a turn start below the root: the rank `below`
/// names and the value `lookup` gives; terminal cases by tag.
pub fn trace_record(t: &Table, j: usize, cap: usize) -> String {
    let mut tr = Tracer { out: String::new(), lines: 0, cap: if cap == 0 { usize::MAX } else { cap } };
    let ok = match t.record_state(j) {
        Some(s) => trace(t, t.rank_of(j), t.fuel, true, &s, &mut tr),
        None => false,
    };
    if cap == 0 {
        use md5::{Digest, Md5};
        let h: String = Md5::digest(tr.out.as_bytes()).iter().map(|c| format!("{c:02x}")).collect();
        format!("R {j} {ok} {} {h}\n", tr.lines)
    } else {
        writeln!(tr.out, "R {j} {ok}").unwrap();
        tr.out
    }
}

/// Every position along a game record with its legal moves, then "G"
/// (as `test/cert_ocaml.ml replay`).
pub fn replay_text(rec: &[u32]) -> String {
    let mut out = String::new();
    let (states, _) = crate::replay_all(rec);
    for s in &states {
        writeln!(out, "{}", walk::state(s)).unwrap();
        writeln!(out, "M {}", moves(s).iter().map(walk::mv).collect::<Vec<_>>().join(" ")).unwrap();
    }
    out.push_str("G\n");
    out
}

struct Tracer {
    out: String,
    lines: usize,
    cap: usize,
}

impl Tracer {
    fn emit(&mut self, line: &str) {
        if self.lines < self.cap {
            self.out.push_str(line);
            self.out.push('\n');
        }
        self.lines += 1;
    }
}

fn trace(t: &Table, r: u32, fuel: u32, root: bool, s: &State, tr: &mut Tracer) -> bool {
    if fuel == 0 {
        tr.emit("F");
        return false;
    }
    match winner(s) {
        Some(p) => {
            tr.emit(if p == Player::A { "OA" } else { "OB" });
            p == Player::B
        }
        None => {
            if !root && cert::is_turn_start(s) {
                let k = t.key(s);
                let b = t.below(&k, r);
                let v = b.and_then(|r2| if r2 < r { t.lookup(&k, r2) } else { None });
                let fmt = |o: Option<u32>| o.map_or("-".to_string(), |x| x.to_string());
                tr.emit(&format!("L {} {} {}", fmt(b), fmt(v), s.side_b.life));
                matches!(v, Some(v) if v <= s.side_b.life)
            } else if t.huge_event(s) {
                tr.emit("H");
                false
            } else {
                let ms = moves(s);
                tr.emit(&walk::state(s));
                tr.emit(&format!("M {}", ms.iter().map(walk::mv).collect::<Vec<_>>().join(" ")));
                let child = |m: &Move, tr: &mut Tracer| {
                    let s2 = step(s, m);
                    if t.too_many(&s2) {
                        tr.emit("T");
                        false
                    } else {
                        trace(t, r, fuel - 1, false, &s2, tr)
                    }
                };
                match to_move(s) {
                    Player::B => ms.iter().any(|m| child(m, tr)),
                    Player::A => !ms.is_empty() && ms.iter().all(|m| child(m, tr)),
                }
            }
        }
    }
}

