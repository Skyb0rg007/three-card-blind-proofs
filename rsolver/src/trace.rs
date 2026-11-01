//! `rsolver trace`: follow the deciding play of a saved table from a start
//! position down to the leaves that decide it, and tally those leaves by
//! the rule that decided them (a real game end, or one of the abstraction's
//! rules). A diagnostic only; nothing here feeds a table.
//!
//! Two traces:
//!
//! - **A-safe table, B life L where A is not safe** (`trace DIR A ...`):
//!   B's winning replies against every A move. The table must be solved
//!   with `TCB_RANKS=1`, so that each position's history says in which
//!   round (of its A-life level) it first became lost at L. A turn that
//!   became lost at round r is followed only into turn starts of the same
//!   level lost by round r - 1, or into lower levels, so the trace is
//!   well founded and every branch ends at a leaf.
//! - **B-win table, B life L where B can't win** (`trace DIR B ...`):
//!   A's escaping replies against every B move. This is co-inductive: the
//!   trace stops at turn starts it has already seen, so it ends either at a
//!   decided leaf or by closing a cycle (a real escape, within the
//!   abstraction). With `TCB_BIG=1` (a saved BIG B-win table, with its
//!   `beta` file) the trace keeps the BIG Walker's exact excess n.
//! - **BIG A-safe table** (`TCB_BIG=1`, solved with `TCB_RANKS=1`): as the
//!   A-safe trace, at the BIG Walker's exact excess n. A turn start is lost
//!   at (L, n) when c + b n < L, and its round is the first logged line
//!   with c + b n < L (lines only decrease). Each turn is searched per n,
//!   so a B win that only the line arithmetic gives (the componentwise min
//!   at B's nodes, or a clamp of c or b) shows up as "not confirmed".
//!
//! Inside a turn the trace searches the model directly (as `eval_turn`),
//! reading turn starts from the table. Where the traced side has several
//! good moves, it takes the one whose subtree in this turn needs the
//! fewest abstraction rules (the smallest leaf mask below), so abstraction
//! leaves show up only where this turn can't avoid them.

use crate::fix::{self, Cfg, F_CREATE, F_HIT, F_PUMP, F_SECOND, INF, NINF};
use crate::model::*;
use crate::walk;
use memmap2::Mmap;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::fs::File;
use std::path::Path;

// Leaf kinds, as bits of a mask; a larger bit is a worse leaf for the
// traced side's choice (abstraction rules above real ends).
const K_ADEAD: u32 = 1 << 0; // A's life reaches 0 (real)
const K_BDEAD: u32 = 1 << 1; // B's life reaches 0 (real)
const K_SAME: u32 = 1 << 2; // a turn start at the same A-life level
const K_BELOW: u32 = 1 << 3; // a turn start at a lower A-life level
const K_HUGE: u32 = 1 << 8; // Cfg::huge_event: a huge Walker unblocked
const K_MANY: u32 = 1 << 9; // Cfg::too_many: opponent's Thopters above ott
const K_LMAX: u32 = 1 << 10; // a turn start needing more than lmax
const K_SECOND: u32 = 1 << 11; // BIG B-win: a second BIG Walker
const K_NBOUND: u32 = 1 << 12; // BIG: n past TCB_TRACE_NMAX, read from the line
const K_HUGE_DIE: u32 = 1 << 13; // huge_event: a huge attacker's blockers total ot + 1
const K_HUGE_BLK: u32 = 1 << 14; // huge_event: a huge blocker against a Walker of ot + 1
const NK: usize = 15;
const NAMES: [&str; NK] = [
    "A dead (real)",
    "B dead (real)",
    "turn start, same level",
    "turn start, level below",
    "-",
    "-",
    "-",
    "-",
    "huge_event: huge Walker unblocked",
    "too_many (opponent Thopters > ott)",
    "lmax clamp",
    "F_SECOND (second BIG Walker)",
    "BIG n past the trace bound",
    "huge_event: huge attacker, blockers total ot+1",
    "huge_event: huge blocker, attacker ot+1",
];

// Annotations, counted over the witness's nodes and edges.
const A_CAP: usize = 0; // a protagonist node where the cap removed a pump
const A_TCUT: usize = 1; // an edge where the protagonist's Thopters were cut to tt
const A_SAT: usize = 2; // an edge where an opponent Walker was clamped to ot + 1
const NA: usize = 3;
const ANAMES: [&str; NA] = [
    "protagonist node where its Walker cap removed a pump",
    "edge where the protagonist's Thopters were cut to tt",
    "edge where an opponent Walker saturated at ot + 1",
];

/// A saved table: dig, keys, vals, and optionally the rank history
/// (hidx, hrec) or BIG's beta.
pub struct Table {
    nb: usize,
    pub nl: usize,
    dig: Mmap,
    keys: Mmap,
    vals: Mmap,
    hist: Option<(Mmap, Mmap)>,
    beta: Option<Mmap>,
}

fn map(p: &Path) -> Mmap {
    unsafe { Mmap::map(&File::open(p).unwrap_or_else(|e| panic!("{}: {e}", p.display()))).unwrap() }
}

impl Table {
    pub fn open(dir: &Path) -> Table {
        let dig = map(&dir.join("dig"));
        let keys = map(&dir.join("keys"));
        let vals = map(&dir.join("vals"));
        let nb = dig.len() / 8;
        let n = vals.len() / 4;
        assert!(nb > 0 && n % nb == 0 && keys.len() == 32 * nb);
        let hist = dir.join("hidx").exists().then(|| (map(&dir.join("hidx")), map(&dir.join("hrec"))));
        let beta = dir.join("beta").exists().then(|| map(&dir.join("beta")));
        Table { nb, nl: n / nb, dig, keys, vals, hist, beta }
    }
    fn digest(&self, b: usize) -> i64 {
        i64::from_le_bytes(self.dig[8 * b..8 * b + 8].try_into().unwrap())
    }
    fn find(&self, d: i64) -> Option<usize> {
        let (mut lo, mut hi) = (0, self.nb);
        while lo < hi {
            let m = (lo + hi) / 2;
            match self.digest(m).cmp(&d) {
                std::cmp::Ordering::Less => lo = m + 1,
                std::cmp::Ordering::Greater => hi = m,
                std::cmp::Ordering::Equal => return Some(m),
            }
        }
        None
    }
    pub fn id(&self, k: &[u8]) -> Option<usize> {
        let slot = k[1] as usize - 1;
        self.find(fix::digest_key(&fix::base_of(k))).map(|b| slot * self.nb + b)
    }
    pub fn key_at(&self, i: usize) -> Vec<u8> {
        let b = i % self.nb;
        let r = &self.keys[32 * b..32 * b + 32];
        fix::with_life(&r[1..1 + r[0] as usize], (i / self.nb) as u32 + 1)
    }
    pub fn val(&self, i: usize) -> i64 {
        fix::of32(i32::from_le_bytes(self.vals[4 * i..4 * i + 4].try_into().unwrap()))
    }
    fn beta(&self, i: usize) -> i64 {
        self.beta.as_ref().map_or(0, |b| b[i] as i8 as i64)
    }
    /// The value at the BIG excess n (c + beta n), or the scalar value.
    pub fn at(&self, i: usize, n: i64) -> i64 {
        let v = self.val(i);
        if v >= INF || v <= NINF { v } else { v + self.beta(i) * n }
    }
    /// A-safe with ranks: the first round in which position i's value
    /// (in BIG mode, at excess n) went below l (B wins at l from then on),
    /// if it ever did.
    pub fn lost_round(&self, i: usize, l: i64, n: i64) -> Option<u32> {
        self.lost_at(i, l, n).map(|x| x.0)
    }
    /// The same round, with the value set in it (at n).
    pub fn lost_at(&self, i: usize, l: i64, n: i64) -> Option<(u32, i64)> {
        let (hidx, hrec) = self.hist.as_ref().expect("the A-safe trace needs a table solved with TCB_RANKS=1");
        let at = |k: usize| u64::from_le_bytes(hidx[8 * k..8 * k + 8].try_into().unwrap()) as usize;
        for p in at(i)..at(i + 1) {
            let r = u32::from_le_bytes(hrec[8 * p..8 * p + 4].try_into().unwrap());
            let x = i32::from_le_bytes(hrec[8 * p + 4..8 * p + 8].try_into().unwrap());
            let v = if self.beta.is_some() {
                // a BIG table logs lines (`solver::lenc`)
                let ln = crate::solver::ldec(x);
                if ln.special() { ln.c } else { ln.c + ln.b * n }
            } else {
                fix::of32(x)
            };
            if v < l {
                return Some((r, v));
            }
        }
        None
    }
}

/// A traced turn start: table position, B's life there, BIG excess.
type Node = (u32, i32, i32);

/// The traced side's preference between good moves, smaller first: the
/// abstraction rules its subtree in this turn needs (bits of the leaf
/// kinds from K_HUGE up), then, in the A-safe trace, the latest (A-life
/// level, round) among the turn starts it reaches (so B heads for the
/// fastest win, as an attractor strategy).
fn score(kind: u32, measure: u64) -> u64 {
    ((kind >> 8) as u64) << 40 | measure
}
fn join(a: u64, b: u64) -> u64 {
    let m = (1u64 << 40) - 1;
    (a | b) & !m | (a & m).max(b & m)
}

struct Tr<'a> {
    c: &'a Cfg,
    tb: &'a Table,
    /// the traced side: B (A-safe trace) or A (B-win trace)
    side: Player,
    nmax: i64,
    /// `TCB_TRACE_PV=1`: at the protagonist's nodes follow only its best
    /// replies by the table's own values (the moves its optimal strategy
    /// in the abstraction picks), instead of every reply.
    pv: bool,
}

/// The per-turn search context: the turn's A-life level and, for the
/// A-safe trace, the round bound for same-level turn starts.
struct Cx {
    level: u32,
    bound: u32,
    memo: HashMap<(State, i64, i64), (bool, u64, u16)>,
    // the protagonist's values (as `eval_turn`), for TCB_TRACE_PV
    vmemo: HashMap<State, i64>,
    lmemo: HashMap<State, fix::Line>,
}

/// What one turn's witness reaches.
#[derive(Default)]
struct TurnOut {
    ok: bool,
    /// (kind, child turn start for K_SAME / K_BELOW)
    leaves: Vec<(u32, Option<Node>)>,
    ann: [u64; NA],
    /// the first leaf of each kind in `want`: its path of moves in this turn
    ex: Vec<(u32, Vec<Move>)>,
    want: u32,
    /// with `collect`: the traced side's chosen (state, move, path) pairs
    collect: bool,
    chosen: Vec<(State, Move, Vec<Move>)>,
}

fn kind_ix(k: u32) -> usize {
    k.trailing_zeros() as usize
}

impl<'a> Tr<'a> {
    fn has_big(&self, s: &State) -> bool {
        self.c.big && s.side_a.bf.iter().any(|w| w.counters == self.c.big_k())
    }

    /// The leaf at a turn start (not the root): (good for the traced side,
    /// kind, the node to trace on, its measure for `score`).
    fn turn_start(&self, cx: &Cx, s: &State, l: i64, n: i64) -> (bool, u32, Option<Node>, u64) {
        let key = fix::key_gen(self.c.full_a, s);
        let i = self.tb.id(&key).expect("turn start not in the table");
        let n = if self.has_big(s) { n } else { 0 };
        let lvl = key[1] as u32;
        let kind = if lvl < cx.level { K_BELOW } else { K_SAME };
        let v = self.tb.at(i, n);
        if self.side == Player::B {
            // A-safe: B wins at l when v < l; v is at most lmax
            // (in BIG mode only c is clamped: c + b n may exceed lmax)
            if l > self.c.lmax && (!self.c.big || v < l) {
                return (true, K_LMAX, None, 0);
            }
            if v >= l {
                return (false, kind, None, 0);
            }
            // trace the child at the least B life lost by the same round
            // (a witness there also wins with more life, by monotonicity)
            let (r, vr) = self.tb.lost_at(i, l, n).expect("lost without a record");
            let ok = kind == K_BELOW || r < cx.bound;
            let lc = if vr <= NINF { 1 } else { (vr + 1).max(1) };
            (ok, kind, Some((i as u32, lc as i32, n as i32)), (lvl as u64) << 24 | r as u64)
        } else {
            // B-win: A escapes at l when v > l (B needs more)
            if n > self.nmax {
                return (v > l, K_NBOUND, None, 0);
            }
            if l > self.c.lmax && v >= INF {
                return (true, K_LMAX, None, 0);
            }
            // trace the child at B's life there: tracing it at the most B
            // life A escapes with (v - 1) would also cover less life, but
            // would make A lean on the lmax clamp where B banks from there
            let lc = l;
            // measure: how thin A's escape is (B's most dangerous tries are
            // the largest)
            let margin = if v >= INF { 1 << 20 } else { (v - l).clamp(0, 1 << 20) };
            (v > l, kind, Some((i as u32, lc as i32, n as i32)), ((1u64 << 20) - margin as u64))
        }
    }

    /// The edge of move m from s: Err(leaf (good, kind)) or Ok(child, its
    /// B life, its n, annotations). None: the move is dropped.
    #[allow(clippy::type_complexity)]
    fn edge(&self, s: &State, m: &Move, l: i64, n: i64) -> Option<Result<(State, i64, i64, [bool; NA]), (bool, u32)>> {
        let c = self.c;
        if c.huge_event(s, m) {
            // a real end if the protagonist dies anyway in this damage step
            // with the huge Walker at its representative size (the real one
            // is at least as big)
            let s2 = step(s, m);
            if c.prot == Player::A && winner(&s2) == Some(Player::B) {
                return Some(Err((true, K_ADEAD)));
            }
            let d = s2.side_b.life as i64 - s.side_b.life as i64;
            if c.prot == Player::B && d < 0 && l <= -d {
                return Some(Err((true, K_BDEAD)));
            }
            return Some(Err((true, self.huge_kind(s))));
        }
        let pre = step(s, m);
        let mut s2 = pre.clone();
        c.clamp(&mut s2);
        let mut ann = [false; NA];
        let (p, o) = (c.prot, c.prot.opp());
        ann[A_TCUT] = s2.side(p).thop_u + s2.side(p).thop_t < pre.side(p).thop_u + pre.side(p).thop_t;
        ann[A_SAT] = s2.side(o).bf.iter().zip(pre.side(o).bf.iter()).any(|(a, b)| a.counters < b.counters)
            && !(c.big && o == Player::A);
        if c.too_many(&s2) {
            return Some(Err((true, K_MANY)));
        }
        let f = c.big_flags(s, m);
        if f & F_SECOND != 0 {
            if c.strict("second") {
                return Some(Err((true, K_SECOND)));
            }
            return None;
        }
        c.big_fix(f, m, &mut s2);
        let mut d = s2.side_b.life as i64 - s.side_b.life as i64;
        let mut n2 = n;
        if f & F_CREATE != 0 {
            n2 = 0;
        }
        if f & F_PUMP != 0 {
            n2 = n + 1;
        }
        if f & F_HIT != 0 {
            d -= n;
        }
        if d < 0 && l <= -d {
            return Some(Err((self.side == Player::A, K_BDEAD)));
        }
        Some(Ok((s2, l + d, n2, ann)))
    }

    /// Which of `Cfg::huge_event`'s rules fired (the first that applies).
    fn huge_kind(&self, s: &State) -> u32 {
        let huge = self.c.ot + 1;
        let o = self.c.prot.opp();
        let att = s.side(s.active);
        let fights = || s.cmb.atk.iter().zip(s.cmb.blk.iter());
        if s.active == o && fights().any(|(&i, bs)| att.bf[i as usize].counters >= huge && bs.is_empty()) {
            K_HUGE
        } else if s.active == o {
            K_HUGE_DIE
        } else {
            K_HUGE_BLK
        }
    }

    /// Does the traced side succeed from s with B on l life (BIG excess n)?
    /// Returns (success, mask of the witness's leaves in this turn).
    fn search(&self, cx: &mut Cx, s: &State, l: i64, n: i64, root: bool) -> (bool, u64) {
        match winner(s) {
            Some(Player::B) => return (self.side == Player::B, 0),
            Some(Player::A) => panic!("A cannot win inside the abstraction"),
            None => {}
        }
        if !root && is_turn_start(s) {
            let (ok, k, _, me) = self.turn_start(cx, s, l, n);
            return (ok, score(k, me));
        }
        let key = (fix::normal(false, s), l, n);
        if let Some(&(ok, mk, _)) = cx.memo.get(&key) {
            return (ok, mk);
        }
        let mine = to_move(s) == self.side;
        let ms = self.c.moves_for(s);
        let (mut ok, mut mask, mut choice) = (!mine, 0u64, u16::MAX);
        let mut best = u64::MAX;
        for (j, m) in ms.iter().enumerate() {
            let Some((cok, cmk)) = self.child(cx, s, m, l, n) else { continue };
            if mine {
                if cok && cmk < best {
                    best = cmk;
                    choice = j as u16;
                    ok = true;
                }
            } else if !cok {
                ok = false;
                break;
            } else {
                mask = join(mask, cmk);
            }
        }
        if mine && ok {
            mask = best;
        }
        cx.memo.insert(key, (ok, mask, choice));
        (ok, mask)
    }

    /// How good move m from s is for the protagonist, in the table's own
    /// terms (its value as `eval_turn` computes it; in BIG mode at the
    /// excess n), larger is better; None for a dropped move.
    fn pv_value(&self, cx: &mut Cx, s: &State, m: &Move, n: i64) -> Option<i64> {
        let c = self.c;
        let sign = if c.up() { -1 } else { 1 };
        let lose = sign * c.lose();
        if c.huge_event(s, m) {
            return Some(lose);
        }
        let mut s2 = step(s, m);
        c.clamp(&mut s2);
        let f = c.big_flags(s, m);
        if f & F_SECOND != 0 && !c.strict("second") {
            return None;
        }
        if c.too_many(&s2) || f & F_SECOND != 0 {
            return Some(lose);
        }
        c.big_fix(f, m, &mut s2);
        let d = s2.side_b.life as i64 - s.side_b.life as i64;
        let tb = self.tb;
        if c.big {
            let mut lookup = |k: &[u8]| {
                let i = tb.id(k).expect("turn start not in the table");
                fix::Line { c: tb.val(i), b: tb.beta(i) }
            };
            let v = fix::ltrans(c.up(), c.bigref, fix::eval_go_big(c, &mut lookup, &mut cx.lmemo, &s2, false), d, f);
            let x = if v.c >= INF || v.c <= NINF { v.c } else { v.c + v.b * n };
            return Some(sign * x);
        }
        let mut lookup = |k: &[u8]| tb.val(tb.id(k).expect("turn start not in the table"));
        let v = fix::shift(fix::eval_go(c, &mut lookup, &mut cx.vmemo, &s2, false), d);
        let v = if d < 0 { if c.up() { (1 - d).max(v) } else { (-d).max(v) } } else { v };
        Some(sign * v)
    }

    /// The (success, score) of move m from s, or None for a dropped move.
    fn child(&self, cx: &mut Cx, s: &State, m: &Move, l: i64, n: i64) -> Option<(bool, u64)> {
        match self.edge(s, m, l, n)? {
            Err((g, k)) => Some((g, score(k, 0))),
            Ok((s2, l2, n2, _)) => Some(self.search(cx, &s2, l2, n2, false)),
        }
    }

    /// Walk the witness found by `search`, collecting its leaves (each
    /// intra-turn state once). With `target`, stop at the first leaf
    /// reaching that turn start and return the path to it.
    #[allow(clippy::too_many_arguments)]
    fn walk(&self, cx: &mut Cx, s: &State, l: i64, n: i64, root: bool, path: &mut Vec<Move>, seen: &mut HashSet<(State, i64, i64)>, out: &mut TurnOut, target: Option<Node>) -> bool {
        let leaf = |out: &mut TurnOut, k: u32, nd: Option<Node>, path: &Vec<Move>| -> bool {
            if let Some(t) = target {
                return nd == Some(t);
            }
            out.leaves.push((k, nd));
            if out.want & k != 0 && !out.ex.iter().any(|(x, _)| *x == k) {
                out.ex.push((k, path.clone()));
            }
            false
        };
        if winner(s).is_some() {
            return leaf(out, K_ADEAD, None, path);
        }
        if !root && is_turn_start(s) {
            let (ok, k, nd, _) = self.turn_start(cx, s, l, n);
            assert!(ok);
            return leaf(out, k, nd, path);
        }
        if !seen.insert((fix::normal(false, s), l, n)) {
            return false;
        }
        let (ok, _) = self.search(cx, s, l, n, root);
        assert!(ok);
        let &(_, _, choice) = cx.memo.get(&(fix::normal(false, s), l, n)).unwrap();
        let mine = to_move(s) == self.side;
        let ms = self.c.moves_for(s);
        if !mine && target.is_none() && self.c.moves_of(self.c.mine, s).len() > ms.len() {
            out.ann[A_CAP] += 1;
        }
        // with pv, the protagonist's best replies only
        let pvv: Vec<Option<i64>> = if !mine && self.pv { ms.iter().map(|m| self.pv_value(cx, s, m, n)).collect() } else { vec![] };
        let top = pvv.iter().flatten().max().copied();
        for (j, m) in ms.iter().enumerate() {
            if mine && j != choice as usize {
                continue;
            }
            if mine && out.collect && target.is_none() {
                out.chosen.push((s.clone(), m.clone(), path.clone()));
            }
            if !mine && self.pv && pvv[j] != top {
                continue;
            }
            path.push(m.clone());
            let found = match self.edge(s, m, l, n) {
                None => false,
                Some(Err((g, k))) => {
                    assert!(g);
                    leaf(out, k, None, path)
                }
                Some(Ok((s2, l2, n2, ann))) => {
                    if target.is_none() {
                        for (a, &x) in ann.iter().enumerate() {
                            out.ann[a] += x as u64;
                        }
                    }
                    self.walk(cx, &s2, l2, n2, false, path, seen, out, target)
                }
            };
            if found {
                return true;
            }
            path.pop();
        }
        false
    }

    fn cx_for(&self, nd: Node) -> Cx {
        let (i, l, _) = nd;
        let level = (i as usize / self.tb.nb) as u32 + 1;
        let bound = if self.side == Player::B { self.tb.lost_round(i as usize, l as i64, nd.2 as i64).expect("not lost") } else { 0 };
        Cx { level, bound, memo: HashMap::default(), vmemo: HashMap::default(), lmemo: HashMap::default() }
    }

    fn state_of(&self, nd: Node) -> State {
        fix::of_key(&self.tb.key_at(nd.0 as usize))
    }

    /// The witness of one traced turn start.
    fn turn(&self, nd: Node, want: u32) -> TurnOut {
        let mut cx = self.cx_for(nd);
        let s = self.state_of(nd);
        let mut out = TurnOut { want, ..Default::default() };
        let (l, n) = (nd.1 as i64, nd.2 as i64);
        let (ok, _) = self.search(&mut cx, &s, l, n, true);
        out.ok = ok;
        if ok {
            self.walk(&mut cx, &s, l, n, true, &mut vec![], &mut HashSet::default(), &mut out, None);
        }
        out
    }

    fn path_to(&self, nd: Node, child: Node) -> Vec<Move> {
        let mut cx = self.cx_for(nd);
        let s = self.state_of(nd);
        let mut path = vec![];
        let found = self.walk(&mut cx, &s, nd.1 as i64, nd.2 as i64, true, &mut path, &mut HashSet::default(), &mut TurnOut::default(), Some(child));
        assert!(found);
        path
    }
}

fn wk(w: &Walker, k: Option<u32>, n: i64) -> String {
    let size = if Some(w.counters) == k { format!("K+{n}") } else { w.counters.to_string() };
    format!("{size}{}{}", if w.tapped { "t" } else { "" }, if w.sick { "s" } else { "" })
}

/// A short readable turn-start or intra-turn state, with B on `bl` life.
fn short(c: &Cfg, s: &State, bl: i64, n: i64) -> String {
    let k = c.big.then(|| c.big_k());
    let side = |sd: &Side, life: String, kk: Option<u32>| {
        let ws: Vec<String> = sd.bf.iter().map(|w| wk(w, kk, n)).collect();
        let mut x = format!("life {life}, Walkers [{}], Thopters {}", ws.join(" "), sd.thop_u);
        if sd.thop_t > 0 {
            x += &format!("+{}t", sd.thop_t);
        }
        if sd.hand_w > 0 {
            x += &format!(", {} Walker(s) in hand", sd.hand_w);
        }
        if sd.hand_e {
            x += ", Elixir in hand";
        }
        if sd.elixir_bf {
            x += ", Elixir out";
        }
        if !sd.library.is_empty() {
            let l: Vec<&str> = sd.library.iter().map(|c| if *c == Card::Walker { "W" } else { "E" }).collect();
            x += &format!(", library [{}]", l.join(""));
        }
        if sd.gy_w > 0 && std::ptr::eq(sd, &s.side_b) {
            x += &format!(", {} Walker in graveyard", sd.gy_w);
        }
        x
    };
    format!(
        "{} active | A: {} | B: {}",
        if s.active == Player::A { "A" } else { "B" },
        side(&s.side_a, s.side_a.life.to_string(), k),
        side(&s.side_b, bl.to_string(), None)
    )
}

/// Print one turn: its start and the moves of `path`, with life changes.
fn print_turn(t: &Tr, nd: Node, path: &[Move]) {
    let c = t.c;
    let mut s = t.state_of(nd);
    let (l0, mut n) = (nd.1 as i64, nd.2 as i64);
    println!("    turn start: {}", short(c, &s, l0, n));
    if std::env::var("TCB_TRACE_KEYS").ok().as_deref() == Some("1") {
        let k: String = fix::key_gen(c.full_a, &s).iter().map(|x| format!("{x:02x}")).collect();
        println!("      key {k}");
    }
    let mut line = String::new();
    for m in path {
        let who = if to_move(&s) == Player::A { "A" } else { "B" };
        let f = c.big_flags(&s, m);
        let mut s2 = step(&s, m);
        c.clamp(&mut s2);
        c.big_fix(f, m, &mut s2);
        let mut d = s2.side_b.life as i64 - s.side_b.life as i64;
        if f & F_HIT != 0 {
            d -= n;
        }
        if f & F_CREATE != 0 {
            n = 0;
        }
        if f & F_PUMP != 0 {
            n += 1;
        }
        let mut txt = format!("{who}:{}", walk::mv(m));
        let da = s.side_a.life as i64 - s2.side_a.life as i64;
        if d != 0 || da != 0 {
            txt += &format!("[A {}, B {}]", s2.side_a.life, l0 + (s2.side_b.life as i64 - fix::BIG as i64) - if f & F_HIT != 0 { n } else { 0 });
        }
        if !line.is_empty() {
            line.push(' ');
        }
        line += &txt;
        s = s2;
    }
    println!("      {line}");
}

/// `TCB_CMP_DIR` and `TCB_CMP_CFG`: a B-win table to compare an A-safe
/// trace with, and its configuration as "t,tt,ot,ott,fullopp,big" (B's
/// moves filtered, as the B-win runs here).
fn cmp_cfg(a: &Cfg) -> Option<(Table, Cfg)> {
    let dir = std::env::var("TCB_CMP_DIR").ok()?;
    let v: Vec<u32> = std::env::var("TCB_CMP_CFG").expect("TCB_CMP_CFG").split(',').map(|x| x.parse().unwrap()).collect();
    let mut c = a.clone();
    c.prot = Player::B;
    (c.t, c.tt, c.ot, c.ott) = (v[0], v[1], v[2], v[3]);
    c.theirs = if v[4] == 1 { fix::MoveSet::Full } else { fix::MoveSet::Filter };
    c.mine = fix::MoveSet::Filter;
    c.big = v[5] == 1;
    c.lax = vec![];
    Some((Table::open(Path::new(&dir)), c))
}

/// Where an A-safe trace node stands in the B-win table.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Cmp {
    /// B wins there in the B-win table too
    Agree,
    /// the B-win table says A escapes at this life
    Disagree,
    /// the B-win table has no such position (outside its caps)
    Missing,
}

fn cmp_of(tb: &Table, cmp: &Table, nd: Node) -> Cmp {
    match cmp.id(&tb.key_at(nd.0 as usize)) {
        None => Cmp::Missing,
        Some(j) => {
            if cmp.at(j, 0) <= nd.1 as i64 {
                Cmp::Agree
            } else {
                Cmp::Disagree
            }
        }
    }
}

/// At a frontier node (the B-win table disagrees, but agrees on, or lacks,
/// every turn start the A-safe witness reaches from it): which rules of the
/// two abstractions differ inside this turn. Returns counts of
/// 0: B replies of the A-safe witness the B-win B can't make (its cap or
///    filter);
/// 1: A-safe witness edges where B's Thopters exceed the B-win tt;
/// 2: A moves of the B-win escape the A-safe A can't make (macro, cap);
/// 3: abstraction leaves in the A-safe witness.
fn frontier_report(ta: &Tr, tbw: &Tr, nd: Node, print: bool) -> [u64; 4] {
    let mut r = [0u64; 4];
    let mut oa = TurnOut { want: 0, collect: true, ..Default::default() };
    {
        let mut cx = ta.cx_for(nd);
        let s = ta.state_of(nd);
        let (l, n) = (nd.1 as i64, nd.2 as i64);
        assert!(ta.search(&mut cx, &s, l, n, true).0);
        ta.walk(&mut cx, &s, l, n, true, &mut vec![], &mut HashSet::default(), &mut oa, None);
    }
    r[3] = oa.leaves.iter().filter(|x| x.0 >= K_HUGE).count() as u64;
    let mut first_b = None;
    for (st, m, p) in &oa.chosen {
        if !tbw.c.moves_for(st).contains(m) {
            r[0] += 1;
            first_b.get_or_insert((m.clone(), p.clone()));
        }
        let s2 = step(st, m);
        if s2.side_b.thop_u + s2.side_b.thop_t > tbw.c.tt {
            r[1] += 1;
        }
    }
    let key = ta.tb.key_at(nd.0 as usize);
    let j = tbw.tb.id(&key).unwrap();
    let ndb: Node = (j as u32, nd.1, 0);
    let mut cx = tbw.cx_for(ndb);
    let s = tbw.state_of(ndb);
    let mut ob = TurnOut { want: 0, collect: true, ..Default::default() };
    let ok = tbw.search(&mut cx, &s, nd.1 as i64, 0, true).0;
    let mut first_a = None;
    if ok {
        tbw.walk(&mut cx, &s, nd.1 as i64, 0, true, &mut vec![], &mut HashSet::default(), &mut ob, None);
        for (st, m, p) in &ob.chosen {
            if !ta.c.moves_for(st).contains(m) {
                r[2] += 1;
                first_a.get_or_insert((m.clone(), p.clone()));
            }
        }
    }
    if print {
        let ps = |p: &Vec<Move>| p.iter().map(walk::mv).collect::<Vec<_>>().join(" ");
        if let Some((m, p)) = first_b {
            println!("      A-safe witness: B plays {} after [{}], which the B-win B can't", walk::mv(&m), ps(&p));
        }
        if let Some((m, p)) = first_a {
            println!("      B-win escape: A plays {} after [{}], which the A-safe A can't", walk::mv(&m), ps(&p));
        }
        if !ok {
            println!("      (the B-win turn, searched directly, does not confirm its stored escape)");
        }
        // the escape's leaves that the A-safe table calls lost for A
        let mut shown = 0;
        for (_, ch) in &ob.leaves {
            if let Some(c) = ch {
                let kk = tbw.tb.key_at(c.0 as usize);
                if let Some(i) = ta.tb.id(&kk) {
                    if ta.tb.val(i) < c.1 as i64 && shown < 2 {
                        shown += 1;
                        println!(
                            "      B-win escape reaches {} (B-win: B needs {}; A-safe: A safe up to {})",
                            short(ta.c, &fix::of_key(&kk), c.1 as i64, 0),
                            tbw.tb.at(c.0 as usize, 0),
                            ta.tb.val(i)
                        );
                    }
                }
            }
        }
    }
    r
}

/// `rsolver trace DIR A|B T TT LMAX STARTER L...` (see the module doc).
pub fn run(c: &Cfg, dir: &str, starter: Player, lives: &[i64]) {
    let tb = Table::open(Path::new(dir));
    let side = c.prot.opp();
    if c.big && side == Player::B && tb.hist.is_none() {
        eprintln!("trace: a BIG A-safe table needs ranks (solve it with TCB_RANKS=1)");
        std::process::exit(2);
    }
    if c.big != tb.beta.is_some() {
        eprintln!("trace: TCB_BIG must match the table (a BIG table has a beta file)");
        std::process::exit(2);
    }
    let env = |v: &str, d: usize| std::env::var(v).ok().and_then(|x| x.parse().ok()).unwrap_or(d);
    let maxn = env("TCB_TRACE_MAX", 3_000_000);
    let t = Tr { c, tb: &tb, side, nmax: env("TCB_TRACE_NMAX", 40) as i64, pv: env("TCB_TRACE_PV", 0) == 1 };
    let cmp = if side == Player::B { cmp_cfg(c) } else { None };
    let tbw = cmp.as_ref().map(|(ct, cc)| Tr { c: cc, tb: ct, side: Player::A, nmax: 40, pv: false });
    if t.pv {
        println!("following only the protagonist's best replies (TCB_TRACE_PV=1)");
    }
    let s0 = crate::start_state(starter);
    let i0 = tb.id(&fix::key_gen(c.full_a, &s0)).expect("start not in the table");
    println!("table {dir}: {} positions ({} bases x {} levels); start value {}{}", tb.nb * tb.nl, tb.nb, tb.nl, tb.val(i0), if c.big { format!(", beta {}", tb.beta(i0)) } else { String::new() });
    let jobs = crate::solver::jobs();
    for &l0 in lives {
        let t0 = std::time::Instant::now();
        let root: Node = (i0 as u32, l0 as i32, 0);
        let good = if side == Player::B { tb.val(i0) < l0 } else { tb.at(i0, 0) > l0 };
        println!();
        if !good {
            println!(
                "B life {l0}: the table gives {} here, nothing to trace",
                if side == Player::B { "A safe" } else { "a B win" }
            );
            continue;
        }
        println!(
            "B life {l0}: tracing {}",
            if side == Player::B { "B's win against every A move (A-safe table)" } else { "A's escape against every B move (B-win table)" }
        );
        // breadth first over traced turn starts
        let mut nodes: Vec<(Node, u32)> = vec![(root, u32::MAX)];
        let mut seen: HashMap<Node, u32> = HashMap::default();
        seen.insert(root, 0);
        let mut count = [0u64; NK];
        let mut turns_with = [0u64; NK];
        let mut ann = [0u64; NA];
        let mut ex: Vec<Option<(u32, Vec<Move>)>> = vec![None; NK];
        let mut loose: Vec<u32> = vec![];
        let mut maxdepth = 0;
        // with a B-win table to compare: (Agree, Disagree, Missing) nodes,
        // and the frontier nodes (disagree; no traced child disagrees)
        let mut ncmp = [0u64; 3];
        let mut frontier: Vec<(u32, bool)> = vec![];
        let mut depth_of: Vec<u32> = vec![0];
        let (mut lo, mut truncated) = (0usize, false);
        while lo < nodes.len() {
            // in batches, so that the turns' outputs held at once stay small
            let hi = nodes.len().min(lo + 200_000);
            if hi > maxn {
                truncated = true;
                break;
            }
            let want = (0..NK).filter(|&b| ex[b].is_none()).fold(0u32, |a, b| a | 1 << b) & !(K_SAME | K_BELOW);
            let next = std::sync::atomic::AtomicUsize::new(lo);
            let res = std::sync::Mutex::new(Vec::<(usize, TurnOut)>::new());
            std::thread::scope(|sc| {
                for _ in 0..jobs {
                    sc.spawn(|| loop {
                        let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if k >= hi {
                            break;
                        }
                        let o = t.turn(nodes[k].0, want);
                        res.lock().unwrap().push((k, o));
                    });
                }
            });
            let mut r = res.into_inner().unwrap();
            r.sort_by_key(|x| x.0);
            let outs: Vec<TurnOut> = r.into_iter().map(|x| x.1).collect();
            for (off, o) in outs.into_iter().enumerate() {
                let k = lo + off;
                if !o.ok {
                    loose.push(k as u32);
                    continue;
                }
                for a in 0..NA {
                    ann[a] += o.ann[a];
                }
                let mut had = 0u32;
                for &(kind, child) in &o.leaves {
                    count[kind_ix(kind)] += 1;
                    had |= kind;
                    if let Some(ch) = child {
                        if !seen.contains_key(&ch) {
                            seen.insert(ch, nodes.len() as u32);
                            nodes.push((ch, k as u32));
                            depth_of.push(depth_of[k] + 1);
                            maxdepth = maxdepth.max(depth_of[k] + 1);
                        }
                    }
                }
                for b in 0..NK {
                    if had & (1 << b) != 0 {
                        turns_with[b] += 1;
                    }
                }
                if let Some((ct, _)) = &cmp {
                    let me = cmp_of(&tb, ct, nodes[k].0);
                    ncmp[me as usize] += 1;
                    if me == Cmp::Disagree {
                        let kids: Vec<Cmp> = o.leaves.iter().filter_map(|x| x.1).map(|ch| cmp_of(&tb, ct, ch)).collect();
                        if !kids.contains(&Cmp::Disagree) {
                            frontier.push((k as u32, kids.contains(&Cmp::Missing)));
                        }
                    }
                }
                for (kind, p) in o.ex {
                    let e = &mut ex[kind_ix(kind)];
                    if e.is_none() {
                        *e = Some((k as u32, p));
                    }
                }
            }
            lo = hi;
        }
        println!(
            "  {} turn starts traced{}, depth up to {maxdepth} turns ({:.1}s)",
            lo,
            if truncated { format!(" (stopped at TCB_TRACE_MAX = {maxn}; {} queued)", nodes.len() - lo) } else { String::new() },
            t0.elapsed().as_secs_f64()
        );
        if !loose.is_empty() {
            println!(
                "  {} traced turn starts where the turn, searched directly from the table, does not confirm the stored value{}",
                loose.len(),
                if c.big && side == Player::A {
                    " (BIG: the line's componentwise or single-line choice; a per-n search disagrees)"
                } else if c.big {
                    " (BIG: the componentwise min at B's nodes, A's single-line choice, or a clamp of c or b; a per-n search disagrees)"
                } else {
                    " (A RED FLAG: the table disagrees with the model)"
                }
            );
            let inf = loose.iter().filter(|&&k| tb.val(nodes[k as usize].0 .0 as usize) >= INF).count();
            let nbig = loose.iter().filter(|&&k| t.has_big(&t.state_of(nodes[k as usize].0))).count();
            println!("    of them {inf} stored as INF, {nbig} with a BIG Walker");
        }
        let chain = |mut k: u32| {
            let mut ch = vec![];
            while k != u32::MAX {
                ch.push(k);
                k = nodes[k as usize].1;
            }
            ch.reverse();
            ch
        };
        if let (Some(tw), Some((_, cc))) = (&tbw, &cmp) {
            println!(
                "  against the B-win table (B Walker cap {}, Thopters {}, A huge > {}, ott {}): B wins there too at {} traced turn starts, A escapes at {}, {} missing",
                cc.t, cc.tt, cc.ot, cc.ott, ncmp[0], ncmp[1], ncmp[2]
            );
            let fm = frontier.iter().filter(|x| x.1).count();
            println!("  frontier (the B-win table disagrees here but on no traced child): {} turn starts, {} of them with a child the B-win table lacks", frontier.len(), fm);
            let mut tot = [0u64; 4];
            let mut why = [0u64; 5];
            for &(k, miss) in &frontier {
                let r = frontier_report(&t, tw, nodes[k as usize].0, false);
                for a in 0..4 {
                    tot[a] += r[a];
                }
                let w = if miss { 0 } else if r[2] > 0 { 1 } else if r[0] > 0 || r[1] > 0 { 2 } else if r[3] > 0 { 3 } else { 4 };
                why[w] += 1;
            }
            println!("    frontier turns by first explanation: a child outside the B-win caps {}; a B-win escape move the A-safe A can't make {}; an A-safe B reply the B-win B can't make, or B Thopters above its cap {}; an A-safe abstraction leaf {}; none of these {}", why[0], why[1], why[2], why[3], why[4]);
            println!("    totals: A-safe B replies the B-win B can't make {}, A-safe edges with B Thopters above the B-win tt {}, B-win escape moves the A-safe A can't make {}, A-safe abstraction leaves {}", tot[0], tot[1], tot[2], tot[3]);
            let ex_n = env("TCB_CMP_EX", 3);
            for &(k, _) in frontier.iter().filter(|x| !x.1).take(ex_n) {
                let nd = nodes[k as usize].0;
                println!("  frontier example ({} turns):", depth_of[k as usize] + 1);
                let ch = chain(k);
                for w in ch.windows(2) {
                    let (a, b) = (nodes[w[0] as usize].0, nodes[w[1] as usize].0);
                    print_turn(&t, a, &t.path_to(a, b));
                }
                print_turn(&t, nd, &[]);
                frontier_report(&t, tw, nd, true);
            }
        }
        println!("  leaves of the witness, by kind: (leaf edges, turns with one)");
        for b in 0..NK {
            if count[b] > 0 {
                println!("    {:<40} {:>10} {:>9}", NAMES[b], count[b], turns_with[b]);
            }
        }
        println!("  annotations: (count)");
        for a in 0..NA {
            println!("    {:<56} {:>10}", ANAMES[a], ann[a]);
        }
        let show_line = |k: u32, last: &[Move]| {
            let ch = chain(k);
            for w in ch.windows(2) {
                let (a, b) = (nodes[w[0] as usize].0, nodes[w[1] as usize].0);
                print_turn(&t, a, &t.path_to(a, b));
            }
            print_turn(&t, nodes[k as usize].0, last);
        };
        for b in 0..NK {
            if let Some((k, p)) = &ex[b] {
                if (1u32 << b) & (K_SAME | K_BELOW) != 0 {
                    continue;
                }
                println!("  example, {} ({} turns):", NAMES[b], depth_of[*k as usize] + 1);
                show_line(*k, p);
            }
        }
        for &k in loose.iter().take(2) {
            let nd = nodes[k as usize].0;
            println!("  example, not confirmed (B life {}, n {}; {} turns):", nd.1, nd.2, depth_of[k as usize] + 1);
            show_line(k, &[]);
        }
    }
}
