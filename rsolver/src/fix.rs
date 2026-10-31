//! The finite abstraction and turn programs (solver/fix.ml): values,
//! clamping, huge events, packed turn-start keys and their digests, turn
//! compilation and evaluation. Keys, digests and programs are identical to
//! the OCaml solver's, so tables are interchangeable.

use crate::model::*;
use crate::reduce::{self, Rules};
use md5::{Digest, Md5};
use rustc_hash::FxHashMap as HashMap;

pub const INF: i64 = i64::MAX / 4;
pub const NINF: i64 = i64::MIN / 4;
/// B's life while a turn is searched, so the model never ends the game for B.
pub const BIG: u32 = 1000;
/// A's life when turns are compiled: no turn can take it.
pub const SENT: u32 = 100;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum MoveSet {
    Full,
    Filter,
    AMacro,
    BMacro,
}

#[derive(Clone, Debug)]
pub struct Cfg {
    pub prot: Player,
    pub t: u32,
    pub ot: u32,
    pub tt: u32,
    pub ott: u32,
    pub lmax: i64,
    pub full_a: bool,
    pub mine: MoveSet,
    pub theirs: MoveSet,
    pub arules: Rules,
    pub brules: Rules,
    pub lax: Vec<String>,
}

impl Cfg {
    pub fn up(&self) -> bool {
        self.prot == Player::B
    }
    pub fn best(&self, a: i64, b: i64) -> i64 {
        if self.up() { a.min(b) } else { a.max(b) }
    }
    pub fn worst(&self, a: i64, b: i64) -> i64 {
        if self.up() { a.max(b) } else { a.min(b) }
    }
    pub fn lose(&self) -> i64 {
        if self.up() { INF } else { NINF }
    }
    /// Normalise a turn-start value: B's life is at least 1 there.
    pub fn norm(&self, v: i64) -> i64 {
        if self.up() {
            if v > self.lmax { INF } else if v <= 1 { 1 } else { v }
        } else if v < 1 {
            NINF
        } else if v >= INF {
            INF
        } else {
            v.min(self.lmax)
        }
    }
    fn huge(&self) -> u32 {
        self.ot + 1
    }
    fn strict(&self, r: &str) -> bool {
        !self.lax.iter().any(|x| x == r)
    }
    fn moves_of(&self, set: MoveSet, s: &State) -> Vec<Move> {
        match set {
            MoveSet::Full => moves(s),
            MoveSet::Filter => reduce::filtered(s),
            MoveSet::AMacro => reduce::a_macro(&self.arules, s),
            MoveSet::BMacro => reduce::b_macro(&self.brules, s),
        }
    }
    pub fn moves_for(&self, s: &State) -> Vec<Move> {
        if to_move(s) == self.prot {
            let ps = s.side(self.prot);
            self.moves_of(self.mine, s)
                .into_iter()
                .filter(|m| match m {
                    Move::Pump(i) => ps.bf[*i as usize].counters < self.t,
                    _ => true,
                })
                .collect()
        } else {
            self.moves_of(self.theirs, s)
        }
    }

    /// Clamp after a step: the opponent's Walkers at most huge, the
    /// protagonist's Thopters at most tt (tapped ones go first).
    pub fn clamp(&self, s: &mut State) {
        let huge = self.huge();
        let tt = self.tt;
        let cut = |sd: &mut Side| {
            let total = sd.thop_u + sd.thop_t;
            if total > tt {
                let extra = total - tt;
                let dt = extra.min(sd.thop_t);
                sd.thop_t -= dt;
                sd.thop_u -= extra - dt;
            }
        };
        let o = self.prot.opp();
        {
            let os = s.side_mut(o);
            for w in os.bf.iter_mut() {
                if w.counters > huge {
                    w.counters = huge;
                }
            }
            if !self.strict("many") {
                cut(os);
            }
        }
        cut(s.side_mut(self.prot));
    }

    /// Does this move make an exact huge size matter (a loss for the protagonist)?
    pub fn huge_event(&self, s: &State, m: &Move) -> bool {
        if !(matches!(s.pend, Pending::ChooseDamage) && matches!(m, Move::Assign(_))) {
            return false;
        }
        let o = self.prot.opp();
        let huge = self.huge();
        let att = s.side(s.active);
        let def = s.side(s.active.opp());
        let is_huge = |sd: &Side, i: u32| sd.bf[i as usize].counters >= huge;
        let total = |bs: &[Blocker]| bs.iter().map(|&b| blocker_toughness(def, b)).sum::<u32>();
        let fights = || s.cmb.atk.iter().zip(s.cmb.blk.iter());
        (self.strict("dmg") && s.active == o && fights().any(|(&i, bs)| is_huge(att, i) && bs.is_empty()))
            || (self.strict("die")
                && s.active == o
                && fights().any(|(&i, bs)| is_huge(att, i) && !bs.is_empty() && total(bs) >= huge))
            || (self.strict("die")
                && s.active != o
                && fights().any(|(&i, bs)| {
                    bs.iter().any(|b| match b {
                        Blocker::BW(j) => is_huge(def, *j) && att.bf[i as usize].counters >= huge,
                        Blocker::BT => false,
                    })
                }))
    }

    pub fn too_many(&self, s: &State) -> bool {
        self.strict("many") && {
            let os = s.side(self.prot.opp());
            os.thop_u + os.thop_t > self.ott
        }
    }
}

pub fn shift(v: i64, d: i64) -> i64 {
    if v >= INF || v <= NINF { v } else { v - d }
}

/// Drop what the abstraction ignores: B's life, A's graveyard, and with
/// `full_a` A's life.
pub fn normal(full_a: bool, s: &State) -> State {
    let mut s = s.clone();
    canon(&mut s);
    s.side_a.gy_w = 0;
    if full_a {
        s.side_a.life = 20;
    }
    s.side_b.life = 0;
    s
}

fn pack_side(buf: &mut Vec<u8>, sd: &Side) {
    let mut byte = |n: u32| {
        assert!(n < 256);
        buf.push(n as u8)
    };
    byte(sd.life);
    byte(sd.city as u32 | (sd.hand_e as u32) << 1 | (sd.elixir_bf as u32) << 2);
    byte(sd.pool);
    byte(sd.hand_w);
    byte(sd.gy_w);
    byte(sd.thop_u);
    byte(sd.thop_t);
    byte(sd.bf.len() as u32);
    for w in &sd.bf {
        byte(w.counters);
        byte(w.tapped as u32 | (w.sick as u32) << 1);
    }
    byte(sd.library.len() as u32);
    for c in &sd.library {
        byte(match c {
            Card::Walker => 0,
            Card::Elixir => 1,
        });
    }
}

/// The packed key of a turn-start position (Fix.key_gen).
pub fn key_gen(full_a: bool, s: &State) -> Vec<u8> {
    debug_assert!(is_turn_start(s) && s.cmb.is_empty());
    let s = normal(full_a, s);
    let mut buf = Vec::with_capacity(32);
    buf.push((if s.active == Player::A { 0 } else { 1 }) | if s.first_turn { 2 } else { 0 });
    pack_side(&mut buf, &s.side_a);
    pack_side(&mut buf, &s.side_b);
    buf
}

pub fn of_key(k: &[u8]) -> State {
    let mut pos = 0;
    let mut byte = || {
        let n = k[pos] as u32;
        pos += 1;
        n
    };
    let side = |byte: &mut dyn FnMut() -> u32| {
        let life = byte();
        let f = byte();
        let pool = byte();
        let hand_w = byte();
        let gy_w = byte();
        let thop_u = byte();
        let thop_t = byte();
        let nb = byte();
        let mut bf = SVec::new();
        for _ in 0..nb {
            let counters = byte();
            let g = byte();
            bf.push(Walker { counters, tapped: g & 1 != 0, sick: g & 2 != 0 });
        }
        let nl = byte();
        let mut library = SVec::new();
        for _ in 0..nl {
            library.push(if byte() == 0 { Card::Walker } else { Card::Elixir });
        }
        Side {
            life,
            city: f & 1 != 0,
            pool,
            hand_w,
            hand_e: f & 2 != 0,
            bf,
            elixir_bf: f & 4 != 0,
            thop_u,
            thop_t,
            library,
            gy_w,
        }
    };
    let g = byte();
    let active = if g & 1 == 0 { Player::A } else { Player::B };
    let side_a = side(&mut byte);
    let mut side_b = side(&mut byte);
    side_b.life = BIG;
    State {
        active,
        first_turn: g & 2 != 0,
        side_a,
        side_b,
        cmb: Combat::default(),
        pend: Pending::Window(Step::Upkeep, active, false),
    }
}

pub fn with_life(k: &[u8], l: u32) -> Vec<u8> {
    let mut k = k.to_vec();
    k[1] = l as u8;
    k
}

pub fn base_of(k: &[u8]) -> Vec<u8> {
    with_life(k, 0)
}

/// The first 8 bytes of the MD5 of a key, as OCaml's 63-bit int.
pub fn digest_key(k: &[u8]) -> i64 {
    let h = Md5::digest(k);
    let x = i64::from_le_bytes(h[0..8].try_into().unwrap());
    (x << 1) >> 1
}

/// Value of the turn starting at `s` by direct search through the model;
/// turn starts after it are looked up. `lookup` also sees every turn start
/// the search reaches, which exploration uses.
pub fn eval_turn(c: &Cfg, lookup: &mut dyn FnMut(&[u8]) -> i64, s: &State) -> i64 {
    let mut local: HashMap<State, i64> = HashMap::default();
    eval_go(c, lookup, &mut local, s, true)
}

fn eval_go(c: &Cfg, lookup: &mut dyn FnMut(&[u8]) -> i64, local: &mut HashMap<State, i64>, s: &State, root: bool) -> i64 {
    match winner(s) {
        Some(Player::B) => return NINF,
        Some(Player::A) => panic!("A cannot win inside the abstraction"),
        None => {}
    }
    if !root && is_turn_start(s) {
        return lookup(&key_gen(c.full_a, s));
    }
    let k = normal(false, s);
    if let Some(&v) = local.get(&k) {
        return v;
    }
    let mine = to_move(s) == c.prot;
    let mut acc = if mine { c.lose() } else if c.up() { NINF } else { INF };
    for m in c.moves_for(s) {
        let v = if c.huge_event(s, &m) {
            c.lose()
        } else {
            let mut s2 = step(s, &m);
            c.clamp(&mut s2);
            if c.too_many(&s2) {
                c.lose()
            } else {
                let d = s2.side_b.life as i64 - s.side_b.life as i64;
                let v = shift(eval_go(c, lookup, local, &s2, false), d);
                if d < 0 {
                    if c.up() { (1 - d).max(v) } else { (-d).max(v) }
                } else {
                    v
                }
            }
        };
        acc = if mine { c.best(acc, v) } else { c.worst(acc, v) };
    }
    local.insert(k, acc);
    acc
}

/// A state with its hash, computed once: the search looks a state up and
/// later inserts it.
#[derive(PartialEq, Eq)]
struct Hashed(u64, State);
impl std::hash::Hash for Hashed {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        h.write_u64(self.0)
    }
}
fn hashed(s: State) -> Hashed {
    use std::hash::BuildHasher;
    Hashed(rustc_hash::FxBuildHasher.hash_one(&s), s)
}

/// A child reference while compiling: a constant (0 = ninf, 1 = inf) or a
/// reference of kind 1 (node) or 2 (turn start) with a change d in B's life.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
enum Cref {
    Const(i64),
    Ref(i64, i64, i64),
}

/// Compile the turn at `s` into a straight-line program (see fix.ml for
/// the format). Returns the words and the node count.
pub fn compile(c: &Cfg, tgt: &dyn Fn(&State) -> i64, s: &State) -> (Vec<i32>, usize) {
    struct Ctx<'a> {
        c: &'a Cfg,
        tgt: &'a dyn Fn(&State) -> i64,
        local: HashMap<Hashed, Cref>,
        buf: Vec<i32>,
        nodes: usize,
        lost: i64,
        won: i64,
    }
    fn push2(buf: &mut Vec<i32>, r: Cref) {
        match r {
            Cref::Ref(kind, x, d) => {
                buf.push(x as i32);
                buf.push((4 * d + kind) as i32);
            }
            Cref::Const(v) => {
                buf.push(v as i32);
                buf.push(0);
            }
        }
    }
    fn go(cx: &mut Ctx, s: &State, root: bool) -> Cref {
        match winner(s) {
            Some(Player::B) => return Cref::Const(0),
            Some(Player::A) => panic!("A cannot win inside the abstraction"),
            None => {}
        }
        if !root && is_turn_start(s) {
            return Cref::Ref(2, (cx.tgt)(s), 0);
        }
        let k = hashed(normal(false, s));
        if let Some(&r) = cx.local.get(&k) {
            return r;
        }
        let mine = to_move(s) == cx.c.prot;
        let useless = if mine { cx.lost } else { cx.won };
        let decisive = if mine { cx.won } else { cx.lost };
        let ms = cx.c.moves_for(s);
        let kids: Vec<Cref> = ms.iter().map(|m| edge(cx, s, m)).collect();
        let r = if kids.contains(&Cref::Const(decisive)) {
            Cref::Const(decisive)
        } else {
            let mut ks: Vec<Cref> = kids.into_iter().filter(|r| *r != Cref::Const(useless)).collect();
            ks.sort();
            ks.dedup();
            match ks.len() {
                0 => Cref::Const(useless),
                1 => ks[0],
                n => {
                    assert!(n < 0x8000);
                    cx.buf.push((2 * n + if mine { 0 } else { 1 }) as i32);
                    for r in ks {
                        push2(&mut cx.buf, r);
                    }
                    cx.nodes += 1;
                    Cref::Ref(1, cx.nodes as i64 - 1, 0)
                }
            }
        };
        cx.local.insert(k, r);
        r
    }
    fn edge(cx: &mut Ctx, s: &State, m: &Move) -> Cref {
        if cx.c.huge_event(s, m) {
            return Cref::Const(cx.lost);
        }
        let mut s2 = step(s, m);
        cx.c.clamp(&mut s2);
        if cx.c.too_many(&s2) {
            return Cref::Const(cx.lost);
        }
        let d = s2.side_b.life as i64 - s.side_b.life as i64;
        let u = s.side_a.life as i64 - s2.side_a.life as i64;
        assert!(u == 0 || d == 0);
        let wrap = |cx: &mut Ctx, kind: i64, x: i64, dd: i64| {
            cx.buf.push(2);
            cx.buf.push(x as i32);
            cx.buf.push((4 * dd + kind) as i32);
            cx.nodes += 1;
            Cref::Ref(1, cx.nodes as i64 - 1, d)
        };
        let r = match go(cx, &s2, false) {
            Cref::Const(v) if d >= 0 => Cref::Const(v),
            Cref::Const(v) => wrap(cx, 0, v, 0),
            Cref::Ref(kind, x, 0) => Cref::Ref(kind, x, d),
            Cref::Ref(kind, x, dd) if d == 0 => Cref::Ref(kind, x, dd),
            Cref::Ref(kind, x, dd) => wrap(cx, kind, x, dd),
        };
        if u == 0 {
            return r;
        }
        match r {
            Cref::Const(0) => r,
            Cref::Const(v) => {
                cx.buf.push(((u << 16) | 2) as i32);
                cx.buf.push(v as i32);
                cx.buf.push(0);
                cx.nodes += 1;
                Cref::Ref(1, cx.nodes as i64 - 1, 0)
            }
            Cref::Ref(kind, x, dd) => {
                cx.buf.push(((u << 16) | 2) as i32);
                cx.buf.push(x as i32);
                cx.buf.push((4 * dd + kind) as i32);
                cx.nodes += 1;
                Cref::Ref(1, cx.nodes as i64 - 1, 0)
            }
        }
    }
    let lost = if c.lose() == NINF { 0 } else { 1 };
    let mut cx = Ctx { c, tgt, local: HashMap::default(), buf: vec![], nodes: 0, lost, won: 1 - lost };
    let root = go(&mut cx, s, true);
    match root {
        Cref::Ref(1, n, 0) if n as usize == cx.nodes - 1 => {}
        r => {
            cx.buf.push(2);
            push2(&mut cx.buf, r);
            cx.nodes += 1;
        }
    }
    (cx.buf, cx.nodes)
}

/// Values are stored as 32-bit ints, the sentinels as the int32 extremes.
pub fn to32(v: i64) -> i32 {
    if v <= NINF { -0x4000_0000 } else if v >= INF { 0x3fff_ffff } else { v as i32 }
}
pub fn of32(v: i32) -> i64 {
    if v == -0x4000_0000 { NINF } else if v == 0x3fff_ffff { INF } else { v as i64 }
}

/// The packed program format, made from a compiled program by `pack`:
///
///   varint nt, then nt turn-start references (b<<5|u), ascending, as
///   varint differences from the previous one (the first from 0);
///   varint nodes, then per node varint (cnt<<1 | theirs) and cnt children.
///
/// A child is varint (val<<3 | ext<<2 | kind): kind 0 a constant (val 0 =
/// ninf, 1 = inf), kind 1 the node val places before this one, kind 2 entry
/// val of the turn-start table. With ext, varints zigzag(d) and g follow: the
/// child's value is ninf when the level is at most g, and otherwise the
/// value with the change d in B's life applied, as in `run`. Single-child
/// nodes are folded into the references to them, identical nodes are
/// shared, and the root is the last node.
pub fn pack(prog: &[i32], nodes: usize) -> Vec<u8> {
    // a reference: (kind, x, d, g) with x a node, constant or turn start
    type R = (u8, i64, i64, i64);
    let mut pc = 0;
    // per old node: its new form, either a reference that replaces it or a
    // new node index
    let mut sub: Vec<R> = Vec::with_capacity(nodes);
    let mut out_nodes: Vec<(bool, Vec<R>)> = vec![];
    let mut cons: HashMap<(bool, Vec<R>), i64> = HashMap::default();
    for n in 0..nodes {
        let h = prog[pc] as i64;
        let theirs = h & 1 == 1;
        let cnt = ((h >> 1) & 0x7fff) as usize;
        let g = h >> 16;
        pc += 1;
        let mut ks: Vec<R> = (0..cnt)
            .map(|i| {
                let (x, kd) = (prog[pc + 2 * i] as i64, prog[pc + 2 * i + 1] as i64);
                let (kind, d) = (kd & 3, kd >> 2);
                match kind {
                    1 => {
                        let r = sub[x as usize];
                        if d == 0 {
                            r
                        } else if r.2 == 0 && r.3 == 0 {
                            (r.0, r.1, d, 0)
                        } else {
                            // a folded reference with its own d or guard:
                            // keep it as a node of its own
                            let key = (false, vec![r]);
                            let next = out_nodes.len() as i64;
                            let id = *cons.entry(key.clone()).or_insert_with(|| {
                                out_nodes.push(key);
                                next
                            });
                            (1, id, d, 0)
                        }
                    }
                    k => (k as u8, x, d, 0),
                }
            })
            .collect();
        pc += 2 * cnt;
        if g > 0 {
            assert!(cnt == 1);
            // a guard over a reference that has a guard or a d of its own
            // can't merge with it
            let r = ks[0];
            ks[0] = if r.3 == 0 { (r.0, r.1, r.2, g) } else {
                let key = (false, vec![r]);
                let next = out_nodes.len() as i64;
                let id = *cons.entry(key.clone()).or_insert_with(|| {
                    out_nodes.push(key);
                    next
                });
                (1, id, 0, g)
            };
        }
        ks.sort();
        ks.dedup();
        let r = if ks.len() == 1 && n + 1 < nodes {
            ks[0]
        } else {
            let key = (if ks.len() == 1 { false } else { theirs }, ks);
            let next = out_nodes.len() as i64;
            let id = *cons.entry(key.clone()).or_insert_with(|| {
                out_nodes.push(key);
                next
            });
            (1, id, 0, 0)
        };
        sub.push(r);
    }
    // the root must be the last node
    let root = sub[nodes - 1];
    assert!(root.0 == 1 && root.2 == 0 && root.3 == 0);
    let root = root.1 as usize;
    // keep the nodes the root reaches, in order
    let reach = |out_nodes: &Vec<(bool, Vec<R>)>| {
        let mut live = vec![false; out_nodes.len()];
        let mut uses = vec![0u32; out_nodes.len()];
        live[root] = true;
        for i in (0..=root).rev() {
            if live[i] {
                for r in &out_nodes[i].1 {
                    if r.0 == 1 {
                        live[r.1 as usize] = true;
                        uses[r.1 as usize] += 1;
                    }
                }
            }
        }
        (live, uses)
    };
    // flatten: a child node with the same operator, read once and with no
    // d or guard, merges into its parent (min/max are associative)
    let (live, uses) = reach(&out_nodes);
    for i in 0..=root {
        if !live[i] || out_nodes[i].1.len() < 2 {
            continue;
        }
        let theirs = out_nodes[i].0;
        let mut ks = Vec::with_capacity(out_nodes[i].1.len());
        let mut merged = false;
        for &r in &out_nodes[i].1 {
            let x = r.1 as usize;
            if r.0 == 1 && r.2 == 0 && r.3 == 0 && uses[x] == 1 && out_nodes[x].1.len() > 1 && out_nodes[x].0 == theirs {
                ks.extend_from_slice(&out_nodes[x].1);
                merged = true;
            } else {
                ks.push(r);
            }
        }
        if merged {
            ks.sort();
            ks.dedup();
            out_nodes[i].1 = ks;
        }
    }
    let (live, _) = reach(&out_nodes);
    let mut idx = vec![0i64; out_nodes.len()];
    let mut k = 0;
    for i in 0..=root {
        if live[i] {
            idx[i] = k;
            k += 1;
        }
    }
    let mut ts: Vec<i64> = out_nodes.iter().enumerate().filter(|(i, _)| live[*i]).flat_map(|(_, n)| n.1.iter().filter(|r| r.0 == 2).map(|r| r.1)).collect();
    ts.sort_unstable();
    ts.dedup();
    let mut buf = Vec::with_capacity(16 + 4 * ts.len() + 4 * out_nodes.len());
    let varint = |buf: &mut Vec<u8>, mut v: u64| {
        while v >= 0x80 {
            buf.push((v as u8) | 0x80);
            v >>= 7;
        }
        buf.push(v as u8);
    };
    varint(&mut buf, ts.len() as u64);
    let mut prev = 0;
    for &t in &ts {
        varint(&mut buf, (t - prev) as u64);
        prev = t;
    }
    varint(&mut buf, k as u64);
    for i in 0..=root {
        if !live[i] {
            continue;
        }
        let (theirs, ks) = &out_nodes[i];
        varint(&mut buf, ((ks.len() as u64) << 1) | *theirs as u64);
        for &(kind, x, d, g) in ks {
            let val = match kind {
                0 => x as u64,
                1 => (idx[i] - idx[x as usize]) as u64,
                _ => ts.binary_search(&x).unwrap() as u64,
            };
            let ext = d != 0 || g != 0;
            varint(&mut buf, (val << 3) | ((ext as u64) << 2) | kind as u64);
            if ext {
                varint(&mut buf, ((d << 1) ^ (d >> 63)) as u64);
                varint(&mut buf, g as u64);
            }
        }
    }
    buf
}

#[inline(always)]
fn get_varint(p: &[u8], pc: &mut usize) -> u64 {
    let mut v = 0u64;
    let mut sh = 0;
    loop {
        let b = p[*pc];
        *pc += 1;
        v |= ((b & 0x7f) as u64) << sh;
        if b < 0x80 {
            return v;
        }
        sh += 7;
    }
}

/// The turn-start references of a packed program.
pub fn packed_targets(p: &[u8]) -> impl Iterator<Item = i64> + '_ {
    let mut pc = 0;
    let nt = get_varint(p, &mut pc) as usize;
    let mut x = 0;
    (0..nt).map(move |_| {
        x += get_varint(p, &mut pc) as i64;
        x
    })
}

/// Evaluate a packed program at A-life level `l`. `nv` and `tv` are scratch.
#[inline]
pub fn run_packed(c: &Cfg, l: i64, value: &dyn Fn(i64) -> i64, p: &[u8], nv: &mut Vec<i64>, tv: &mut Vec<i64>) -> i64 {
    let up = c.up();
    let lose = c.lose();
    let mut pc = 0;
    let nt = get_varint(p, &mut pc) as usize;
    tv.clear();
    let mut x = 0;
    for _ in 0..nt {
        x += get_varint(p, &mut pc) as i64;
        tv.push(value(x));
    }
    let nodes = get_varint(p, &mut pc) as usize;
    nv.clear();
    for n in 0..nodes {
        let h = get_varint(p, &mut pc);
        let mine = h & 1 == 0;
        let cnt = h >> 1;
        let mut acc = if mine { lose } else if up { NINF } else { INF };
        for _ in 0..cnt {
            let w = get_varint(p, &mut pc);
            let val = (w >> 3) as usize;
            let mut v = match w & 3 {
                0 => if val == 0 { NINF } else { INF },
                1 => nv[n - val],
                _ => tv[val],
            };
            if w & 4 != 0 {
                let z = get_varint(p, &mut pc) as i64;
                let d = (z >> 1) ^ -(z & 1);
                let g = get_varint(p, &mut pc) as i64;
                if g > 0 && l <= g {
                    v = NINF;
                } else {
                    v = shift(v, d);
                    if d < 0 {
                        v = if up { (1 - d).max(v) } else { (-d).max(v) };
                    }
                }
            }
            acc = if mine == up { acc.min(v) } else { acc.max(v) };
        }
        nv.push(acc);
    }
    nv[nodes - 1]
}
