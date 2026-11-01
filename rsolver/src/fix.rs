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
    /// The parametric big Walker (`TCB_BIG=1`, A-safe or B-win): see `Line`.
    pub big: bool,
    /// The protagonist's choice between lines is the best at n = bigref
    /// (`TCB_BIGREF`).
    pub bigref: i64,
    /// Check every BIG state against BIG + 3 (`TCB_BIGCHECK=1`; always on
    /// in debug builds).
    pub bigcheck: bool,
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
    pub fn strict(&self, r: &str) -> bool {
        !self.lax.iter().any(|x| x == r)
    }
    pub fn moves_of(&self, set: MoveSet, s: &State) -> Vec<Move> {
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
                    Move::Pump(i) => {
                        let n = ps.bf[*i as usize].counters;
                        n < self.t
                            || (self.big
                                && self.prot == Player::A
                                && (n == self.big_k() || (n == self.t && !ps.bf.iter().any(|w| w.counters == self.big_k()))))
                    }
                    _ => true,
                })
                .collect()
        } else {
            self.moves_of(self.theirs, s)
        }
    }

    /// Clamp after a step: the opponent's Walkers at most huge, the
    /// protagonist's Thopters at most tt (tapped ones go first), and with
    /// `TCB_LAX=many` the opponent's at most ott.
    pub fn clamp(&self, s: &mut State) {
        let huge = self.huge();
        let cut = |sd: &mut Side, tt: u32| {
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
                cut(os, self.ott);
            }
        }
        cut(s.side_mut(self.prot), self.tt);
    }

    /// Does this move make an exact huge size matter (a loss for the protagonist)?
    pub fn huge_event(&self, s: &State, m: &Move) -> bool {
        if !(matches!(s.pend, Pending::ChooseDamage) && matches!(m, Move::Assign(_))) {
            return false;
        }
        if self.big && self.prot == Player::B {
            // B-win BIG mode: A's only Walker at the saturation size is BIG
            // (a second one is a loss for B, see `big_flags`). Its
            // unblocked hit is an `F_HIT` edge, not a huge event. The other
            // two huge events can't happen, because K exceeds every total
            // of B's (checked when the mode starts); check that here.
            let huge = self.huge();
            let att = s.side(s.active);
            let def = s.side(s.active.opp());
            for (&i, bs) in s.cmb.atk.iter().zip(s.cmb.blk.iter()) {
                if s.active == Player::A && att.bf[i as usize].counters >= huge {
                    assert!(bs.iter().map(|&b| blocker_toughness(def, b)).sum::<u32>() < huge, "BIG blocked by a total of K");
                }
                if s.active == Player::B {
                    assert!(att.bf[i as usize].counters < huge, "a B Walker of K");
                }
            }
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

    /// BIG mode: the size K of a BIG Walker, which stands for K + n
    /// counters for an unknown n >= 0. A-safe: t + 1 (A's cap plus one).
    /// B-win: ot + 1 (where A's Walkers would saturate).
    pub fn big_k(&self) -> u32 {
        if self.prot == Player::A { self.t + 1 } else { self.ot + 1 }
    }

    /// BIG mode: the flags of a legal move's edge. `F_PUMP`: a pump on the
    /// BIG Walker (n -> n + 1; the caller puts its counters back to K).
    /// `F_CREATE`: a pump from K - 1 to K, which makes a BIG Walker with
    /// n = 0. `F_SECOND`: the same pump while A already has a BIG Walker;
    /// the edge is a loss for the protagonist (A-safe forbids the pump, and
    /// in B-win it counts as a huge event: sound, pessimistic for B).
    /// `F_HIT`: combat damage in which the BIG Walker is unblocked, so B
    /// takes n more than the model deals.
    pub fn big_flags(&self, s: &State, m: &Move) -> i64 {
        if !self.big {
            return 0;
        }
        let k = self.big_k();
        match (&s.pend, m) {
            (Pending::Window(_, Player::A, _), Move::Pump(i)) => {
                let before = s.side_a.bf[*i as usize].counters;
                if before == k {
                    F_PUMP
                } else if before == k - 1 {
                    if s.side_a.bf.iter().any(|w| w.counters == k) { F_SECOND } else { F_CREATE }
                } else {
                    0
                }
            }
            (Pending::ChooseDamage, Move::Assign(_)) if s.active == Player::A => {
                let hit = s.cmb.atk.iter().zip(s.cmb.blk.iter()).any(|(&i, bs)| bs.is_empty() && s.side_a.bf[i as usize].counters == k);
                if hit { F_HIT } else { 0 }
            }
            _ => 0,
        }
    }

    /// BIG mode: the step of a legal move with the BIG Walker kept at K.
    pub fn big_fix(&self, f: i64, m: &Move, s2: &mut State) {
        if f & F_PUMP != 0 {
            let Move::Pump(i) = m else { unreachable!() };
            // K + 1, or already K where the opponent's Walkers saturate
            let w = &mut s2.side_a.bf[*i as usize];
            assert!(w.counters == self.big_k() + 1 || w.counters == self.big_k());
            w.counters = self.big_k();
        }
    }

    pub fn bigcheck_on(&self) -> bool {
        self.big && (cfg!(debug_assertions) || self.bigcheck)
    }

    /// BIG mode: check that a state with a BIG Walker behaves the same with
    /// BIG at K + 3, except for B's life: the same moves, the same huge
    /// events and Thopter losses, the same successors (BIG still at +3),
    /// and B 3 life lower exactly on `F_HIT` edges. Also that BIG never
    /// dies. This is the claim that the only dependence on n is damage to B.
    pub fn big_check(&self, s: &State) {
        const E: u32 = 3;
        let k = self.big_k();
        if !s.side_a.bf.iter().any(|w| w.counters == k) {
            return;
        }
        let mut sp = s.clone();
        for w in sp.side_a.bf.iter_mut() {
            if w.counters == k {
                w.counters += E;
            }
        }
        let set = if to_move(s) == self.prot { self.mine } else { self.theirs };
        let ms = self.moves_of(set, s);
        assert_eq!(ms, self.moves_of(set, &sp), "BIG: the moves depend on n at {s:?}");
        for m in &ms {
            assert_eq!(self.huge_event(s, m), self.huge_event(&sp, m), "BIG: a huge event depends on n at {s:?}, {m:?}");
            let mut a = step(s, m);
            self.clamp(&mut a);
            let mut b = step(&sp, m);
            self.clamp(&mut b);
            assert_eq!(self.too_many(&a), self.too_many(&b));
            assert!(a.side_a.bf.iter().any(|w| w.counters >= k), "BIG died at {s:?}, {m:?}");
            for w in b.side_a.bf.iter_mut() {
                if w.counters >= k + E {
                    w.counters -= E;
                }
            }
            let hit = matches!(m, Move::Assign(_)) && self.big_flags(s, m) & F_HIT != 0;
            assert_eq!(a.side_b.life, b.side_b.life + if hit { E } else { 0 }, "BIG: damage to B at {s:?}, {m:?}");
            b.side_b.life = a.side_b.life;
            assert!(a == b, "BIG: the step depends on n at {s:?}, {m:?}");
        }
    }

    pub fn too_many(&self, s: &State) -> bool {
        self.strict("many") && {
            let os = s.side(self.prot.opp());
            os.thop_u + os.thop_t > self.ott
        }
    }
}

/// Edge flags in BIG mode (see `Cfg::big_flags`).
pub const F_HIT: i64 = 1;
pub const F_PUMP: i64 = 2;
pub const F_CREATE: i64 = 4;
pub const F_SECOND: i64 = 8;

/// Edges that make a second BIG Walker (B-win; see `F_SECOND`): how many
/// were compiled, and in how many turns.
pub static SECOND_EDGES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static SECOND_TURNS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// A value in BIG mode, where the position's BIG Walker has K + n
/// counters. A-safe: A is safe at B life L whenever L <= c + b * n (a
/// lower bound for every n >= 0). B-win: B wins whenever L >= c + b * n (an
/// upper bound for every n >= 0). Positions with no BIG Walker have b = 0.
/// INF and NINF (in c, with b = 0) are kept as special values.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Line {
    pub c: i64,
    pub b: i64,
}
pub const LINF: Line = Line { c: INF, b: 0 };
pub const LNINF: Line = Line { c: NINF, b: 0 };
/// The largest b kept.
pub const BMAX: i64 = 8;

impl Line {
    pub fn special(self) -> bool {
        self.c >= INF || self.c <= NINF
    }
}

/// B's nodes: componentwise min, a lower bound on the pointwise min for
/// every n >= 0.
#[inline]
pub fn lmin(a: Line, b: Line) -> Line {
    if a.c >= INF {
        b
    } else if b.c >= INF {
        a
    } else if a.c <= NINF || b.c <= NINF {
        LNINF
    } else {
        Line { c: a.c.min(b.c), b: a.b.min(b.b) }
    }
}

/// A's nodes: one of the two, the larger at n = r (ties by c, then b, so
/// that this is the max of a total order: associative and commutative).
/// Either choice is a lower bound on the max.
///
/// With r < 0 (`TCB_LAX=adapt`, an unsound diagnostic) it is the
/// componentwise max instead: as if A could choose a different move for
/// every n. That is optimistic for A (above the pointwise max).
#[inline]
pub fn lpick(r: i64, a: Line, b: Line) -> Line {
    if r < 0 {
        return lmaxc(a, b);
    }
    if a.c >= INF || b.c >= INF {
        LINF
    } else if a.c <= NINF {
        b
    } else if b.c <= NINF {
        a
    } else if (a.c + a.b * r, a.c, a.b) >= (b.c + b.b * r, b.c, b.b) {
        a
    } else {
        b
    }
}

/// B-win, A's nodes: componentwise max, an upper bound on the pointwise
/// max for every n >= 0. INF (B never wins) absorbs, NINF is the identity.
#[inline]
pub fn lmaxc(a: Line, b: Line) -> Line {
    if a.c <= NINF {
        b
    } else if b.c <= NINF {
        a
    } else if a.c >= INF || b.c >= INF {
        LINF
    } else {
        Line { c: a.c.max(b.c), b: a.b.max(b.b) }
    }
}

/// B-win, B's nodes: one of the two, the smaller at n = r (ties by c,
/// then b: the min of a total order). Either is an upper bound on the min.
#[inline]
pub fn lpick_low(r: i64, a: Line, b: Line) -> Line {
    if a.c <= NINF || b.c <= NINF {
        LNINF
    } else if a.c >= INF {
        b
    } else if b.c >= INF {
        a
    } else if (a.c + a.b * r, a.c, a.b) <= (b.c + b.b * r, b.c, b.b) {
        a
    } else {
        b
    }
}

/// The protagonist's node operation (A-safe: `lpick`; B-win: `lpick_low`).
#[inline]
pub fn lbest(up: bool, r: i64, a: Line, b: Line) -> Line {
    if up { lpick_low(r, a, b) } else { lpick(r, a, b) }
}
/// The opponent's node operation (A-safe: `lmin`; B-win: `lmaxc`).
#[inline]
pub fn lworst(up: bool, a: Line, b: Line) -> Line {
    if up { lmaxc(a, b) } else { lmin(a, b) }
}

/// An edge in BIG mode: the child's value seen from the parent. `F_CREATE`
/// reads the child at n = 0, `F_PUMP` at n + 1, a change d in B's life
/// shifts c, and `F_HIT` adds the n extra damage. After combat damage
/// (d < 0) B's death is folded in as in `shift`: B dies when L <= -d (+ n
/// with `F_HIT`). A-safe (`up` false): the larger of the two lines at `r`
/// is kept (A is safe either way). B-win (`up`): B must also survive, L >=
/// 1 - d (+ n with `F_HIT`), and the componentwise max is kept, an upper
/// bound on the pointwise max.
#[inline]
pub fn ltrans(up: bool, r: i64, mut v: Line, d: i64, f: i64) -> Line {
    let hit = (f & F_HIT != 0) as i64;
    if !v.special() {
        if f & F_CREATE != 0 {
            v.b = 0;
        }
        if f & F_PUMP != 0 {
            v.c += v.b;
        }
        v.c -= d;
        v.b += hit;
    }
    if d < 0 {
        v = if up { lmaxc(Line { c: 1 - d, b: hit }, v) } else { lpick(r, Line { c: -d, b: hit }, v) };
    } else {
        debug_assert!(hit == 0);
    }
    v
}

impl Cfg {
    /// Normalise a turn-start line (A-safe): c at most lmax, b at most
    /// BMAX, a line that is below 1 at n = 0 and doesn't grow is lost, and
    /// so is one with c below -lmax (which keeps the iteration finite). All
    /// of these only lower the value.
    pub fn norm_big(&self, v: Line) -> Line {
        if self.up() {
            // B-win: only raise. B needs at least 1 life; more than lmax, or
            // b above BMAX, is "never"; a negative b is raised to 0.
            if v.c <= NINF {
                return Line { c: 1, b: 0 };
            }
            if v.c >= INF || v.c > self.lmax || v.b > BMAX {
                return LINF;
            }
            return Line { c: v.c.max(1), b: v.b.max(0) };
        }
        if v.c >= INF {
            return LINF;
        }
        if v.c <= NINF || v.b < 0 {
            return LNINF;
        }
        let (c, b) = (v.c.min(self.lmax), v.b.min(BMAX));
        if (b <= 0 && c < 1) || c < -self.lmax {
            LNINF
        } else {
            Line { c, b }
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

pub fn eval_go(c: &Cfg, lookup: &mut dyn FnMut(&[u8]) -> i64, local: &mut HashMap<State, i64>, s: &State, root: bool) -> i64 {
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

/// `eval_turn` in BIG mode, with lines for values.
pub fn eval_turn_big(c: &Cfg, lookup: &mut dyn FnMut(&[u8]) -> Line, s: &State) -> Line {
    let mut local: HashMap<State, Line> = HashMap::default();
    eval_go_big(c, lookup, &mut local, s, true)
}

pub fn eval_go_big(c: &Cfg, lookup: &mut dyn FnMut(&[u8]) -> Line, local: &mut HashMap<State, Line>, s: &State, root: bool) -> Line {
    match winner(s) {
        Some(Player::B) => return LNINF,
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
    let up = c.up();
    let lost = if up { LINF } else { LNINF };
    let mut acc = if mine { lost } else if up { LNINF } else { LINF };
    for m in c.moves_for(s) {
        let v = if c.huge_event(s, &m) {
            lost
        } else {
            let mut s2 = step(s, &m);
            c.clamp(&mut s2);
            let f = c.big_flags(s, &m);
            if f & F_SECOND != 0 && !c.strict("second") {
                // dropped (TCB_LAX=second): what the mover never picks
                if mine { lost } else if up { LNINF } else { LINF }
            } else if c.too_many(&s2) || f & F_SECOND != 0 {
                lost
            } else {
                c.big_fix(f, &m, &mut s2);
                let d = s2.side_b.life as i64 - s.side_b.life as i64;
                ltrans(up, c.bigref, eval_go_big(c, lookup, local, &s2, false), d, f)
            }
        };
        acc = if mine { lbest(up, c.bigref, acc, v) } else { lworst(up, acc, v) };
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
/// reference of kind 1 (node) or 2 (turn start) with a change d in B's life
/// and BIG-mode edge flags f (0 outside BIG mode).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
enum Cref {
    Const(i64),
    Ref(i64, i64, i64, i64),
}

/// A child's second word in a compiled program: 4d + kind, or with BIG
/// flags f, 4(32d + 4f + kind) + 3.
fn enc_kd(kind: i64, d: i64, f: i64) -> i32 {
    if f == 0 { (4 * d + kind) as i32 } else { (4 * (32 * d + 4 * f + kind) + 3) as i32 }
}
/// (kind, d, f) of a child's second word.
fn dec_kd(kd: i64) -> (i64, i64, i64) {
    if kd & 3 == 3 {
        let inner = kd >> 2;
        (inner & 3, inner >> 5, (inner >> 2) & 7)
    } else {
        (kd & 3, kd >> 2, 0)
    }
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
        // edges with `F_SECOND`
        second: u64,
    }
    fn push2(buf: &mut Vec<i32>, r: Cref) {
        match r {
            Cref::Ref(kind, x, d, f) => {
                buf.push(x as i32);
                buf.push(enc_kd(kind, d, f));
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
            return Cref::Ref(2, (cx.tgt)(s), 0, 0);
        }
        let k = hashed(normal(false, s));
        if let Some(&r) = cx.local.get(&k) {
            return r;
        }
        if cx.c.bigcheck_on() {
            cx.c.big_check(s);
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
                    Cref::Ref(1, cx.nodes as i64 - 1, 0, 0)
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
        let f = cx.c.big_flags(s, m);
        if f & F_SECOND != 0 {
            cx.second += 1;
            // TCB_LAX=second (unsound, a diagnostic): drop the move instead
            return Cref::Const(if cx.c.strict("second") { cx.lost } else { cx.won });
        }
        cx.c.big_fix(f, m, &mut s2);
        let d = s2.side_b.life as i64 - s.side_b.life as i64;
        let u = s.side_a.life as i64 - s2.side_a.life as i64;
        assert!(u == 0 || d == 0);
        assert!(f == 0 || u == 0);
        // a reference to a new node holding the child (kind, x, dd, ff),
        // with this edge's d and f
        let wrap = |cx: &mut Ctx, kind: i64, x: i64, dd: i64, ff: i64| {
            cx.buf.push(2);
            cx.buf.push(x as i32);
            cx.buf.push(enc_kd(kind, dd, ff));
            cx.nodes += 1;
            Cref::Ref(1, cx.nodes as i64 - 1, d, f)
        };
        let r = match go(cx, &s2, false) {
            Cref::Const(v) if d >= 0 => Cref::Const(v),
            Cref::Const(v) => wrap(cx, 0, v, 0, 0),
            Cref::Ref(kind, x, 0, 0) => Cref::Ref(kind, x, d, f),
            Cref::Ref(kind, x, dd, ff) if d == 0 && f == 0 => Cref::Ref(kind, x, dd, ff),
            Cref::Ref(kind, x, dd, ff) => wrap(cx, kind, x, dd, ff),
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
                Cref::Ref(1, cx.nodes as i64 - 1, 0, 0)
            }
            Cref::Ref(kind, x, dd, ff) => {
                cx.buf.push(((u << 16) | 2) as i32);
                cx.buf.push(x as i32);
                cx.buf.push(enc_kd(kind, dd, ff));
                cx.nodes += 1;
                Cref::Ref(1, cx.nodes as i64 - 1, 0, 0)
            }
        }
    }
    let lost = if c.lose() == NINF { 0 } else { 1 };
    let mut cx = Ctx { c, tgt, local: HashMap::default(), buf: vec![], nodes: 0, lost, won: 1 - lost, second: 0 };
    let root = go(&mut cx, s, true);
    if cx.second > 0 {
        use std::sync::atomic::Ordering::Relaxed;
        SECOND_EDGES.fetch_add(cx.second, Relaxed);
        SECOND_TURNS.fetch_add(1, Relaxed);
    }
    match root {
        Cref::Ref(1, n, 0, 0) if n as usize == cx.nodes - 1 => {}
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
///
/// With `big` (BIG mode), the extension is three varints: zigzag(d), g and
/// the edge flags f, applied as in `ltrans` after the guard. Outside BIG
/// mode f is always 0 and the format is unchanged.
pub fn pack(prog: &[i32], nodes: usize, big: bool) -> Vec<u8> {
    // a reference: (kind, x, d, g, f) with x a node, constant or turn start
    type R = (u8, i64, i64, i64, i64);
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
                let (kind, d, f) = dec_kd(kd);
                assert!(big || f == 0);
                match kind {
                    1 => {
                        let r = sub[x as usize];
                        if d == 0 && f == 0 {
                            r
                        } else if r.2 == 0 && r.3 == 0 && r.4 == 0 {
                            (r.0, r.1, d, 0, f)
                        } else {
                            // a folded reference with its own d or guard:
                            // keep it as a node of its own
                            let key = (false, vec![r]);
                            let next = out_nodes.len() as i64;
                            let id = *cons.entry(key.clone()).or_insert_with(|| {
                                out_nodes.push(key);
                                next
                            });
                            (1, id, d, 0, f)
                        }
                    }
                    k => (k as u8, x, d, 0, f),
                }
            })
            .collect();
        pc += 2 * cnt;
        if g > 0 {
            assert!(cnt == 1);
            // a guard over a reference that has a guard or a d of its own
            // can't merge with it
            let r = ks[0];
            ks[0] = if r.3 == 0 { (r.0, r.1, r.2, g, r.4) } else {
                let key = (false, vec![r]);
                let next = out_nodes.len() as i64;
                let id = *cons.entry(key.clone()).or_insert_with(|| {
                    out_nodes.push(key);
                    next
                });
                (1, id, 0, g, 0)
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
            (1, id, 0, 0, 0)
        };
        sub.push(r);
    }
    // the root must be the last node
    let root = sub[nodes - 1];
    assert!(root.0 == 1 && root.2 == 0 && root.3 == 0 && root.4 == 0);
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
            if r.0 == 1 && r.2 == 0 && r.3 == 0 && r.4 == 0 && uses[x] == 1 && out_nodes[x].1.len() > 1 && out_nodes[x].0 == theirs {
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
        for &(kind, x, d, g, f) in ks {
            let val = match kind {
                0 => x as u64,
                1 => (idx[i] - idx[x as usize]) as u64,
                _ => ts.binary_search(&x).unwrap() as u64,
            };
            let ext = d != 0 || g != 0 || f != 0;
            varint(&mut buf, (val << 3) | ((ext as u64) << 2) | kind as u64);
            if ext {
                varint(&mut buf, ((d << 1) ^ (d >> 63)) as u64);
                varint(&mut buf, g as u64);
                if big {
                    varint(&mut buf, f as u64);
                }
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

/// `run_packed` in BIG mode (a program packed with `big`), with lines.
#[inline]
pub fn run_packed_big(c: &Cfg, l: i64, value: &dyn Fn(i64) -> Line, p: &[u8], nv: &mut Vec<Line>, tv: &mut Vec<Line>) -> Line {
    debug_assert!(c.big);
    let r = c.bigref;
    let up = c.up();
    let lost = if up { LINF } else { LNINF };
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
        let mut acc = if mine { lost } else if up { LNINF } else { LINF };
        for _ in 0..cnt {
            let w = get_varint(p, &mut pc);
            let val = (w >> 3) as usize;
            let mut v = match w & 3 {
                0 => if val == 0 { LNINF } else { LINF },
                1 => nv[n - val],
                _ => tv[val],
            };
            if w & 4 != 0 {
                let z = get_varint(p, &mut pc) as i64;
                let d = (z >> 1) ^ -(z & 1);
                let g = get_varint(p, &mut pc) as i64;
                let f = get_varint(p, &mut pc) as i64;
                v = if g > 0 && l <= g { LNINF } else { ltrans(up, r, v, d, f) };
            }
            acc = if mine { lbest(up, r, acc, v) } else { lworst(up, acc, v) };
        }
        nv.push(acc);
    }
    nv[nodes - 1]
}
