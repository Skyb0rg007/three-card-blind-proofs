//! Certified play for B when B goes first.
//!
//! The certificate is the table Rocq checks for the B-first theorem
//! (`proofs/bfirst/Data.v`: the arrays `K1`, `K2`, `RV` and the constants
//! `H`, `ott`, `tt`, `fuel`). This module is a line-by-line port of what
//! Rocq runs on it:
//!
//! * `key`, `entry`, `huge_event`, `too_many`, `is_turn_start` from
//!   `proofs/core/Checker.v`;
//! * `enc`, `dec`, `lower`/`start`, `scan`, `scan_below`, `lookup`, `below`,
//!   `rank_of`, `val_of` from `proofs/core/Packed.v`;
//! * `check_win` from `proofs/core/WinCert.v` (with Packed's `hint`, which
//!   lets B try every move).
//!
//! Rocq proves that every record passes `check_win`, and that a passing
//! record is a real win for B (`WinCert.cert_wins`). B plays from it like
//! this:
//!
//! * At each turn start `t` (in the sense of `Checker.is_turn_start`), B
//!   takes the record of `key t` with the lowest rank among those that need
//!   at most B's actual life. B then keeps an abstract copy `s` of the game
//!   for the rest of the turn: `s = entry (key t) life` (A's Walkers clamped
//!   at `H` counters, A's graveyard dropped, B's Thopters cut to `tt`, as in
//!   the certificate), stepped with the same moves as the real game.
//! * At each of B's decisions, B plays the first move (in model order)
//!   after which `check_win` still passes, which is the move the checker
//!   itself would find. A's moves need no choice: `check_win` passed for
//!   every one of them.
//!
//! The abstract state stands for the real one in the sense of
//! `Checker.R`, so by `WinCert.check_win_wins` every position B reaches
//! this way is a real win, and ranks strictly fall from one turn start to
//! the next, so the game ends. B plays from its actual life rather than the
//! record's value; a record passes with the record's value (Rocq checked
//! that), and if it ever failed with the actual life B would fall back to
//! the record's value, which is the checked computation itself.

use crate::model::*;

// ---- the table ----

pub struct Table {
    pub h: u32,
    pub ott: u32,
    pub tt: u32,
    pub fuel: u32,
    pub k1: Vec<u64>,
    pub k2: Vec<u64>,
    pub rv: Vec<u32>,
}

/// The opening record named by `proofs/bfirst/BFirst.v`.
pub const OPENING_RANK: u32 = 587;
pub const OPENING_VAL: u32 = 17;

const MAGIC: &[u8; 8] = b"TCBWIN01";

fn fnv(h: &mut u64, x: u64) {
    for i in 0..8 {
        *h ^= (x >> (8 * i)) & 0xff;
        *h = h.wrapping_mul(0x100_0000_01b3);
    }
}

fn put_varint(out: &mut Vec<u8>, mut n: u64) {
    loop {
        let b = (n & 0x7f) as u8;
        n >>= 7;
        if n == 0 {
            out.push(b);
            return;
        }
        out.push(b | 0x80);
    }
}

struct Reader<'a> {
    b: &'a [u8],
    p: usize,
}

impl<'a> Reader<'a> {
    fn bytes(&mut self, n: usize) -> Result<&'a [u8], String> {
        let end = self.p.checked_add(n).filter(|&e| e <= self.b.len()).ok_or("table truncated")?;
        let r = &self.b[self.p..end];
        self.p = end;
        Ok(r)
    }
    fn u32(&mut self) -> Result<u32, String> {
        Ok(u32::from_le_bytes(self.bytes(4)?.try_into().unwrap()))
    }
    fn u64(&mut self) -> Result<u64, String> {
        Ok(u64::from_le_bytes(self.bytes(8)?.try_into().unwrap()))
    }
    fn varint(&mut self) -> Result<u64, String> {
        let mut n = 0u64;
        for shift in (0..64).step_by(7) {
            let b = *self.b.get(self.p).ok_or("table truncated")?;
            self.p += 1;
            n |= ((b & 0x7f) as u64) << shift;
            if b & 0x80 == 0 {
                return Ok(n);
            }
        }
        Err("bad varint".into())
    }
}

impl Table {
    /// Parse `Data.v` as written by `solver/main.exe certify-win-export`.
    pub fn parse_data_v(text: &str) -> Result<Table, String> {
        fn def<'a>(t: &'a str, name: &str, end: &str) -> Result<&'a str, String> {
            let pat = format!("\nDefinition {name} ");
            let i = t.find(&pat).ok_or(format!("Data.v has no {name}"))?;
            if t[i + 1..].contains(&pat) {
                return Err(format!("Data.v defines {name} twice"));
            }
            let rest = &t[i + pat.len()..];
            let j = rest.find(":=").ok_or("no :=")?;
            let rest = &rest[j + 2..];
            Ok(&rest[..rest.find(end).ok_or("no end")?])
        }
        fn nat(t: &str, name: &str) -> Result<u32, String> {
            def(t, name, ".\n")?.trim().parse().map_err(|e| format!("{name}: {e}"))
        }
        fn arr(t: &str, name: &str) -> Result<Vec<u64>, String> {
            let body = def(t, name, "%uint63.\n")?.trim();
            let body = body.strip_prefix(": array int :=").unwrap_or(body).trim();
            let body = body.strip_prefix("[|").ok_or(format!("{name}: not an array"))?;
            let bar = body.find('|').ok_or(format!("{name}: no default"))?;
            let default = body[bar + 1..].trim();
            if default != "0 : int |]" {
                return Err(format!("{name}: unexpected default {default:?}"));
            }
            body[..bar].split(';').map(|x| x.trim().parse::<u64>().map_err(|e| format!("{name}: {e}"))).collect()
        }
        let k1 = arr(text, "K1")?;
        let k2 = arr(text, "K2")?;
        let rv = arr(text, "RV")?;
        if k1.len() != k2.len() || k1.len() != rv.len() {
            return Err("array lengths differ".into());
        }
        let t = Table {
            h: nat(text, "H")?,
            ott: nat(text, "ott")?,
            tt: nat(text, "tt")?,
            fuel: nat(text, "fuel")?,
            k1,
            k2,
            rv: rv.into_iter().map(|x| u32::try_from(x).map_err(|_| "RV entry too big".to_string())).collect::<Result<_, _>>()?,
        };
        t.validate()?;
        Ok(t)
    }

    /// The table's arrays are sorted by key, then rank, with no duplicate
    /// (key, rank). Rocq doesn't need this for soundness, but its binary
    /// search (`lower`) only finds records in a sorted table, so the
    /// checker would have failed on an unsorted one.
    fn validate(&self) -> Result<(), String> {
        for j in 1..self.k1.len() {
            let a = (self.k1[j - 1], self.k2[j - 1], self.rank_of(j - 1));
            let b = (self.k1[j], self.k2[j], self.rank_of(j));
            if a >= b {
                return Err(format!("table not sorted at {j}"));
            }
        }
        if self.k1.iter().chain(&self.k2).any(|&x| x >> 63 != 0) {
            return Err("key out of 63-bit range".into());
        }
        Ok(())
    }

    pub fn len(&self) -> usize {
        self.k1.len()
    }

    pub fn is_empty(&self) -> bool {
        self.k1.is_empty()
    }

    pub fn checksum(&self) -> u64 {
        let mut h = 0xcbf2_9ce4_8422_2325u64;
        for j in 0..self.len() {
            fnv(&mut h, self.k1[j]);
            fnv(&mut h, self.k2[j]);
            fnv(&mut h, self.rv[j] as u64);
        }
        h
    }

    /// Compact binary form: a header, then three varint columns (K1 as
    /// deltas; K2 as deltas within a K1, else absolute; RV as is). The
    /// site gzips it.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut c1 = vec![];
        let mut c2 = vec![];
        let mut c3 = vec![];
        let (mut p1, mut p2) = (0u64, 0u64);
        for j in 0..self.len() {
            let (a, b) = (self.k1[j], self.k2[j]);
            put_varint(&mut c1, a - p1);
            put_varint(&mut c2, if a == p1 { b - p2 } else { b });
            put_varint(&mut c3, self.rv[j] as u64);
            p1 = a;
            p2 = b;
        }
        let mut out = MAGIC.to_vec();
        for x in [self.h, self.ott, self.tt, self.fuel, self.len() as u32] {
            out.extend(x.to_le_bytes());
        }
        out.extend(self.checksum().to_le_bytes());
        for c in [c1, c2, c3] {
            out.extend((c.len() as u32).to_le_bytes());
            out.extend(c);
        }
        out
    }

    pub fn from_bytes(b: &[u8]) -> Result<Table, String> {
        let mut r = Reader { b, p: 0 };
        if r.bytes(8)? != MAGIC {
            return Err("not a certificate table".into());
        }
        let (h, ott, tt, fuel, n) = (r.u32()?, r.u32()?, r.u32()?, r.u32()?, r.u32()? as usize);
        let sum = r.u64()?;
        let mut cols = vec![];
        for _ in 0..3 {
            let len = r.u32()? as usize;
            cols.push(r.bytes(len)?);
        }
        let mut k1 = Vec::with_capacity(n);
        let mut k2 = Vec::with_capacity(n);
        let mut rv = Vec::with_capacity(n);
        let mut r1 = Reader { b: cols[0], p: 0 };
        let mut r2 = Reader { b: cols[1], p: 0 };
        let mut r3 = Reader { b: cols[2], p: 0 };
        let (mut p1, mut p2) = (0u64, 0u64);
        for _ in 0..n {
            let d = r1.varint()?;
            let a = p1.checked_add(d).ok_or("bad K1")?;
            let x = r2.varint()?;
            let bb = if d == 0 { p2.checked_add(x).ok_or("bad K2")? } else { x };
            k1.push(a);
            k2.push(bb);
            rv.push(u32::try_from(r3.varint()?).map_err(|_| "bad RV")?);
            p1 = a;
            p2 = bb;
        }
        if r1.p != cols[0].len() || r2.p != cols[1].len() || r3.p != cols[2].len() || r.p != b.len() {
            return Err("trailing bytes in table".into());
        }
        let t = Table { h, ott, tt, fuel, k1, k2, rv };
        if t.checksum() != sum {
            return Err("table checksum mismatch".into());
        }
        t.validate()?;
        Ok(t)
    }

    // ---- Packed.v ----

    /// `rank_of j = nat_of_int 16 (shr RV.[j] 6)`.
    pub fn rank_of(&self, j: usize) -> u32 {
        (self.rv[j] >> 6) & 0xffff
    }

    /// `val_of j = nat_of_int 6 RV.[j]`.
    pub fn val_of(&self, j: usize) -> u32 {
        self.rv[j] & 0x3f
    }

    fn get1(&self, j: u64) -> u64 {
        // PArray.get out of bounds is the default, 0.
        self.k1.get(j as usize).copied().unwrap_or(0)
    }
    fn get2(&self, j: u64) -> u64 {
        self.k2.get(j as usize).copied().unwrap_or(0)
    }

    /// `lower f lo hi k1 k2`: the first index in [lo, hi) whose key is not
    /// below (k1, k2), with fuel `f`.
    fn lower(&self, f: u32, mut lo: u64, mut hi: u64, k1: u64, k2: u64) -> u64 {
        for _ in 0..f {
            if lo < hi {
                let mid = (lo + hi) >> 1;
                let (a1, a2) = (self.get1(mid), self.get2(mid));
                if a1 < k1 || (a1 == k1 && a2 < k2) {
                    lo = mid + 1;
                } else {
                    hi = mid;
                }
            } else {
                return lo;
            }
        }
        lo
    }

    /// `start k1 k2 = lower 32 0 (length K1) k1 k2`.
    pub fn start(&self, k1: u64, k2: u64) -> u64 {
        self.lower(32, 0, self.len() as u64, k1, k2)
    }

    fn at_key(&self, j: u64, k1: u64, k2: u64) -> bool {
        j < self.len() as u64 && self.k1[j as usize] == k1 && self.k2[j as usize] == k2
    }

    /// `scan 64 j k1 k2 r`.
    fn scan(&self, mut j: u64, k1: u64, k2: u64, r: u32) -> Option<usize> {
        for _ in 0..64 {
            if !self.at_key(j, k1, k2) {
                return None;
            }
            if self.rank_of(j as usize) == r {
                return Some(j as usize);
            }
            j += 1;
        }
        None
    }

    /// `scan_below 64 j k1 k2 r None`.
    fn scan_below(&self, mut j: u64, k1: u64, k2: u64, r: u32) -> Option<u32> {
        let mut best = None;
        for _ in 0..64 {
            if !self.at_key(j, k1, k2) {
                return best;
            }
            let rk = self.rank_of(j as usize);
            if rk < r {
                best = Some(rk);
            }
            j += 1;
        }
        best
    }

    /// `lookup s r`: the value of the record of `s` with rank `r`, if `s`
    /// decodes back to itself.
    pub fn lookup(&self, s: &State, r: u32) -> Option<u32> {
        let (k1, k2) = enc(s);
        let j = self.scan(self.start(k1, k2), k1, k2, r)?;
        if dec(k1, k2).as_ref() == Some(s) {
            Some(self.val_of(j))
        } else {
            None
        }
    }

    /// `below s r`: the highest rank of `s` below `r`.
    pub fn below(&self, s: &State, r: u32) -> Option<u32> {
        let (k1, k2) = enc(s);
        self.scan_below(self.start(k1, k2), k1, k2, r)
    }

    /// The state record `j` stands for: `entry (dec K1.[j] K2.[j]) (val_of j)`.
    pub fn record_state(&self, j: usize) -> Option<State> {
        dec(self.k1[j], self.k2[j]).map(|s| entry(&s, self.val_of(j)))
    }

    /// `record_ok j`.
    pub fn record_ok(&self, j: usize, nodes: &mut u64) -> bool {
        match self.record_state(j) {
            Some(s) => self.check_win(self.rank_of(j), self.fuel, true, &s, nodes),
            None => false,
        }
    }

    // ---- Checker.v ----

    /// `key s`: A's Walkers clamped at `H` counters, A's graveyard dropped,
    /// B's life zeroed and B's Thopters cut to `tt` (tapped ones first).
    pub fn key(&self, s: &State) -> State {
        let mut k = s.clone();
        for w in k.side_a.bf.iter_mut() {
            w.counters = w.counters.min(self.h);
        }
        k.side_a.gy_w = 0;
        k.side_b.life = 0;
        let sd = &mut k.side_b;
        let extra = (sd.thop_u + sd.thop_t).saturating_sub(self.tt);
        let dt = extra.min(sd.thop_t);
        sd.thop_u = sd.thop_u.saturating_sub(extra - dt);
        sd.thop_t -= dt;
        k
    }

    fn is_huge(&self, sd: &Side, i: u32) -> bool {
        self.h <= walker_power(sd, i)
    }

    pub fn huge_event(&self, s: &State) -> bool {
        if s.pend != Pending::ChooseDamage {
            return false;
        }
        let a = s.side(s.active);
        let d = s.side(s.active.opp());
        let mut fights = s.cmb.atk.iter().zip(s.cmb.blk.iter());
        match s.active {
            Player::A => fights.any(|(&i, bs)| {
                self.is_huge(a, i)
                    && (bs.is_empty() || self.h <= bs.iter().map(|&b| blocker_toughness(d, b)).sum::<u32>())
            }),
            Player::B => fights.any(|(&i, bs)| {
                self.h <= walker_power(a, i)
                    && bs.iter().any(|b| matches!(b, Blocker::BW(j) if self.is_huge(d, *j)))
            }),
        }
    }

    pub fn too_many(&self, s: &State) -> bool {
        self.ott < s.side_a.thop_u + s.side_a.thop_t
    }

    // ---- WinCert.v ----

    /// `check_win H ott tt lookup below hint r fuel root s`, with Packed's
    /// `hint` (every B move). `nodes` counts calls.
    pub fn check_win(&self, r: u32, fuel: u32, root: bool, s: &State, nodes: &mut u64) -> bool {
        *nodes += 1;
        if fuel == 0 {
            return false;
        }
        let f = fuel - 1;
        match winner(s) {
            Some(Player::B) => true,
            Some(Player::A) => false,
            None => {
                if !root && is_turn_start(s) {
                    let k = self.key(s);
                    match self.below(&k, r) {
                        Some(r2) if r2 < r => match self.lookup(&k, r2) {
                            Some(v) => v <= s.side_b.life,
                            None => false,
                        },
                        _ => false,
                    }
                } else if self.huge_event(s) {
                    false
                } else {
                    let ms = moves(s);
                    let mut next = |m: &Move| {
                        let s2 = step(s, m);
                        !self.too_many(&s2) && self.check_win(r, f, false, &s2, nodes)
                    };
                    match to_move(s) {
                        Player::B => ms.iter().any(&mut next),
                        Player::A => !ms.is_empty() && ms.iter().all(&mut next),
                    }
                }
            }
        }
    }
}

/// `Checker.is_turn_start`: an upkeep window where the active player has
/// priority and nobody has passed. (Unlike `model::is_turn_start`, this
/// excludes the window after the non-active player acts in an upkeep.)
pub fn is_turn_start(s: &State) -> bool {
    matches!(s.pend, Pending::Window(Step::Upkeep, p, false) if p == s.active)
}

/// `entry s v`: `s` with B on `v` life.
pub fn entry(s: &State, v: u32) -> State {
    let mut e = s.clone();
    e.side_b.life = v;
    e
}

// ---- packing (Packed.v) ----

fn put(off: u32, w: u32, x: u64) -> u64 {
    (x & ((1u64 << w) - 1)) << off
}

fn enc_walker(w: &Walker) -> u64 {
    put(0, 5, w.counters as u64) | put(5, 1, w.tapped as u64) | put(6, 1, w.sick as u64)
}

fn enc_side(sd: &Side) -> u64 {
    let wslot = |n: usize| sd.bf.get(n).map_or(0, enc_walker);
    let cslot = |n: usize| sd.library.get(n).map_or(0, |c| (*c == Card::Elixir) as u64);
    put(0, 5, sd.life as u64)
        | put(5, 1, sd.city as u64)
        | put(6, 3, sd.pool as u64)
        | put(9, 2, sd.hand_w as u64)
        | put(11, 1, sd.hand_e as u64)
        | put(12, 1, sd.elixir_bf as u64)
        | put(13, 5, sd.thop_u as u64)
        | put(18, 5, sd.thop_t as u64)
        | put(23, 2, sd.gy_w as u64)
        | put(25, 2, sd.bf.len() as u64)
        | put(27, 7, wslot(0))
        | put(34, 7, wslot(1))
        | put(41, 7, wslot(2))
        | put(48, 2, sd.library.len() as u64)
        | put(50, 1, cslot(0))
        | put(51, 1, cslot(1))
        | put(52, 1, cslot(2))
}

/// `enc s`: A's side with the active player (bit 53) and the first-turn
/// flag (bit 54), then B's side.
pub fn enc(s: &State) -> (u64, u64) {
    (
        enc_side(&s.side_a) | put(53, 1, (s.active == Player::B) as u64) | put(54, 1, s.first_turn as u64),
        enc_side(&s.side_b),
    )
}

fn field(i: u64, off: u32, k: u32) -> u32 {
    ((i >> off) & ((1u64 << k) - 1)) as u32
}
fn bit(i: u64, off: u32) -> bool {
    (i >> off) & 1 == 1
}

fn dec_walker(x: u64) -> Walker {
    Walker { counters: field(x, 0, 5), tapped: bit(x, 5), sick: bit(x, 6) }
}

/// `dec_side`. `None` for three Walkers or three library cards, which
/// `model.rs` can't represent (nor can a real game reach).
fn dec_side(x: u64) -> Option<Side> {
    let nw = field(x, 25, 2) as usize;
    let nl = field(x, 48, 2) as usize;
    if nw > 2 || nl > 2 {
        return None;
    }
    let ws = [dec_walker(x >> 27), dec_walker(x >> 34)];
    let cs = [bit(x, 50), bit(x, 51)].map(|b| if b { Card::Elixir } else { Card::Walker });
    Some(Side {
        life: field(x, 0, 5),
        city: bit(x, 5),
        pool: field(x, 6, 3),
        hand_w: field(x, 9, 2),
        hand_e: bit(x, 11),
        bf: SVec::from_slice(&ws[..nw]),
        elixir_bf: bit(x, 12),
        thop_u: field(x, 13, 5),
        thop_t: field(x, 18, 5),
        library: SVec::from_slice(&cs[..nl]),
        gy_w: field(x, 23, 2),
    })
}

/// `dec k1 k2`: a turn start (no combat, upkeep window of the active player).
pub fn dec(k1: u64, k2: u64) -> Option<State> {
    let p = if bit(k1, 53) { Player::B } else { Player::A };
    Some(State {
        active: p,
        first_turn: bit(k1, 54),
        side_a: dec_side(k1)?,
        side_b: dec_side(k2)?,
        cmb: Combat::default(),
        pend: Pending::Window(Step::Upkeep, p, false),
    })
}

// ---- the abstraction relation (Checker.R), for tests ----

/// `R s t`: the abstract state `s` stands for the real state `t`.
pub fn related(h: u32, s: &State, t: &State) -> bool {
    let walker_rel = |w: &Walker, x: &Walker| {
        w.tapped == x.tapped && w.sick == x.sick && (w.counters == x.counters || (h <= w.counters && h <= x.counters))
    };
    let (a, x) = (&s.side_a, &t.side_a);
    let side_a = a.life == x.life
        && a.city == x.city
        && a.pool == x.pool
        && a.hand_w == x.hand_w
        && !a.hand_e
        && !x.hand_e
        && !a.elixir_bf
        && !x.elixir_bf
        && a.library.iter().all(|c| *c == Card::Walker)
        && a.library == x.library
        && a.bf.len() == x.bf.len()
        && a.bf.iter().zip(x.bf.iter()).all(|(w, y)| walker_rel(w, y))
        && a.thop_u == x.thop_u
        && a.thop_t == x.thop_t;
    let strip = |b: &Side| {
        let mut b = *b;
        b.life = 0;
        b.thop_u = 0;
        b.thop_t = 0;
        b
    };
    let (b, y) = (&s.side_b, &t.side_b);
    let side_b = b.life <= y.life && b.thop_u <= y.thop_u && b.thop_t <= y.thop_t && strip(b) == strip(y);
    s.active == t.active
        && s.first_turn == t.first_turn
        && s.cmb == t.cmb
        && s.pend == t.pend
        && !matches!(s.pend, Pending::ChooseShuffle(_, Player::A, _))
        && side_a
        && side_b
}

// ---- playing B from the certificate ----

/// B's plan for the current turn: the record it plays from and the
/// abstract state it searches.
#[derive(Clone, Debug)]
pub struct Segment {
    pub rank: u32,
    pub val: u32,
    /// B's life in the abstract state at the turn start: B's actual life,
    /// or the record's value if the check failed with the actual life.
    pub life: u32,
    pub abs: State,
    pub fuel: u32,
    /// Moves since the turn start.
    pub depth: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Failure {
    /// The position is outside the certificate (not an error in itself).
    Uncovered(String),
    /// The certificate should cover this position but the search failed:
    /// a bug in this port or a mismatch with the Rocq model.
    Bug(String),
}

impl Failure {
    pub fn message(&self) -> &str {
        match self {
            Failure::Uncovered(m) | Failure::Bug(m) => m,
        }
    }
}

/// Statistics of certified play, for tests.
#[derive(Default, Debug, Clone)]
pub struct Stats {
    pub nodes: u64,
    pub segments: u64,
    /// Segments where the check failed on B's actual life and B fell back
    /// to the record's value.
    pub record_life: u64,
}

impl Table {
    /// The record B plays from at turn start `t`: among the records of
    /// `key t` that need at most B's life, the one with the lowest rank.
    pub fn pick_record(&self, t: &State) -> Option<(u32, u32)> {
        let k = self.key(t);
        let (k1, k2) = enc(&k);
        if dec(k1, k2).as_ref() != Some(&k) {
            return None;
        }
        let mut j = self.start(k1, k2);
        let mut best: Option<(u32, u32)> = None;
        while self.at_key(j, k1, k2) {
            let (r, v) = (self.rank_of(j as usize), self.val_of(j as usize));
            if v <= t.side_b.life && best.map_or(true, |(br, _)| r < br) {
                best = Some((r, v));
            }
            j += 1;
        }
        best
    }

    /// Start B's plan at the turn start `t`.
    pub fn begin(&self, t: &State, stats: &mut Stats) -> Result<Segment, Failure> {
        debug_assert!(is_turn_start(t));
        let (rank, val) = self
            .pick_record(t)
            .ok_or_else(|| Failure::Uncovered(format!("no record covers this turn start with B on {} life", t.side_b.life)))?;
        let k = self.key(t);
        stats.segments += 1;
        for (life, fallback) in [(t.side_b.life, false), (val, true)] {
            let abs = entry(&k, life);
            if !related(self.h, &abs, t) {
                return Err(Failure::Bug("the certificate's position does not stand for the real one".into()));
            }
            if self.check_win(rank, self.fuel, true, &abs, &mut stats.nodes) {
                if fallback {
                    stats.record_life += 1;
                }
                return Ok(Segment { rank, val, life, abs, fuel: self.fuel, depth: 0 });
            }
        }
        Err(Failure::Bug(format!("the record of rank {rank} for this turn start fails the check")))
    }

    /// Does the certificate still cover the current position of `seg`?
    pub fn covered(&self, seg: &Segment, stats: &mut Stats) -> bool {
        self.check_win(seg.rank, seg.fuel, seg.depth == 0, &seg.abs, &mut stats.nodes)
    }

    /// Follow move `m` (made in the real game) in the abstract state.
    pub fn follow(&self, seg: &mut Segment, m: &Move) -> Result<(), String> {
        if !moves(&seg.abs).contains(m) {
            return Err(format!("move {} is not a move of the certificate's position", crate::walk::mv(m)));
        }
        if seg.fuel == 0 {
            return Err("out of fuel".into());
        }
        seg.abs = step(&seg.abs, m);
        seg.fuel -= 1;
        seg.depth += 1;
        if self.too_many(&seg.abs) {
            return Err("A has more Thopters than the certificate allows".into());
        }
        Ok(())
    }

    /// B's move in the abstract state: the first after which the check
    /// still passes. `None` only if `seg` is not covered.
    pub fn choose(&self, seg: &Segment, stats: &mut Stats) -> Option<Move> {
        let s = &seg.abs;
        if winner(s).is_some() || to_move(s) != Player::B || self.huge_event(s) || seg.fuel == 0 {
            return None;
        }
        moves(s).into_iter().find(|m| {
            let s2 = step(s, m);
            !self.too_many(&s2) && self.check_win(seg.rank, seg.fuel - 1, false, &s2, &mut stats.nodes)
        })
    }

    /// The segment for the real state at the end of `states` (the states
    /// of a game, with `moves[i]` played from `states[i]`), replaying from
    /// the last turn start.
    pub fn segment_at(&self, states: &[State], mvs: &[Move], stats: &mut Stats) -> Result<(Segment, usize), Failure> {
        let n = states.len() - 1;
        let k = (0..=n).rev().find(|&i| is_turn_start(&states[i])).ok_or(Failure::Uncovered("no turn start".into()))?;
        let mut seg = self.begin(&states[k], stats)?;
        for m in &mvs[k..n] {
            self.follow(&mut seg, m).map_err(Failure::Uncovered)?;
        }
        Ok((seg, k))
    }

    /// Where coverage was lost, for a game whose current position is not
    /// covered: the index of the first move after which the position is
    /// not covered although the one before was. `None` if the game never
    /// was covered.
    pub fn diagnose(&self, states: &[State], mvs: &[Move]) -> Option<usize> {
        let mut stats = Stats::default();
        let mut prev = false;
        for i in 0..states.len() {
            let cov = matches!(self.segment_at(&states[..=i], mvs, &mut stats), Ok((seg, _)) if self.covered(&seg, &mut stats));
            if prev && !cov {
                return Some(i - 1);
            }
            prev = cov;
        }
        None
    }
}

/// The result of asking for B's certified moves.
#[derive(Debug, Clone)]
pub struct Plan {
    /// Move indices (into `model::moves` of each successive real state) for
    /// B's decisions until A is to move or the game is over.
    pub moves: Vec<usize>,
    pub rank: u32,
    pub val: u32,
    pub life: u32,
    pub stats: Stats,
}

/// Plan B's moves from the end of a game (`states`/`mvs` as in
/// `segment_at`). On `Uncovered`, `diagnose` says where coverage was lost.
pub fn plan(t: &Table, states: &[State], mvs: &[Move]) -> Result<Plan, Failure> {
    let mut stats = Stats::default();
    let (mut seg, _) = t.segment_at(states, mvs, &mut stats)?;
    if !t.covered(&seg, &mut stats) {
        return Err(Failure::Uncovered("the certificate does not cover this position".into()));
    }
    let mut cur = states[states.len() - 1].clone();
    let (rank, val, life) = (seg.rank, seg.val, seg.life);
    let mut out = vec![];
    while winner(&cur).is_none() && to_move(&cur) == Player::B {
        let m = t.choose(&seg, &mut stats).ok_or_else(|| Failure::Bug("no certified move at a covered position".into()))?;
        let legal = moves(&cur);
        let i = legal
            .iter()
            .position(|x| *x == m)
            .ok_or_else(|| Failure::Bug(format!("certified move {} is not legal in the real game", crate::walk::mv(&m))))?;
        out.push(i);
        cur = step(&cur, &m);
        t.follow(&mut seg, &m).map_err(Failure::Bug)?;
        if !related(t.h, &seg.abs, &cur) {
            return Err(Failure::Bug("abstract state no longer stands for the real one".into()));
        }
        if winner(&cur).is_none() && is_turn_start(&cur) {
            let old = seg.rank;
            seg = t.begin(&cur, &mut stats).map_err(|e| Failure::Bug(format!("at a new turn start: {}", e.message())))?;
            if seg.rank >= old {
                return Err(Failure::Bug(format!("rank did not fall ({old} to {})", seg.rank)));
            }
        }
    }
    Ok(Plan { moves: out, rank, val, life, stats })
}
