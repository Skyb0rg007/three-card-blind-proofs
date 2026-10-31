//! The computer opponent: an iterative-deepening minimax over whole turns.
//!
//! This is a strong bounded search, not optimal play. Optimal play is not
//! known for this matchup (see REDUCTION.md), and the solver's tables are
//! far too large to ship.
//!
//! * **Depth is counted in turns.** A search of depth d plays out the rest
//!   of the current turn and then d further turns move by move, and scores
//!   the turn-start position it reaches with a static evaluation. Inside a
//!   turn every decision (each priority pass, attack, block, ...) is
//!   searched exactly, with a transposition table keyed on (position,
//!   depth left), so the many orders of passing that reach the same
//!   position are only searched once.
//! * **Move sets.** At the root the engine considers every move in the
//!   exploration filter (`reduce::filtered`), which drops moves that are
//!   dominated by the same move at a later window (REDUCTION.md R6). Inside
//!   the tree both players use the macro move sets (`reduce::a_macro`,
//!   `reduce::b_macro`), which keep the extreme attacks, blocks and damage
//!   assignments; this keeps the branching factor manageable when there
//!   are many Thopters.
//! * **Iterative deepening** with a time budget: depth 0, 1, 2, ... until
//!   the budget is spent or a forced result is found. An unfinished
//!   iteration is thrown away.
//!
//! Scores are from A's point of view (A maximises, B minimises).

use crate::model::*;
use crate::now;
use crate::reduce::{self, Rules};
use rustc_hash::FxHashMap as HashMap;
use std::hash::{DefaultHasher, Hash, Hasher};

/// A won game. Faster wins score higher (see `terminal`).
pub const WIN: i32 = 1_000_000;
/// The bonus for a position where the player about to attack threatens
/// lethal damage that the defender cannot obviously stop.
const LETHAL: i32 = 400;
/// Transposition table entries before it is cleared (about 70 MB).
const TT_MAX: usize = 2_000_000;

pub struct Search {
    /// Keyed by a 128-bit hash of (canonical position, depth left), to keep
    /// entries small enough for a browser.
    tt: HashMap<u128, i32>,
    arules: Rules,
    brules: Rules,
    pub nodes: u64,
    deadline: f64,
    aborted: bool,
}

pub struct Choice {
    /// Index into `model::moves` of the position searched.
    pub index: usize,
    pub value: i32,
    /// Deepest completed iteration (turns beyond the current one).
    pub depth: u32,
    pub nodes: u64,
    pub ms: f64,
    /// Number of candidate moves considered.
    pub candidates: usize,
    /// (index, value) of each candidate at the deepest completed depth.
    pub scores: Vec<(usize, i32)>,
}

impl Choice {
    pub fn to_json(&self) -> String {
        format!(
            "{{\"move\":{},\"value\":{},\"depth\":{},\"nodes\":{},\"ms\":{:.0},\"candidates\":{},\"win\":{},\"scores\":[{}]}}",
            self.index,
            self.value,
            self.depth,
            self.nodes,
            self.ms,
            self.candidates,
            WIN,
            self.scores.iter().map(|(i, v)| format!("[{i},{v}]")).collect::<Vec<_>>().join(",")
        )
    }
}

fn terminal(w: Player, d: u8) -> i32 {
    // More depth left means the game ended sooner.
    let v = WIN + 1000 * d as i32;
    if w == Player::A { v } else { -v }
}

/// Static value of one side's assets, in rough "life point" units.
fn assets(sd: &Side, is_b: bool) -> i32 {
    let counters: u32 = sd.bf.iter().map(|w| w.counters).sum();
    let mut v = 3 * counters as i32           // each counter is a point of power, and a Thopter later
        + 6 * sd.bf.len() as i32              // a body on the battlefield can be pumped every round
        + 5 * sd.hand_w as i32                // a Walker in hand costs the whole City to cast
        + 3 * (sd.thop_u + sd.thop_t) as i32  // evasive power; only Thopters can block them
        + if sd.city { 2 } else { 0 }; // mana still to spend this round
    if is_b {
        // Elixir: 5 life every couple of rounds while it cycles.
        let elixir_somewhere = sd.elixir_bf || sd.hand_e || sd.library.contains(&Card::Elixir);
        v += if sd.elixir_bf { 7 } else { 0 } + if sd.hand_e { 5 } else { 0 };
        for (pos, c) in sd.library.iter().enumerate() {
            v += match c {
                Card::Elixir => 4 - pos as i32,
                Card::Walker => 3,
            };
        }
        if elixir_somewhere {
            v += sd.gy_w as i32; // Walkers in the graveyard come back with the next shuffle
        }
    }
    v
}

/// Rough damage the active player `p` can push through at the start of
/// their turn, against the defender's untapped blockers.
fn threat(s: &State, p: Player) -> u32 {
    let a = s.side(p);
    let d = s.side(p.opp());
    let flyers = a.thop_u;
    let evasive = flyers.saturating_sub(d.thop_u);
    let spare = d.thop_u.saturating_sub(flyers);
    let mut powers: Vec<u32> = a.bf.iter().filter(|w| !w.tapped && !w.sick).map(|w| w.counters).collect();
    powers.sort_unstable_by(|x, y| y.cmp(x));
    let blockers = d.bf.iter().filter(|w| !w.tapped).count() as u32 + spare;
    let ground: u32 = powers.iter().skip(blockers as usize).sum();
    evasive + ground
}

/// Static evaluation of a turn-start position, from A's point of view.
pub fn evaluate(s: &State) -> i32 {
    let a = &s.side_a;
    let b = &s.side_b;
    let mut v = a.life as i32 - b.life as i32 + assets(a, false) - assets(b, true);
    let p = s.active;
    let q = p.opp();
    let dq = s.side(q);
    let mut life_q = dq.life;
    if q == Player::B && dq.elixir_bf && (dq.pool >= 2 || dq.city) {
        life_q += 5;
    }
    if threat(s, p) >= life_q {
        v += if p == Player::A { LETHAL } else { -LETHAL };
    }
    v
}

/// Two independent SipHash digests of the canonical position and depth.
fn tt_key(s: &State, d: u8) -> u128 {
    let mut k = s.clone();
    canon(&mut k);
    let mut h1 = DefaultHasher::new();
    k.hash(&mut h1);
    d.hash(&mut h1);
    let mut h2 = DefaultHasher::new();
    0x9e37_79b9_7f4a_7c15u64.hash(&mut h2);
    k.hash(&mut h2);
    d.hash(&mut h2);
    (h1.finish() as u128) << 64 | h2.finish() as u128
}

impl Default for Search {
    fn default() -> Self {
        Self::new()
    }
}

impl Search {
    pub fn new() -> Search {
        Search {
            tt: HashMap::default(),
            arules: Rules::new(reduce::A_DEFAULT.iter().map(|r| r.to_string()).collect()),
            brules: Rules::new(reduce::B_DEFAULT.iter().map(|r| r.to_string()).collect()),
            nodes: 0,
            deadline: f64::INFINITY,
            aborted: false,
        }
    }

    /// The moves searched inside the tree.
    fn tree_moves(&self, s: &State) -> Vec<Move> {
        match to_move(s) {
            Player::A => reduce::a_macro(&self.arules, s),
            Player::B => reduce::b_macro(&self.brules, s),
        }
    }

    fn child(&mut self, c: &State, d: u8) -> i32 {
        if let Some(w) = winner(c) {
            return terminal(w, d);
        }
        if is_turn_start(c) {
            if d == 0 {
                return evaluate(c);
            }
            return self.node(c, d - 1);
        }
        self.node(c, d)
    }

    fn node(&mut self, s: &State, d: u8) -> i32 {
        if self.aborted {
            return 0;
        }
        let key = tt_key(s, d);
        if let Some(&v) = self.tt.get(&key) {
            return v;
        }
        self.nodes += 1;
        if self.nodes & 255 == 0 && now() > self.deadline {
            self.aborted = true;
            return 0;
        }
        let maxi = to_move(s) == Player::A;
        let mut best = if maxi { i32::MIN } else { i32::MAX };
        for m in self.tree_moves(s) {
            let v = self.child(&step(s, &m), d);
            if self.aborted {
                return 0;
            }
            best = if maxi { best.max(v) } else { best.min(v) };
        }
        if self.tt.len() >= TT_MAX {
            self.tt.clear();
        }
        self.tt.insert(key, best);
        best
    }

    /// Choose a move for the side to move in `s`.
    pub fn think(&mut self, s: &State, budget_ms: f64, max_depth: u8) -> Choice {
        let t0 = now();
        self.nodes = 0;
        self.aborted = false;
        let all = moves(s);
        let kept = reduce::filtered(s);
        let mut cands: Vec<usize> = all.iter().enumerate().filter(|(_, m)| kept.contains(m)).map(|(i, _)| i).collect();
        if cands.is_empty() {
            cands = (0..all.len()).collect();
        }
        let mut choice = Choice {
            index: cands.first().copied().unwrap_or(0),
            value: 0,
            depth: 0,
            nodes: 0,
            ms: 0.0,
            candidates: cands.len(),
            scores: vec![],
        };
        if cands.len() <= 1 {
            choice.ms = now() - t0;
            return choice;
        }
        let maxi = to_move(s) == Player::A;
        let children: Vec<State> = cands.iter().map(|&i| step(s, &all[i])).collect();
        // Depth 0 always completes, whatever the budget.
        self.deadline = f64::INFINITY;
        for d in 0..=max_depth {
            let it0 = now();
            let mut scores = Vec::with_capacity(cands.len());
            for (&i, c) in cands.iter().zip(&children) {
                let v = self.child(c, d);
                if self.aborted {
                    break;
                }
                scores.push((i, v));
            }
            if self.aborted {
                break;
            }
            // First best in move order (Pass first), so ties are stable.
            let mut best = scores[0];
            for &(i, v) in &scores[1..] {
                if (maxi && v > best.1) || (!maxi && v < best.1) {
                    best = (i, v);
                }
            }
            choice.index = best.0;
            choice.value = best.1;
            choice.depth = d as u32;
            choice.scores = scores;
            let spent = now() - t0;
            let last = now() - it0;
            // Stop at a forced result, or when the next iteration (several
            // times longer) would not fit in the budget.
            if best.1.abs() >= WIN || spent + 3.0 * last > budget_ms {
                break;
            }
            self.deadline = t0 + budget_ms;
        }
        choice.nodes = self.nodes;
        choice.ms = now() - t0;
        choice
    }
}
