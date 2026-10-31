//! The play site's engine: the rsolver game model compiled to WASM, plus a
//! bounded search for the computer opponent.
//!
//! The rules are not re-implemented here. `model.rs`, `reduce.rs`, `fix.rs`
//! and `walk.rs` are the files in `rsolver/src/`, included by path and left
//! unchanged. This file only adds a small C-ABI surface for JavaScript:
//!
//! * `load(ptr, n)` rebuilds the current state from `[starter, lifeA, lifeB,
//!   m1, m2, ...]`, where each `m` is an index into `model::moves` of the
//!   state at that point. A game is therefore just its starting options and
//!   a list of move indices, which makes undo and the worker trivial.
//! * `play(i)` applies move `i` of the current state.
//! * `view()` writes the current state and its legal moves as JSON.
//! * `think(budget_ms, max_depth)` runs the search and writes its choice as JSON.
//! * `walk(seed_lo, seed_hi, steps, bias)` writes the differential-test walk,
//!   in exactly the format of `rsolver walk`; `walk_lines()` writes the block
//!   that walk prints for the current state, so a JavaScript driver can
//!   replay the walk through `load`/`play`/`view`.
//!
//! Results are written to an output buffer read through `out_ptr`/`out_len`.

#![allow(clippy::missing_safety_doc)]

#[allow(dead_code)]
#[path = "../../../rsolver/src/model.rs"]
pub mod model;
#[allow(dead_code)]
#[path = "../../../rsolver/src/reduce.rs"]
pub mod reduce;
#[allow(dead_code)]
#[path = "../../../rsolver/src/fix.rs"]
pub mod fix;
#[allow(dead_code)]
#[path = "../../../rsolver/src/walk.rs"]
pub mod walk;

pub mod search;

use model::*;
use std::cell::RefCell;
use std::fmt::Write;

// ---- time ----

#[cfg(target_arch = "wasm32")]
mod clock {
    #[link(wasm_import_module = "env")]
    extern "C" {
        fn now_ms() -> f64;
    }
    pub fn now() -> f64 {
        unsafe { now_ms() }
    }
}
#[cfg(not(target_arch = "wasm32"))]
mod clock {
    use std::sync::OnceLock;
    use std::time::Instant;
    static T0: OnceLock<Instant> = OnceLock::new();
    pub fn now() -> f64 {
        T0.get_or_init(Instant::now).elapsed().as_secs_f64() * 1000.0
    }
}
pub use clock::now;

// ---- starting position ----

/// `model::init`, with optional starting life totals (20 in the real game).
pub fn start(starter: Player, life_a: u32, life_b: u32) -> State {
    let mut s = init(starter);
    s.side_a.life = life_a;
    s.side_b.life = life_b;
    s
}

/// Replay a game record `[starter, lifeA, lifeB, m...]`. Returns the state
/// and how many moves applied cleanly (all of them unless an index is out
/// of range, in which case replay stops there).
pub fn replay(rec: &[u32]) -> (State, usize) {
    let starter = if rec.first().copied().unwrap_or(0) == 0 { Player::A } else { Player::B };
    let la = rec.get(1).copied().unwrap_or(20).max(1);
    let lb = rec.get(2).copied().unwrap_or(20).max(1);
    let mut s = start(starter, la, lb);
    let ms = if rec.len() > 3 { &rec[3..] } else { &[][..] };
    for (k, &i) in ms.iter().enumerate() {
        let legal = moves(&s);
        match legal.get(i as usize) {
            Some(m) => s = step(&s, m),
            None => return (s, k),
        }
    }
    (s, ms.len())
}

// ---- JSON ----

fn pl(p: Player) -> &'static str {
    match p {
        Player::A => "A",
        Player::B => "B",
    }
}

fn step_name(st: Step) -> &'static str {
    match st {
        Step::Upkeep => "Upkeep",
        Step::DrawStep => "DrawStep",
        Step::Main1 => "Main1",
        Step::BeginCombat => "BeginCombat",
        Step::DeclAtk => "DeclAtk",
        Step::DeclBlk => "DeclBlk",
        Step::DamageStep => "DamageStep",
        Step::EndCombat => "EndCombat",
        Step::Main2 => "Main2",
        Step::EndStep => "EndStep",
    }
}

fn card_json(c: &Card) -> &'static str {
    match c {
        Card::Walker => "\"W\"",
        Card::Elixir => "\"E\"",
    }
}

fn join<T>(l: &[T], f: impl Fn(&T) -> String) -> String {
    format!("[{}]", l.iter().map(f).collect::<Vec<_>>().join(","))
}

fn blocker_json(b: &Blocker) -> String {
    match b {
        Blocker::BT => "\"T\"".into(),
        Blocker::BW(i) => i.to_string(),
    }
}

fn side_json(sd: &Side) -> String {
    format!(
        "{{\"life\":{},\"city\":{},\"pool\":{},\"handW\":{},\"handE\":{},\"bf\":{},\"elixir\":{},\"thopU\":{},\"thopT\":{},\"library\":{},\"gyW\":{}}}",
        sd.life,
        sd.city,
        sd.pool,
        sd.hand_w,
        sd.hand_e,
        join(&sd.bf, |w| format!("{{\"c\":{},\"tapped\":{},\"sick\":{}}}", w.counters, w.tapped, w.sick)),
        sd.elixir_bf,
        sd.thop_u,
        sd.thop_t,
        join(&sd.library, |c| card_json(c).to_string()),
        sd.gy_w
    )
}

fn pend_json(p: &Pending) -> String {
    match p {
        Pending::Window(st, p, passed) => format!(
            "{{\"kind\":\"window\",\"step\":\"{}\",\"prio\":\"{}\",\"passed\":{}}}",
            step_name(*st),
            pl(*p),
            passed
        ),
        Pending::ChooseAttack => "{\"kind\":\"attack\",\"step\":\"DeclAtk\"}".into(),
        Pending::ChooseBlock => "{\"kind\":\"block\",\"step\":\"DeclBlk\"}".into(),
        Pending::ChooseOrder => "{\"kind\":\"order\",\"step\":\"DeclBlk\"}".into(),
        Pending::ChooseDamage => "{\"kind\":\"damage\",\"step\":\"DamageStep\"}".into(),
        Pending::ChooseShuffle(st, p, cs) => format!(
            "{{\"kind\":\"shuffle\",\"step\":\"{}\",\"prio\":\"{}\",\"cards\":{}}}",
            step_name(*st),
            pl(*p),
            join(cs, |c| card_json(c).to_string())
        ),
        Pending::Over(w) => format!("{{\"kind\":\"over\",\"winner\":\"{}\"}}", pl(*w)),
    }
}

pub fn move_json(m: &Move) -> String {
    match m {
        Move::Pass => "{\"k\":\"pass\"}".into(),
        Move::Pump(i) => format!("{{\"k\":\"pump\",\"w\":{i}}}"),
        Move::ActElixir => "{\"k\":\"elixir\"}".into(),
        Move::CastWalker(x) => format!("{{\"k\":\"cast\",\"x\":{x}}}"),
        Move::CastElixir => "{\"k\":\"castElixir\"}".into(),
        Move::Attack(ws, k) => format!("{{\"k\":\"attack\",\"ws\":{},\"t\":{k}}}", join(ws, |i| i.to_string())),
        Move::Block(wb, tb, tr) => format!(
            "{{\"k\":\"block\",\"wb\":{},\"tb\":{},\"tr\":{tr}}}",
            join(wb, |o| match o {
                None => "null".into(),
                Some(i) => i.to_string(),
            }),
            join(tb, |i| i.to_string())
        ),
        Move::Order(os) => format!("{{\"k\":\"order\",\"os\":{}}}", join(os, |bs| join(bs, blocker_json))),
        Move::Assign(js) => format!("{{\"k\":\"assign\",\"js\":{}}}", join(js, |i| i.to_string())),
        Move::Arrange(l) => format!("{{\"k\":\"arrange\",\"lib\":{}}}", join(l, |c| card_json(c).to_string())),
    }
}

pub fn view_json(s: &State) -> String {
    let ms = moves(s);
    let kept = reduce::filtered(s);
    let filtered: Vec<usize> = ms.iter().enumerate().filter(|(_, m)| kept.contains(m)).map(|(i, _)| i).collect();
    let mut o = String::with_capacity(1024);
    write!(
        o,
        "{{\"fmt\":\"{}\",\"active\":\"{}\",\"firstTurn\":{},\"toMove\":\"{}\",\"winner\":{},\"turnStart\":{},\"pend\":{},\"A\":{},\"B\":{},",
        walk::state(s),
        pl(s.active),
        s.first_turn,
        pl(to_move(s)),
        match winner(s) {
            Some(p) => format!("\"{}\"", pl(p)),
            None => "null".into(),
        },
        is_turn_start(s),
        pend_json(&s.pend),
        side_json(&s.side_a),
        side_json(&s.side_b),
    )
    .unwrap();
    write!(
        o,
        "\"cmb\":{{\"atk\":{},\"atkThop\":{},\"blk\":{},\"trades\":{}}},",
        join(&s.cmb.atk, |i| i.to_string()),
        s.cmb.atk_thop,
        join(&s.cmb.blk, |bs| join(bs, blocker_json)),
        s.cmb.trades
    )
    .unwrap();
    write!(
        o,
        "\"moves\":{},\"filtered\":{},\"key\":\"{}\"}}",
        join(&ms, |m| move_json(m)),
        join(&filtered, |i| i.to_string()),
        position_key(s)
    )
    .unwrap();
    o
}

/// A compact identifier of a turn-start position, for repetition checks.
pub fn position_key(s: &State) -> String {
    let mut k = s.clone();
    canon(&mut k);
    walk::state(&k)
}

// ---- the walk (rsolver/src/walk.rs, written to a string) ----

/// The block `walk::run` prints for one state (without moving).
pub fn walk_lines(s: &State) -> String {
    let ar = reduce::Rules::new(reduce::A_DEFAULT.iter().map(|r| r.to_string()).collect());
    let br = reduce::Rules::new(reduce::B_DEFAULT.iter().map(|r| r.to_string()).collect());
    let mut line = String::new();
    writeln!(line, "{}", walk::state(s)).unwrap();
    let ms = moves(s);
    for (tag, l) in [
        ("M", ms.clone()),
        ("F", reduce::filtered(s)),
        ("AM", reduce::a_macro(&ar, s)),
        ("BM", reduce::b_macro(&br, s)),
    ] {
        writeln!(line, "{} {}", tag, l.iter().map(walk::mv).collect::<Vec<_>>().join(" ")).unwrap();
    }
    if is_turn_start(s) {
        let k = fix::key_gen(false, s);
        let hex: String = k.iter().map(|c| format!("{c:02x}")).collect();
        writeln!(line, "K {} {}", hex, fix::digest_key(&k)).unwrap();
    }
    line
}

/// The same walk as `rsolver walk SEED STEPS [bias]` (walk::run), into a string.
pub fn walk_text(seed: u64, steps: usize, bias: bool) -> String {
    let mut x = seed;
    let start = || init(if seed & 1 == 0 { Player::A } else { Player::B });
    let mut s = start();
    let mut out = String::new();
    for _ in 0..steps {
        out.push_str(&walk_lines(&s));
        let ms = moves(&s);
        let big = |sd: &Side| sd.bf.iter().any(|w| w.counters > 40);
        if winner(&s).is_some() || ms.is_empty() || big(&s.side_a) || big(&s.side_b) {
            s = start();
        } else {
            let next = |x: u64| x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let pick = |x: u64, n: usize| ((x >> 33) % n as u64) as usize;
            x = next(x);
            let others: Vec<Move> = ms.iter().filter(|m| !matches!(m, Move::Pass | Move::Pump(_))).cloned().collect();
            let ms = if bias && !others.is_empty() && pick(x, 3) != 0 {
                x = next(x);
                others
            } else {
                ms
            };
            s = step(&s, &ms[pick(x, ms.len())]);
        }
    }
    out
}

// ---- C ABI ----

thread_local! {
    static CUR: RefCell<State> = RefCell::new(init(Player::A));
    static OUT: RefCell<String> = RefCell::new(String::new());
    static SEARCH: RefCell<search::Search> = RefCell::new(search::Search::new());
}

fn set_out(s: String) {
    OUT.with(|o| *o.borrow_mut() = s);
}

/// Space for `n` u32 words (a game record for `load`).
#[no_mangle]
pub extern "C" fn alloc_words(n: usize) -> *mut u32 {
    let mut v: Vec<u32> = Vec::with_capacity(n.max(1));
    let p = v.as_mut_ptr();
    std::mem::forget(v);
    p
}

#[no_mangle]
pub unsafe extern "C" fn free_words(p: *mut u32, n: usize) {
    drop(Vec::from_raw_parts(p, 0, n.max(1)));
}

#[no_mangle]
pub extern "C" fn out_ptr() -> *const u8 {
    OUT.with(|o| o.borrow().as_ptr())
}

#[no_mangle]
pub extern "C" fn out_len() -> usize {
    OUT.with(|o| o.borrow().len())
}

/// Load a game record of `n` u32 words at `p`. Returns the number of moves
/// applied; fewer than `n - 3` means an index was illegal.
#[no_mangle]
pub unsafe extern "C" fn load(p: *const u32, n: usize) -> i32 {
    let rec = if n == 0 { &[][..] } else { std::slice::from_raw_parts(p, n) };
    let (s, k) = replay(rec);
    CUR.with(|c| *c.borrow_mut() = s);
    k as i32
}

/// Apply move `i` of the current state. Returns 1, or 0 if `i` is illegal.
#[no_mangle]
pub extern "C" fn play(i: u32) -> i32 {
    CUR.with(|c| {
        let s = c.borrow().clone();
        match moves(&s).get(i as usize) {
            Some(m) => {
                *c.borrow_mut() = step(&s, m);
                1
            }
            None => 0,
        }
    })
}

#[no_mangle]
pub extern "C" fn view() {
    let j = CUR.with(|c| view_json(&c.borrow()));
    set_out(j);
}

#[no_mangle]
pub extern "C" fn walk_block() {
    let j = CUR.with(|c| walk_lines(&c.borrow()));
    set_out(j);
}

#[no_mangle]
pub extern "C" fn walk(seed_lo: u32, seed_hi: u32, steps: u32, bias: u32) {
    let seed = (seed_hi as u64) << 32 | seed_lo as u64;
    set_out(walk_text(seed, steps as usize, bias != 0));
}

/// Search the current position for the side to move.
#[no_mangle]
pub extern "C" fn think(budget_ms: f64, max_depth: u32) {
    let s = CUR.with(|c| c.borrow().clone());
    let r = SEARCH.with(|sr| sr.borrow_mut().think(&s, budget_ms, max_depth.min(60) as u8));
    set_out(r.to_json());
}

/// Drop the search's transposition table.
#[no_mangle]
pub extern "C" fn reset_search() {
    SEARCH.with(|sr| *sr.borrow_mut() = search::Search::new());
}
