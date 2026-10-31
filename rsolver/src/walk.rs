//! Differential testing: the same seeded random walk and text format as
//! solver/walk.ml.

use crate::fix;
use crate::model::*;
use crate::reduce::{self, Rules};
use std::fmt::Write;
use std::io::Write as _;

fn b(x: bool) -> &'static str {
    if x { "1" } else { "0" }
}
fn pl(p: Player) -> &'static str {
    match p {
        Player::A => "A",
        Player::B => "B",
    }
}
fn list<T>(l: &[T], f: impl Fn(&T) -> String) -> String {
    format!("[{}]", l.iter().map(f).collect::<Vec<_>>().join(";"))
}
fn card(c: &Card) -> String {
    match c {
        Card::Walker => "W".into(),
        Card::Elixir => "E".into(),
    }
}
fn blocker(x: &Blocker) -> String {
    match x {
        Blocker::BT => "T".into(),
        Blocker::BW(i) => format!("W{i}"),
    }
}

fn side(sd: &Side) -> String {
    format!(
        "{},{},{},{},{},{},{},{},{},{},{}",
        sd.life,
        b(sd.city),
        sd.pool,
        sd.hand_w,
        b(sd.hand_e),
        list(&sd.bf, |w| format!("{}:{}:{}", w.counters, b(w.tapped), b(w.sick))),
        b(sd.elixir_bf),
        sd.thop_u,
        sd.thop_t,
        list(&sd.library, card),
        sd.gy_w
    )
}

fn pend(p: &Pending) -> String {
    match p {
        Pending::Window(st, p, x) => format!("W{},{},{}", *st as u32, pl(*p), b(*x)),
        Pending::ChooseAttack => "CA".into(),
        Pending::ChooseBlock => "CB".into(),
        Pending::ChooseOrder => "CO".into(),
        Pending::ChooseDamage => "CD".into(),
        Pending::ChooseShuffle(st, p, cs) => format!("CS{},{},{}", *st as u32, pl(*p), list(cs, card)),
        Pending::Over(p) => format!("O{}", pl(*p)),
    }
}

pub fn state(s: &State) -> String {
    format!(
        "S act={} ft={} pend={} cmb={}/{}/{}/{} A={} B={}",
        pl(s.active),
        b(s.first_turn),
        pend(&s.pend),
        list(&s.cmb.atk, |i| i.to_string()),
        s.cmb.atk_thop,
        list(&s.cmb.blk, |bs| list(bs, blocker)),
        s.cmb.trades,
        side(&s.side_a),
        side(&s.side_b)
    )
}

pub fn mv(m: &Move) -> String {
    match m {
        Move::Pass => "P".into(),
        Move::Pump(i) => format!("U{i}"),
        Move::ActElixir => "X".into(),
        Move::CastWalker(x) => format!("C{x}"),
        Move::CastElixir => "E".into(),
        Move::Attack(ws, k) => format!("A{}{}", list(ws, |i| i.to_string()), k),
        Move::Block(wb, tb, tr) => format!(
            "B{}{}{}",
            list(wb, |o| match o {
                None => "-".into(),
                Some(i) => i.to_string(),
            }),
            list(tb, |i| i.to_string()),
            tr
        ),
        Move::Order(os) => format!("O{}", list(os, |bs| list(bs, blocker))),
        Move::Assign(js) => format!("S{}", list(js, |i| i.to_string())),
        Move::Arrange(l) => format!("R{}", list(l, card)),
    }
}

fn hex(k: &[u8]) -> String {
    k.iter().map(|c| format!("{c:02x}")).collect()
}

/// With `bias`, two draws in three avoid Pass and pumps when there is
/// another move. A walk restarts when a Walker passes 40 counters.
pub fn run(seed: u64, steps: usize, bias: bool) {
    let ar = Rules::new(reduce::A_DEFAULT.iter().map(|r| r.to_string()).collect());
    let br = Rules::new(reduce::B_DEFAULT.iter().map(|r| r.to_string()).collect());
    let mut x = seed;
    let start = || init(if seed & 1 == 0 { Player::A } else { Player::B });
    let mut s = start();
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());
    let mut line = String::new();
    for _ in 0..steps {
        line.clear();
        writeln!(line, "{}", state(&s)).unwrap();
        let ms = moves(&s);
        for (tag, l) in [
            ("M", ms.clone()),
            ("F", reduce::filtered(&s)),
            ("AM", reduce::a_macro(&ar, &s)),
            ("BM", reduce::b_macro(&br, &s)),
        ] {
            writeln!(line, "{} {}", tag, l.iter().map(mv).collect::<Vec<_>>().join(" ")).unwrap();
        }
        if is_turn_start(&s) {
            let k = fix::key_gen(false, &s);
            writeln!(line, "K {} {}", hex(&k), fix::digest_key(&k)).unwrap();
        }
        out.write_all(line.as_bytes()).unwrap();
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
}
