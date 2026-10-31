//! The exploration filter and the macro move sets (solver/reduce.ml).

use crate::model::*;

pub fn blocking_walkers(s: &State) -> Vec<u32> {
    s.cmb.blk.iter().flatten().filter_map(|b| if let Blocker::BW(i) = b { Some(*i) } else { None }).collect()
}

fn keep(s: &State, m: &Move) -> bool {
    match &s.pend {
        Pending::Window(st, p, _) => {
            let st = *st;
            let ap = *p == s.active;
            let pool = s.side(*p).pool;
            match m {
                Move::Pass => true,
                Move::CastWalker(x) => *x == 1 && st == Step::Main2,
                Move::CastElixir => st == Step::Main2,
                Move::Pump(i) => {
                    if ap {
                        st == Step::Main2 && pool > 0
                    } else {
                        st == Step::EndStep || (st == Step::DeclBlk && (blocking_walkers(s).contains(i) || pool > 0))
                    }
                }
                Move::ActElixir => {
                    if ap {
                        st == Step::Upkeep
                    } else {
                        st == Step::EndStep || st == Step::DeclBlk
                    }
                }
                _ => true,
            }
        }
        _ => true,
    }
}

/// The filter (Reduce.moves).
pub fn filtered(s: &State) -> Vec<Move> {
    moves(s).into_iter().filter(|m| keep(s, m)).collect()
}

/// The most Thopters a player may hold back from an attack under rule r:
/// "atk" holds none back, "atkN" at most N.
pub fn held_of(r: &str) -> Option<u32> {
    if r == "atk" {
        Some(0)
    } else if r.len() > 3 && r.starts_with("atk") {
        r[3..].parse().ok()
    } else {
        None
    }
}

#[derive(Clone, Debug)]
pub struct Rules {
    pub list: Vec<String>,
    pub held_back: Option<u32>,
}

impl Rules {
    pub fn new(list: Vec<String>) -> Rules {
        let held_back = list.iter().find_map(|r| held_of(r));
        Rules { list, held_back }
    }
    pub fn from_env(var: &str, default: &[&str]) -> Rules {
        let list = match std::env::var(var) {
            Ok(l) => l.split(',').filter(|r| !r.is_empty()).map(String::from).collect(),
            Err(_) => default.iter().map(|r| r.to_string()).collect(),
        };
        Rules::new(list)
    }
    pub fn on(&self, r: &str) -> bool {
        self.list.iter().any(|x| x == r)
    }
}

pub const A_DEFAULT: &[&str] = &["atk", "pump", "order", "dmg"];
pub const B_DEFAULT: &[&str] = &["blk", "tr", "atk", "dmg"];

fn two_extremes(ms: Vec<Move>) -> Vec<Move> {
    if ms.len() <= 1 {
        return ms;
    }
    let mut v = vec![ms[0].clone(), ms[ms.len() - 1].clone()];
    v.sort();
    v.dedup();
    v
}

/// A's macro move set (Reduce.a_macro).
pub fn a_macro(rules: &Rules, s: &State) -> Vec<Move> {
    let ms = filtered(s);
    if to_move(s) != Player::A {
        return ms;
    }
    let a = s.side(Player::A);
    let size = |i: u32| a.bf[i as usize].counters;
    let ready: Vec<u32> = a.bf.iter().enumerate().filter(|(_, w)| !w.tapped && !w.sick).map(|(i, _)| i as u32).collect();
    // stable sort by size, as List.sort
    let by_size = |l: &[u32]| {
        let mut l = l.to_vec();
        l.sort_by_key(|&i| size(i));
        l
    };
    match &s.pend {
        Pending::ChooseAttack => {
            let sorted = by_size(&ready);
            let mut sets: Vec<Vec<u32>> = vec![vec![], ready.clone()];
            if sorted.len() >= 2 {
                sets.push(vec![sorted[0]]);
                sets.push(vec![sorted[sorted.len() - 1]]);
            }
            let mut sets: Vec<Vec<u32>> = sets
                .into_iter()
                .map(|mut v| {
                    v.sort();
                    v
                })
                .collect();
            sets.sort();
            sets.dedup();
            let ks: Vec<u32> = match rules.held_back {
                Some(n) => {
                    let mut ks: Vec<u32> = vec![0];
                    ks.extend((0..=n).map(|j| a.thop_u.saturating_sub(j)));
                    ks.sort();
                    ks.dedup();
                    ks
                }
                None => (0..=a.thop_u).collect(),
            };
            let mut out = vec![];
            for ws in &sets {
                for &k in &ks {
                    let m = Move::Attack(ws.clone(), k);
                    if ms.contains(&m) {
                        out.push(m);
                    }
                }
            }
            out
        }
        Pending::Window(Step::EndStep, Player::A, _) if s.active == Player::B && rules.on("pump") => {
            let pumps: Vec<u32> = ms.iter().filter_map(|m| if let Move::Pump(i) = m { Some(*i) } else { None }).collect();
            let sorted = by_size(&pumps);
            match sorted.last() {
                Some(&i) => vec![Move::Pump(i), Move::Pass],
                None => vec![Move::Pass],
            }
        }
        Pending::ChooseOrder if rules.on("order") => {
            let front_t = Move::Order(
                s.cmb
                    .blk
                    .iter()
                    .map(|bs| {
                        let mut v: Vec<Blocker> = bs.iter().copied().filter(|b| *b == Blocker::BT).collect();
                        v.extend(bs.iter().copied().filter(|b| *b != Blocker::BT));
                        v
                    })
                    .collect(),
            );
            let front_w = Move::Order(
                s.cmb
                    .blk
                    .iter()
                    .map(|bs| {
                        let mut v: Vec<Blocker> = bs.iter().copied().filter(|b| *b != Blocker::BT).collect();
                        v.extend(bs.iter().copied().filter(|b| *b == Blocker::BT));
                        v
                    })
                    .collect(),
            );
            let mut v = vec![front_t, front_w];
            v.sort();
            v.dedup();
            v
        }
        Pending::ChooseDamage if rules.on("dmg") => two_extremes(ms),
        _ => ms,
    }
}

/// B's macro move set (Reduce.b_macro).
pub fn b_macro(rules: &Rules, s: &State) -> Vec<Move> {
    let ms = filtered(s);
    if to_move(s) != Player::B {
        return ms;
    }
    match &s.pend {
        Pending::ChooseBlock if rules.on("blk") || rules.on("tr") => {
            let a = s.side(Player::A);
            let b = s.side(Player::B);
            let c = &s.cmb;
            let sizes: Vec<u32> = c.atk.iter().map(|&i| a.bf[i as usize].counters).collect();
            ms.into_iter()
                .filter(|m| match m {
                    Move::Block(wb, tb, tr) => {
                        let n_t: u32 = tb.iter().sum();
                        let max_tr = c.atk_thop.min(b.thop_u.saturating_sub(n_t));
                        (!rules.on("blk")
                            || (sizes.iter().zip(tb.iter()).all(|(&sz, &k)| k == 0 || k == 1 || k == sz)
                                && wb.iter().filter(|o| o.is_some()).count() <= 1))
                            && (!rules.on("tr") || *tr == 0 || *tr == max_tr)
                    }
                    _ => true,
                })
                .collect()
        }
        Pending::ChooseAttack if rules.held_back.is_some() => {
            let b = s.side(Player::B);
            let n = rules.held_back.unwrap();
            ms.into_iter()
                .filter(|m| match m {
                    Move::Attack(_, k) => *k == 0 || *k >= b.thop_u.saturating_sub(n),
                    _ => true,
                })
                .collect()
        }
        Pending::ChooseDamage if rules.on("dmg") => two_extremes(ms),
        _ => ms,
    }
}
