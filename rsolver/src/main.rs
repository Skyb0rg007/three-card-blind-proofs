//! rsolver: a Rust port of the OCaml fixed-point solver (solver/), for
//! speed. It reads and writes the same tables. Commands:
//!   walk SEED STEPS [bias]            the differential-test walk (as `main walk`)
//!   fix safe|win A|B T TT LMAX STARTER as `main fix`, with the same TCB_*
//!                                     variables (no ranks, lines or warm starts yet)
mod fix;
mod model;
mod progstat;
mod reduce;
mod solver;
mod walk;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use fix::{Cfg, MoveSet, INF, NINF};
use model::Player;
use reduce::Rules;
use std::time::Instant;

fn env_flag(v: &str) -> bool {
    std::env::var(v).ok().as_deref() == Some("1")
}
fn env_int(v: &str, d: u32) -> u32 {
    std::env::var(v).ok().and_then(|x| x.parse().ok()).unwrap_or(d)
}
fn pl(s: &str) -> Player {
    match s {
        "A" => Player::A,
        "B" => Player::B,
        _ => panic!("player must be A or B"),
    }
}

fn show(c: &Cfg, v: i64) -> String {
    if c.up() {
        if v >= INF { "never".into() } else { format!("B life >= {v}") }
    } else if v <= NINF {
        "never".into()
    } else if v >= INF {
        "any B life".into()
    } else {
        format!("B life <= {v}")
    }
}

fn cfg_from_env(prot: Player, t: u32, tt: u32, lmax: i64) -> Cfg {
    let (ot, ott) = (env_int("TCB_OT", t), env_int("TCB_OTT", tt));
    let (fulla, macro_, fullopp) = (env_flag("TCB_FULLA"), env_flag("TCB_MACRO"), env_flag("TCB_FULLOPP"));
    let arules = Rules::from_env("TCB_AMACRO", reduce::A_DEFAULT);
    let brules = Rules::from_env("TCB_BMACRO", reduce::B_DEFAULT);
    Cfg {
        prot,
        t,
        ot,
        tt,
        ott,
        lmax,
        full_a: prot == Player::B && fulla,
        mine: if env_flag("TCB_FULLMINE") {
            MoveSet::Full
        } else if !macro_ {
            MoveSet::Filter
        } else if prot == Player::B {
            MoveSet::BMacro
        } else {
            MoveSet::AMacro
        },
        theirs: if fullopp { MoveSet::Full } else { MoveSet::Filter },
        arules: arules.clone(),
        brules: brules.clone(),
        lax: std::env::var("TCB_LAX").map(|l| l.split(',').map(String::from).collect()).unwrap_or_default(),
    }
}

fn fix_cmd(mode: &str, who: &str, t: &str, tt: &str, lmax: &str, starter: &str) {
    let (t, tt, lmax): (u32, u32, i64) = (t.parse().unwrap(), tt.parse().unwrap(), lmax.parse().unwrap());
    let prot = pl(who);
    let c = cfg_from_env(prot, t, tt, lmax);
    let (ot, ott, fulla, macro_, fullopp) = (c.ot, c.ott, env_flag("TCB_FULLA"), env_flag("TCB_MACRO"), env_flag("TCB_FULLOPP"));
    let (arules, brules) = (c.arules.clone(), c.brules.clone());
    let t0 = Instant::now();
    let save = std::env::var("TCB_SAVE").ok();
    let dir = match &save {
        Some(d) => std::path::PathBuf::from(d),
        None => std::path::PathBuf::from(std::env::var("TCB_WORK").unwrap_or("tables".into()))
            .join(format!(".work-r{}", std::process::id())),
    };
    let s0 = model::init(pl(starter));
    let (sv, progs) = solver::reach(&c, &s0, &dir);
    println!("{} positions ({} bases at {} levels)", sv.n, sv.nb, sv.nl);
    let start = if mode == "safe" { if c.up() { 1 } else { INF } } else { c.lose() };
    solver::solve(&c, &sv, progs, start);
    let v = sv.get(sv.id(&fix::key_gen(c.full_a, &s0)).unwrap());
    println!("{who} {mode} from the start position: {}  ({:.1}s)", show(&c, v), t0.elapsed().as_secs_f64());
    let b = |x: bool| if x { "1" } else { "0" }.to_string();
    match save {
        Some(path) => {
            let hex: String = fix::key_gen(c.full_a, &s0).iter().map(|x| format!("{x:02x}")).collect();
            let h: Vec<(String, String)> = vec![
                ("mode", mode.to_string()),
                ("who", who.to_string()),
                ("t", t.to_string()),
                ("ot", ot.to_string()),
                ("tt", tt.to_string()),
                ("ott", ott.to_string()),
                ("lmax", lmax.to_string()),
                ("fulla", b(fulla)),
                ("macro", b(macro_)),
                ("bmacro", brules.list.join(",")),
                ("amacro", arules.list.join(",")),
                ("fullopp", b(fullopp)),
                ("blife", s0.side_b.life.to_string()),
                ("start", hex),
            ]
            .into_iter()
            .map(|(k, v)| (k.to_string(), v))
            .collect();
            solver::save_meta(&sv, &h);
            println!("saved {} positions to {path}", sv.n);
        }
        None => {
            drop(sv);
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let a: Vec<&str> = args.iter().map(|s| s.as_str()).collect();
    match a.as_slice() {
        [_, "walk", seed, steps] => walk::run(seed.parse().unwrap(), steps.parse().unwrap(), false),
        [_, "walk", seed, steps, "bias"] => walk::run(seed.parse().unwrap(), steps.parse().unwrap(), true),
        [_, "fix", mode, who, t, tt, lmax, starter] => fix_cmd(mode, who, t, tt, lmax, starter),
        [_, "progstats-table", dir, who, t, tt, every] => {
            let c = cfg_from_env(pl(who), t.parse().unwrap(), tt.parse().unwrap(), 100);
            progstat::run_table(&c, dir, every.parse().unwrap())
        }
        [_, "progstats", who, t, tt, starter, n, seed] => {
            let c = cfg_from_env(pl(who), t.parse().unwrap(), tt.parse().unwrap(), 100);
            progstat::run(&c, &model::init(pl(starter)), n.parse().unwrap(), seed.parse().unwrap())
        }
        _ => {
            eprintln!("usage: rsolver walk SEED STEPS [bias] | rsolver fix safe|win A|B T TT LMAX STARTER");
            std::process::exit(2);
        }
    }
}
