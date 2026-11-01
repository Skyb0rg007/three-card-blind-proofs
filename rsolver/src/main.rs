//! rsolver: a Rust port of the OCaml fixed-point solver (solver/), for
//! speed. It reads and writes the same tables. Commands:
//!   walk SEED STEPS [bias]            the differential-test walk (as `main walk`)
//!   fix safe|win A|B T TT LMAX STARTER as `main fix`, with the same TCB_*
//!                                     variables (no ranks, lines or warm starts yet);
//!                                     with TCB_BIG=1 (`fix safe A` only), one A Walker
//!                                     is unbounded (fix::Line)
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
        big: env_flag("TCB_BIG"),
        bigref: env_int("TCB_BIGREF", 20) as i64,
        bigcheck: env_flag("TCB_BIGCHECK"),
    }
}

/// `fix safe A` or `fix win B` with `TCB_BIG=1`: one A Walker unbounded
/// (see `fix::Line`). A-safe: A's Walker past its cap T becomes BIG.
/// B-win: A's Walker past TCB_OT becomes BIG instead of saturating, and a
/// second one is a loss for B.
fn big_cmd(c: &Cfg, starter: &str) {
    let k = c.big_k();
    if c.full_a {
        eprintln!("TCB_BIG=1 doesn't work with TCB_FULLA");
        std::process::exit(2);
    }
    // B's largest power or toughness total: its Walker and its Thopters
    let btotal = if c.prot == Player::A { (c.ot + 1) + c.ott } else { c.t + c.tt };
    if c.prot == Player::A && !(k > btotal && k > 20) {
        eprintln!("TCB_BIG=1 needs K = T + 1 = {k} > (TCB_OT + 1) + TCB_OTT = {btotal} and K > 20, so that BIG outsizes every B creature total");
        std::process::exit(2);
    }
    if c.prot == Player::B && k <= btotal {
        eprintln!("TCB_BIG=1 needs K = TCB_OT + 1 = {k} > T + TT = {btotal}, so that BIG outsizes every B creature total");
        std::process::exit(2);
    }
    if c.prot == Player::B && std::env::var("TCB_RANKS").ok().as_deref() == Some("1") {
        eprintln!("TCB_BIG=1 doesn't keep ranks");
        std::process::exit(2);
    }
    if !c.strict("dmg") || !c.strict("die") || !c.strict("many") {
        println!("warning: TCB_LAX is set, so the opponent's caps are relaxed and the result is not sound");
    }
    println!("BIG mode: K = {k}, reference n = {}, BIG check {}", c.bigref, if c.bigcheck_on() { "on" } else { "off" });
    let t0 = Instant::now();
    // TCB_SAVE=DIR keeps dig, keys, vals (c) and beta (one byte per
    // position) there, for comparisons; it is not a table `fixload` reads
    let save = std::env::var("TCB_SAVE").ok();
    let dir = match &save {
        Some(d) => std::path::PathBuf::from(d),
        None => std::path::PathBuf::from(std::env::var("TCB_WORK").unwrap_or("tables".into())).join(format!(".work-r{}", std::process::id())),
    };
    let s0 = model::init(pl(starter));
    let (sv, progs) = solver::reach(c, &s0, &dir);
    println!("{} positions ({} bases at {} levels)", sv.n, sv.nb, sv.nl);
    if c.prot == Player::B {
        use std::sync::atomic::Ordering::Relaxed;
        println!(
            "second BIG Walker (a loss for B): {} edges in {} of {} compiled turns",
            fix::SECOND_EDGES.load(Relaxed),
            fix::SECOND_TURNS.load(Relaxed),
            sv.nb
        );
    }
    let beta = solver::solve_big(c, &sv, progs);
    let i0 = sv.id(&fix::key_gen(false, &s0)).unwrap();
    let v = sv.get(i0);
    println!(
        "{} (BIG) from the start position: {}, c = {}, beta = {}  ({:.1}s)",
        if c.prot == Player::A { "A safe" } else { "B win" },
        show(c, v),
        if v >= INF { "inf".into() } else if v <= NINF { "-inf".into() } else { v.to_string() },
        beta[i0],
        t0.elapsed().as_secs_f64()
    );
    solver::big_stats(c, &sv, &beta);
    if std::env::var("TCB_NOSPOT").ok().as_deref() != Some("1") {
        solver::spot_check_big(c, &sv, &beta);
    }
    drop(sv);
    if save.is_some() {
        std::fs::write(dir.join("beta"), beta.iter().map(|&b| b as u8).collect::<Vec<u8>>()).unwrap();
        println!("saved c and beta to {}", dir.display());
    } else {
        let _ = std::fs::remove_dir_all(&dir);
    }
}

fn fix_cmd(mode: &str, who: &str, t: &str, tt: &str, lmax: &str, starter: &str) {
    let (t, tt, lmax): (u32, u32, i64) = (t.parse().unwrap(), tt.parse().unwrap(), lmax.parse().unwrap());
    let prot = pl(who);
    let c = cfg_from_env(prot, t, tt, lmax);
    if c.big {
        if (prot == Player::A) != (mode == "safe") {
            eprintln!("TCB_BIG=1 needs `fix safe A` or `fix win B`");
            std::process::exit(2);
        }
        return big_cmd(&c, starter);
    }
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
        [_, "treesize", dir, who, t, tt, every] => {
            let c = cfg_from_env(pl(who), t.parse().unwrap(), tt.parse().unwrap(), 100);
            progstat::tree_sizes(&c, dir, every.parse().unwrap())
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
