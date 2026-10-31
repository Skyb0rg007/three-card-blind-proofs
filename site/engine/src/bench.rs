//! Native self-play for tuning and timing the search:
//!   engine-bench BUDGET_MS TURNS [A|B] [LIFE_A LIFE_B] [random-A|random-B]
//! Plays the engine against itself (or against a uniformly random player
//! on one side) and prints one line per turn and the search statistics.
//!
//!   engine-bench trace < RECORD
//! reads a game record (whitespace-separated: starter lifeA lifeB moves...)
//! and prints the walk block of every state along it, for test/trace-check.mjs.

use tcb_engine::model::*;
use tcb_engine::search::Search;
use tcb_engine::{now, start, walk};


fn trace() {
    let mut input = String::new();
    std::io::Read::read_to_string(&mut std::io::stdin(), &mut input).unwrap();
    let rec: Vec<u32> = input.split_whitespace().map(|x| x.parse().unwrap()).collect();
    let mut out = String::new();
    for k in 3..=rec.len() {
        let (s, applied) = tcb_engine::replay(&rec[..k]);
        assert_eq!(applied, k - 3, "illegal move in record");
        out.push_str(&tcb_engine::walk_lines(&s));
    }
    print!("{out}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(|s| s.as_str()) == Some("trace") {
        return trace();
    }
    let budget: f64 = args.get(1).and_then(|x| x.parse().ok()).unwrap_or(1000.0);
    let turns: u32 = args.get(2).and_then(|x| x.parse().ok()).unwrap_or(30);
    let starter = if args.get(3).map(|s| s.as_str()) == Some("B") { Player::B } else { Player::A };
    let la: u32 = args.get(4).and_then(|x| x.parse().ok()).unwrap_or(20);
    let lb: u32 = args.get(5).and_then(|x| x.parse().ok()).unwrap_or(20);
    let random = match args.get(6).map(|s| s.as_str()) {
        Some("random-A") => Some(Player::A),
        Some("random-B") => Some(Player::B),
        _ => None,
    };
    let mut s = start(starter, la, lb);
    let mut sr = Search::new();
    let mut turn = 0;
    let mut decisions = 0u32;
    let mut max_ms: f64 = 0.0;
    let mut depth_sum = 0u64;
    let mut searched = 0u32;
    let mut rng: u64 = 12345;
    let t0 = now();
    while winner(&s).is_none() && turn <= turns {
        if is_turn_start(&s) {
            turn += 1;
            println!("turn {turn:3} {}", walk::state(&s));
        }
        let ms = moves(&s);
        let idx = if random == Some(to_move(&s)) {
            rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            ((rng >> 33) % ms.len() as u64) as usize
        } else {
            let c = sr.think(&s, budget, 40);
            decisions += 1;
            if c.candidates > 1 {
                searched += 1;
                depth_sum += c.depth as u64;
                max_ms = max_ms.max(c.ms);
                if !matches!(ms[c.index], Move::Pass) {
                    println!(
                        "    {} plays {:<14} value {:>8} depth {} nodes {} {:.0}ms",
                        if to_move(&s) == Player::A { "A" } else { "B" },
                        walk::mv(&ms[c.index]),
                        c.value,
                        c.depth,
                        c.nodes,
                        c.ms
                    );
                }
            }
            c.index
        };
        s = step(&s, &ms[idx]);
    }
    println!("final {}", walk::state(&s));
    println!("winner {:?}", winner(&s));
    println!(
        "decisions {decisions}, searched {searched}, mean depth {:.2}, max {:.0}ms, total {:.1}s",
        depth_sum as f64 / searched.max(1) as f64,
        max_ms,
        (now() - t0) / 1000.0
    );
}
