
# three-card-blind-proofs

This repo contains a mechanization of the famous open problem in
MTG three-card blind.

## The background

[Three card blind](https://www.3cardblind.com/) is a MTG format where each
player has perfect info, and matchups are resolved by playing the game
optimally.

One matchup complicated things so much that it became impossible to determine,
resulting in a card banning.

## The matchup

Player A has the deck:

- [Hangarback Walker][]
- [Hangarback Walker][]
- [City of Traitors][]

Player B has the deck:

- [Hangarback Walker][]
- [Elixir of Immortality][]
- [City of Traitors][]

The goal: determine whether either player has a winning strategy (both when
Player A starts and when Player B starts).

The official channel made a YouTube video on the topic [here](https://youtu.be/hdaiKwKN50U).

## This repo

This repo contains a [Rocq][] mechanization of the problem and a proof of the solution.

| Opening | Result | Status |
|---|---|---|
| B plays first | B can force a win | proved in Rocq |
| A plays first | A can't force a win | proved in Rocq |
| A plays first | B can't force a win, so the game is a draw | proved in Rocq |

Rocq also proves three facts about the model itself (all in `spec/Claims.v`):

- the game never gets stuck: in every position without a winner, the player
  to move has a legal move (`never_stuck`);
- legal moves keep every position well formed: no card is created or lost,
  and combat only refers to Walkers and Thopters that exist (`preservation`);
- every legal move changes the position, so nobody can stall by repeating a
  move that does nothing (`no_idle_moves`).

### The A-first draw

The second half is that A never loses going first. The solver finds this
with every legal B move: A is safe up to B life 20, which is exactly B's
starting life. The table behind it treats one of A's Walkers as unbounded:
it stands for K + n counters for every n ≥ 0, and each position stores a line
c + b n, the most life B can have there with A still safe.

`proofs/core/CheckerA.v` checks line-valued tables, and
`proofs/core/SaturationA.v` proves the checker sound, both for A's unbounded
Walker and for B's Walker saturated at a fixed size. `proofs/adraw` holds
0.58M positions of the solver's table, enough for the check of the
opening (a position can be answered by the same position with less A life,
or with A's two Walkers in the other order),
and Rocq checks every entry of it, so `safe PA (init PA)` (`a_first_a_safe`)
is a theorem, and with `a_first_b_safe` the A-first game is a draw
(`a_first_draw`). `REDUCTION.md` (R7 and the end) has the details.

`STRATEGY.md` explains the three results in plain Magic terms:

- short rule strategies for B (both openings) and for A (A first), with machine checks of how far each agrees with the certificates;
- the key lines;
- what the certificates' numbers measure, and why the A-first draw is exactly at 20.

## Auditing the result

The repository is split so that you only have to read one directory.

- **`spec/`: read this.** It defines the problem and states the claims.
  It contains no proofs.
  - `RULES.md`: the rules version (the Comprehensive Rules from when Hangarback
    Walker was banned), the card text, and every modelling simplification,
    each with its justification.
  - `Model.v`: the game, as code. It defines states, the opening, the legal
    moves and how each move changes the state.
  - `Game.v`: what it means for a player to win (force the opponent to lose in
    finitely many moves) or to be safe (never lose).
  - `Claims.v`: the claims, stated with the definitions above.
- **`proofs/`: let Rocq check this.** `results/Results.v` proves each claim
  of `spec/Claims.v` with no hypotheses. Everything else in `proofs/`
  supports it:
  - `core/Checker.v` and `core/WinCert.v` define checkers for B's safety and
    for wins, and prove them sound for any table of positions at all
    (`core/Saturation.v` proves the simulation facts `Checker.v` needs).
    `core/CheckerA.v` and `core/SaturationA.v` do the same for A's safety,
    with line-valued tables.
  - `core/Progress.v`, `core/Preservation.v` and `core/Idle.v` prove the facts
    about the model: `never_stuck`, `preservation` and `no_idle_moves`.
  - `core/Packed.v` stores such a table compactly in primitive arrays, and proves
    that if every entry passes the checker, the claim holds. `core/PackedA.v`
    does the same for line-valued tables. The entries are checked with
    `core/MemoB.v` and `core/MemoA.v`: the same searches with a memo of
    the positions already searched, proved to imply the checkers above.
  - `bfirst/`, `afirst/` and `adraw/` hold the three tables (`Data*.v.xz`,
    computed by the solver). Each `Chunk*.v` runs the checker on a slice of
    the table with `vm_compute`.

Build everything with:

```sh
nix-shell --run 'dune build -j 4'
```

This takes about 0.8 CPU-hours (16 minutes with `-j 3`): Rocq runs the
checker on 0.57M positions for the B-first claim (`proofs/bfirst`, 0.31
CPU-hours: 16 chunks of 0.9–1.5 minutes), 0.13M for A-first B-safe
(`proofs/afirst`, 0.05 CPU-hours: 4 chunks of 0.7–0.8 minutes) and 0.58M
for A-first A-safe (`proofs/adraw`, 0.38 CPU-hours: 24 chunks of 0.7–1.2
minutes). Each job needs about 1.3 GB of memory or less.

For each theorem in `proofs/results/Results.v`, the build prints the
assumptions it rests on. The only ones are Rocq's primitive 63-bit integers
and arrays (`int`, `add`, `ltb`, `array`, `get`, …) and the standard library
axioms that specify them (`add_spec`, `ltb_spec`, `eqb_correct`, …). There
are no other axioms. To see the
theorems yourself, run `nix-shell --run 'dune rocq top proofs/results/Results.v'`
and then:

```coq
From TCB.Results Require Import Results.
Check b_first_b_wins_holds.  (* : b_first_b_wins *)
```

### What you have to trust

Only Rocq itself: its kernel, including the bytecode virtual machine behind
`vm_compute`, and its primitive integers and arrays, which the kernel computes
with machine operations.

You don't have to trust the tables in `proofs/bfirst`, `proofs/afirst` and `proofs/adraw`,
the solver that computed them (`rsolver/`, `solver/`), or `xz`. Rocq checks
every entry of each table during the build. The theorems in `proofs/core`
say that any table whose entries all pass that check proves the claim, so a
wrong or corrupted table can only make the build fail. It can't make it prove
something false.

### Reproducing the tables

The tables come from the solver (each step takes up to about 30 minutes and
7 GB of memory):

```sh
nix-shell --run 'dune build solver'
(cd rsolver && nix-shell ../shell.nix --run 'cargo build --release')
R=rsolver/target/release/rsolver
C=_build/default/solver/main.exe
COMMON='TCB_MACRO=1 TCB_FULLOPP=1 TCB_BMACRO=blk,atk2,dmg'

export TCB_JOBS=4

# A plays first: B is safe, so A can't force a win
env $COMMON TCB_OT=9 TCB_OTT=20 TCB_SAVE=tables/bsafe-afirst-ot9 $R fix safe B 10 10 100 A
TCB_ROUNDS=4 $C certify-safe-export tables/bsafe-afirst-ot9 A proofs/afirst 4 200

# B plays first: B wins
env $COMMON TCB_RANKS=1 TCB_OT=12 TCB_OTT=12 TCB_SAVE=tables/bwin-bfirst-12-full $R fix win B 4 12 100 B
TCB_ROUNDS=4 $C certify-win-export tables/bwin-bfirst-12-full B proofs/bfirst 16 200

# A plays first: A is safe (one unbounded A Walker, lines c + b n)
env TCB_BIG=1 TCB_BIGCHECK=1 TCB_MACRO=1 TCB_FULLOPP=1 TCB_NOBOUND=1 TCB_OT=5 TCB_OTT=5 \
  TCB_AMACRO=atk2,pump,order,dmg TCB_SAVE=tables/asafe-afirst-big-o5 $R fix safe A 20 8 100 A
export TCB_HB=6 TCB_OTT=5
$C certify-a tables/asafe-afirst-big-o5 A tables/adraw-0.entries
for r in 1 2 3 4 5 6; do
  TCB_PREV=tables/adraw-$((r - 1)).entries $C certify-a tables/asafe-afirst-big-o5 A tables/adraw-$r.entries
done
# the smallest round (here adraw-6: 0.58M entries)
TCB_M=64 TCB_FUEL=200 $C certify-a-export tables/adraw-6.entries A proofs/adraw 24
```

`main.exe rechunk proofs/afirst 4` (or `proofs/bfirst 16`) checks an exported
table again as Rocq will and cuts it into chunks of near-equal work,
leaving `Data.v.xz` as it is.

The export keeps only the positions the check of the opening needs, runs
the same check as Rocq (the checkers extracted to OCaml) and writes the
Rocq files, with the chunks cut by the work the check does on each entry
(Rocq's time estimated from the nodes, moves and lookups of the check,
with coefficients fitted to a full build). The tables store each position
with A's two Walkers in one order, sorted as Rocq's lookups sort them
(`Sym.normA`).
It follows the check from the opening, choosing the protagonist's moves so
that their turn starts need as few new entries as possible, and a lookup
may answer with the same position at another A life (more A life for B's
tables, less for A's), so one entry serves several. `TCB_ROUNDS=N` runs
this N more times, preferring the entries the previous run used
(`TCB_PREV=ENTRIES` does the same for `certify-a`, from a previous run's
entries). The B-first records get the smallest ranks their checks allow
(`TCB_RERANK=0` keeps the solver's order). None of these choices is
trusted: Rocq tries every move and checks every entry.
For the A-safe table these are two steps: `certify-a` collects the
entries (choosing A's moves) and `certify-a-export` checks them again
exactly as Rocq will, with A trying every move (its attacks in reverse
order). The entries `certify-a` collects depend a little on `TCB_JOBS`
(its workers see each other's new entries only between layers) and vary
from round to round; the shipped table is the smallest round.

`REDUCTION.md` explains how the search space was reduced to make these
tables small enough to compute.

[Hangarback Walker]: https://scryfall.com/card/soc/348/hangarback-walker
[City of Traitors]: https://scryfall.com/card/tpr/237/city-of-traitors
[Elixir of Immortality]: https://scryfall.com/card/c21/243/elixir-of-immortality
[Rocq]: https://rocq-prover.org
