
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

| Opening | Result |
|---|---|
| B plays first | B can force a win |
| A plays first | A can't force a win (B never loses; whether B can force a win is still open) |

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
  - `core/Checker.v` and `core/WinCert.v` define checkers for safety and for
    wins, and prove them sound for any table of positions at all.
  - `core/Packed.v` stores such a table compactly in primitive arrays, and proves
    that if every entry passes the checker, the claim holds.
  - `bfirst/` and `afirst/` hold the two tables (`Data.v.xz`, computed by the
    solver). Each `Chunk*.v` runs the checker on a slice of the table with
    `vm_compute`.

Build everything with:

```sh
nix-shell --run 'dune build -j 4'
```

This takes about 2.5 CPU-hours (50 minutes with `-j 3`): Rocq runs the checker on 1.5M positions for
the B-first claim and 1.6M for the A-first one. Each job needs about 1 GB of
memory, so choose `-j` to fit your machine.

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

You don't have to trust the tables in `proofs/bfirst` and `proofs/afirst`,
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

# A plays first: B is safe, so A can't force a win
env $COMMON TCB_OT=10 TCB_OTT=20 TCB_SAVE=tables/bsafe-afirst-10-full $R fix safe B 10 10 100 A
$C certify-safe-export tables/bsafe-afirst-10-full A proofs/afirst 48 200

# B plays first: B wins
env $COMMON TCB_RANKS=1 TCB_OT=14 TCB_OTT=14 TCB_SAVE=tables/bwin-bfirst-14-full $R fix win B 4 14 100 B
$C certify-win-export tables/bwin-bfirst-14-full B proofs/bfirst 48 200
```

The export keeps only the positions the check of the opening reaches, runs
the same check as Rocq (the checkers extracted to OCaml) and writes the
Rocq files.

`REDUCTION.md` explains how the search space was reduced to make these
tables small enough to compute.

[Hangarback Walker]: https://scryfall.com/card/soc/348/hangarback-walker
[City of Traitors]: https://scryfall.com/card/tpr/237/city-of-traitors
[Elixir of Immortality]: https://scryfall.com/card/c21/243/elixir-of-immortality
[Rocq]: https://rocq-prover.org
