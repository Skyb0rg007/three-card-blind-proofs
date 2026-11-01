
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
| A plays first | A can't force a win (whether B can is still open) |

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
- **`proofs/`: let Rocq check this.** `Results.v` proves each claim of
  `spec/Claims.v`. Everything else in `proofs/` supports it.

Build everything with:

```sh
nix-shell --run 'dune build'
```

The build prints `Closed under the global context` for each theorem in
`proofs/Results.v`. That means the proofs use no axioms.

### What Rocq does not check

Each theorem in `proofs/Results.v` takes one hypothesis: every entry of a table
computed by the solver passes a checker. The checkers are defined and proved
sound in `proofs/` for any table at all, so the solver and its tables need no
trust. But the check itself runs outside Rocq: the tables are too large to
check inside it (90.8M entries for the A-first result, 1.1M for the B-first
one). The checkers are extracted to OCaml, and `solver/certify.ml` runs them
over every entry. Believing the results therefore also means trusting:

- Rocq's extraction to OCaml, and the OCaml compiler;
- `solver/certify.ml`, which reads the tables, defines the lookup function the
  hypothesis is about, and runs the check on every entry it answers for.

To reproduce the checks (the tables are not committed; each takes up to about
30 minutes and 7 GB of memory):

```sh
nix-shell --run 'dune build'
(cd rsolver && nix-shell ../shell.nix --run 'cargo build --release')
R=rsolver/target/release/rsolver
C=_build/default/solver/main.exe
COMMON='TCB_MACRO=1 TCB_FULLOPP=1 TCB_BMACRO=blk,atk2,dmg'

# A plays first: B is safe, so A can't force a win
env $COMMON TCB_OT=10 TCB_OTT=20 TCB_SAVE=tables/bsafe-afirst-10-full $R fix safe B 10 10 100 A
$C certify tables/bsafe-afirst-10-full A

# B plays first: B wins
env $COMMON TCB_RANKS=1 TCB_OT=14 TCB_OTT=14 TCB_SAVE=tables/bwin-bfirst-14-full $R fix win B 4 14 100 B
$C certify-win tables/bwin-bfirst-14-full B
```

`REDUCTION.md` explains how the search space was reduced to make these
tables small enough to compute.

[Hangarback Walker]: https://scryfall.com/card/soc/348/hangarback-walker
[City of Traitors]: https://scryfall.com/card/tpr/237/city-of-traitors
[Elixir of Immortality]: https://scryfall.com/card/c21/243/elixir-of-immortality
[Rocq]: https://rocq-prover.org
