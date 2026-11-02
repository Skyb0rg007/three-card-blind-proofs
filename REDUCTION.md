# Reducing the game to a finite one

Where things stand:

- **B first: B wins.** Certified, and proved in Rocq (`b_first_b_wins`).
- **A first: A can't win.** B is safe; certified, and proved in Rocq
  (`a_first_b_safe`).
- **A first: B can't win either, so the game is a draw.** The solver finds
  A safe up to B life 20, exactly B's starting life, with every legal B move
  (R7 and the last section). Certified, and proved in Rocq
  (`a_first_a_safe`, `a_first_draw`).

A depth-bounded search can never show a draw. A draw needs two separate
facts:

- **B-safe:** B has a strategy that never loses (`safe PB` in `Game.v`).
- **A-safe:** A has a strategy that never loses (`safe PA`).

Each fact is witnessed by an invariant set of positions: a set that holds the
start, contains no lost position, and that the protagonist can always stay in,
whatever the opponent does. The game is infinite, because Walker counters,
Thopter counts and B's life are unbounded. So the work is to find reductions
that make such sets finite and computable, without becoming unsound.

`solver/fix.ml` (`main fix` / `main pfix`) implements the reductions below and
computes greatest fixed points (safety) and least fixed points (wins) over the
turn-start positions reachable from a start.

## R1. Turn starts only

Positions are kept only at the start of a turn (untap done, upkeep, nobody
has passed). Everything inside a turn is a finite game tree that is searched
again each time the position is evaluated. This is exact.

One wrinkle: the solvers stop at any upkeep window nobody has passed in,
including the one after the non-active player acts in the active player's
upkeep (the actor keeps priority). The packed key records only the active
player, so that position is read as the one where the active player has
priority. The two are not the same position. The certificate checker
(`proofs/core/Checker.v`) therefore counts a turn start only when the active
player has priority, and searches through the other case. The B-safe table
for the A-first opening passes that stricter check (see Results).

## R2. B's life as a threshold (exact)

Every property used here is monotone in B's life. More life never hurts B,
because life only matters through the "life ≤ 0" check. Within a turn, B's
life only *shifts*: combat damage subtracts and Elixir adds 5. No move's
legality or effect depends on its value. So B's life is dropped from the
position and replaced by a threshold:

| property | value of a position |
|---|---|
| B-safe, B-wins | least B life with which the property holds |
| A-safe, A-wins | greatest B life with which the property holds |

Thresholds compose exactly through a turn:
- an edge where B's life changes by δ maps a child value v to v − δ;
- after combat damage, B's death is folded in: for B, `max(1 − δ, v)`; for A, `max(−δ, v)`;
- the protagonist takes the best child, the opponent the worst.

This removes the one dimension that is unbounded in *every* line of play: B
can gain 5 life every two rounds forever.

Monotonicity is proven in `proofs/core/Mono.v`, for either player: `wins_bump`
(a win stays a win with more life), `safe_bump` (likewise for safety) and
`wins_opp_bump` (an opponent's win against more life is a win against
less). All three rest on `step_bump`: adding life to a player commutes with
every move, unless the original move made that player lose.

Values are cut at `lmax` on the pessimistic side only:
- B needing more than `lmax` counts as "never";
- A's bound on B's life is lowered to `lmax`.

## R3. Capping the protagonist (sound by restriction and monotonicity)

The protagonist's strategy may be restricted freely: a safe strategy inside a
restricted move set is a safe strategy. Two restrictions are used.

- Its Walkers never pump above `t` counters.
- Its Thopters above `tt` are discarded, tapped ones first. Monotonicity: a
  position with one more Thopter for a player is at least as good for that
  player. The player can play exactly as before and ignore the Thopter. No
  opposing option depends on the existence of an unused untapped or tapped
  Thopter: attacks are unrestricted, and blocks and damage-assignment orders
  only involve creatures the owner chose to block with. Proven in
  `proofs/core/Mono.v` as `wins_thop` and `safe_thop`: if `t` matches `s`
  except that `p` has at least as many untapped and at least as many tapped
  Thopters, then a win or safety for `p` from `s` holds from `t` too. Every
  step preserves the relation (`step_thop`), the opponent's moves are the
  same (`moves_thop_opp`), and `p`'s own moves only grow (`moves_thop_mine`).

## R4. Saturating the opponent (sound by pessimism)

The opponent may not be restricted. Its unbounded quantities saturate
instead.

- A Walker pumped above `ot` counters becomes **huge** and is kept at
  `ot + 1`. Any event whose outcome depends on the exact size of a huge
  Walker counts as an immediate loss for the protagonist:
  - it deals combat damage to the protagonist;
  - it dies, giving an unbounded number of Thopters;
  - its blockers' total toughness reaches `ot + 1`, so the representative
    could die or fail to kill them where the real Walker would not;
  - it blocks a protagonist Walker with at least `ot + 1` power.

  In every other combat the real Walker and the representative behave
  identically: it kills every Walker of at most `ot` counters and every
  Thopter, and survives anything below its size.
- More than `ott` opposing Thopters counts as a loss for the protagonist
  (`TCB_OTT`, by default `tt`).

  When B is the protagonist this rule can be made vacuous. A's Thopters
  only come from its two Walkers dying, and A has no Elixir, so a dead
  Walker never returns. A Walker that dies has at most `ot` counters (a huge
  one dying is already a loss), so A never has more than `2 ot` Thopters
  beyond those it starts with. With `ott` at least that, the rule never
  fires and costs B nothing.

**Proved in Rocq, in both directions.** With B as protagonist, A's Walkers
saturate: `proofs/core/Saturation.v` proves the simulation facts that
`Checker.cert_safe` needs. With A as protagonist, B's Walker saturates:
`proofs/core/SaturationA.v` proves the same for `CheckerA.cert_safe`. In
both, a huge event or too many opposing Thopters is a loss in the checker,
and the proof shows that every other step of the real game is matched by a
step of the saturated one.

## R5. A's life pinned at 20 (B-safe only, sound by monotonicity)

`TCB_FULLA=1` resets A's life to 20 at every turn start. For B-safety this is
pessimistic, since A's life is monotone good for A like B's is for B. It
removes A's life from the position (a factor of 20), and it is valid
whenever B's defence does not rely on threatening to kill A. The
monotonicity used here is `safe_bump` with `p = PA` (`proofs/core/Mono.v`).

## R5b. Solving by A-life level (exact)

A never gains life, so a turn only ends in a position with the same or
lower A life. Positions are therefore solved one A-life level at a time,
lowest first, each swept (alternately forwards and backwards) until no
value changes. The fixed point is unchanged. Digest collisions are ignored:
for n positions they occur with probability about n²/2⁶⁴, around 10⁻⁵ at
ten million.

**The levels share their turns (exact).** A's life enters a turn at one
point only: combat damage on B's turn, at most once per turn, kills A when it
reaches A's life. The damage itself does not depend on A's life, and no
move, filter or cap does either. So the solver works with *bases*, turn-start
keys with A's life left out. It explores bases (expanding each with A on
20 life, which gives every successor of every level, since lower life only
ends more lines), and compiles each base's turn once, with A on a life no
turn can take. The damage step becomes a guard node that is a B win at any
level up to the damage, and a turn start records its base and the damage A
took on the way, so at level l it reads the position at level l − u. (A
turn start after 20 or more damage is dead at every level; exploration never
reached it and the guard always decides, so it gets a placeholder.) Every
base is then solved at every level from 1 to A's starting life. That
includes some combinations that can't be reached, but their values are
still exact. On the opening, where nearly every base occurs at every level,
exploration and compiling shrink by about the number of levels. The
fortress and two-Walker tables come out identical position by position
(`main fixcmp OLD NEW`).

**Bounds from the level below (exact).** In the abstraction too, more life
is never worse for A. By induction on the level: at level l + 1 a guard fires
for fewer damages than at level l, and a turn start after damage u ≥ 1 reads
level l + 1 − u, which by induction is at least as good for A as level l − u.
So level l + 1's operator is at least as good for A as level l's, pointwise
and monotonically, and so are its least and greatest fixed points. The value
one level down therefore bounds each position's value:
- When B's win or A's safety is sought, the bound is on the far side of
  the fixed point (the best B could do, or the worst A could suffer). A
  position whose value reaches it is final, and later sweeps skip it. That
  includes every position already lost one level down. At the lowest level,
  the extreme value (B needing 1 life; A losing) plays the same role.
- When B's safety or A's win is sought, the bound is a closer start than
  the extreme, and each level starts from it.
The results are unchanged (`TCB_NOBOUND=1` turns this off for comparison).
On the fortress the four checks need 2 to 6 times fewer turn evaluations,
with identical values, history and lines.

All per-position data lives on disk (`solver/disk.ml`), so memory stays
bounded:
- **Exploration** is a breadth-first search with duplicate detection on
  disk. Each layer's successors are buffered, sorted into runs, merged, and
  filtered against the sorted file of digests seen so far.
- **A position** is its rank in the sorted digest file. The digests (8
  bytes), the packed keys (32 bytes) and the values (4 bytes) are
  memory-mapped files. Lookups use interpolation search, which takes only a
  few probes because the digests are uniform.

Anonymous memory is the sort buffer (`TCB_MEM` megabytes, 256 by default)
plus a few words per position of the level being solved. The mapped pages
are file-backed, so the kernel drops them under pressure instead of
swapping. The solver works in `TCB_SAVE=DIR` if that is given; otherwise it
uses a temporary directory under `TCB_WORK` (default `tables/`) and deletes
it at the end.

The solver runs on `TCB_JOBS` forked workers (default: one per processor;
`solver/par.ml`). They share the mapped files:
- **Exploration:** each worker expands a slice of the frontier into its own
  sorted runs.
- **Compiling:** each worker compiles a slice of the bases' turns.
- **Sweeps:** workers sweep their slices concurrently, writing to the shared
  values. The operator is monotone and starts at its bottom (or top), so
  this chaotic iteration reaches the same fixed point. It stops after a
  round in which no worker changed a value.
- **Ranks:** the rounds stay synchronous.

The two-Walker subgame (1.23M positions) takes 103 s on 14 workers, against
753 s on one. Its saved table is byte-identical, and the workers peak at
171 MB of anonymous memory in total.

**Warm starts.** `TCB_FROM=TABLE` starts a win solve from a saved win table
of the same check whose caps (`t`, `ot`, `tt`, `ott`, `lmax`) are no larger.
The old table may also restrict more: a macro protagonist, or an opponent
with every legal move (`TCB_FULLOPP=1`) where this run filters it. Both only
make its values worse for the protagonist. A position the old table never
reached (a protagonist Walker above the old `t`) starts lost. Each
position starts at the old value of its image under the old caps (its
Walkers clamped, its Thopters cut, a loss if the opponent has too many).
That value is never better than the new fixed point: raising a protagonist
cap adds options (R3), and raising an opponent cap moves R4's losses further
out, while a formerly huge Walker behaves either as its representative did or
in a way the old abstraction already counted as a loss. Sweeps then keep only
changes for the better. The iteration stays on the pessimistic side of the
fixed point. When a round changes nothing, every value is at least as good
as one step from the current values, and any such point is at least as good
as the fixed point; being no better either, it is the fixed point. So the result is exactly the cold
solve's, which the tests confirm: the fortress (8/8 to 10/10) and the
two-Walker subgame (6/8 to 8/10, where the start value moves from "never" to
B life ≥ 9) give byte-identical values with about half the sweeps. Ranks
can't be numbered from a warm start, so `TCB_FROM` excludes `TCB_RANKS`.

**The Rust solver (`rsolver/`).** A port of the model (`spec/Model.v`),
the filter and macros, and `fix`. It writes the same tables, so `main
fixcmp` and `main fixload` work on them. It is not trusted:
- `main walk SEED STEPS [bias]` and `rsolver walk` print the same seeded
  random walk through the model: every state, its four move lists (full,
  filter, both macros), and each turn start's packed key and digest. The
  outputs must be byte-identical. 16 walks of 100k–200k steps are.
- Tables solved by both must have identical values. So far: A-safe 4/4 and
  6/6, B-win 4/6 (macro), B-safe 4/4 with A's life pinned, and A-win 4/4,
  B first, with every legal B move. All have 0 differences and the same
  number of program words.
- The spot check re-evaluates every 500th position through the model.

Differences from the OCaml solver:
- Threads instead of forked workers.
- Exploration in memory.
- **Worklist sweeps.** After compiling, each base gets the list of bases
  whose turns read it at the same A-life level: turn starts reached with no
  damage to A, or all of them when A's life is pinned. A sweep evaluates only
  dirty positions. A position's flag is cleared before it is evaluated, and
  a change marks its readers dirty. So any change to an input leads to
  another evaluation, and a sweep that finds nothing dirty ends the level at
  the same fixed point. On the tests above this takes 2.3–9× fewer
  evaluations.
- **Compiled while exploring.** Each base's turn is compiled when it is
  expanded, and that one search also finds its successors. A turn start gets
  an id when first reached, from a sharded map shared by the threads, so
  programs refer to turn starts by discovery order. The tables stay in
  digest order, with a permutation from ids to bases.
- **Packed programs** (`fix::pack`). The compiled program is rewritten as:
  - a per-turn table of the turn starts it reads, ascending, as varint
    differences;
  - then the nodes, each child one varint: a constant, the node a given
    distance back, or a table entry.

  Rewrite rules:
  - A guard ("lost when A's life is at most g") and a change in B's life
    become two optional varints on the reference, instead of a node.
  - Single-child nodes fold into their references, identical nodes are
    shared, and a node read once with the same operator merges into its
    reader.

  Programs are 4–5× smaller than the OCaml word format. The A-safe 14/14
  programs drop from 54 GB to about 5.5 GB, so the sweeps run from the page
  cache instead of disk. Values are unchanged: the five comparison tables
  above are byte-identical.
- mimalloc, and each intra-turn state hashed once: 26% fewer instructions
  per compiled turn.
- No ranks, lines or warm starts yet.

Build with `nix-shell --run 'cd rsolver && cargo build --release'`, then
run `rsolver/target/release/rsolver fix …` with the same arguments and
`TCB_*` variables as `main fix`.

## R5c. Macro moves for the protagonist (sound by restriction)

`TCB_MACRO=1` restricts the protagonist to its macro move set:
`Reduce.b_macro` for B, `Reduce.a_macro` for A. A's macro attacks with no
Walker, every Walker, or its smallest or biggest one alone (with two Walkers
that is every subset), with no Thopters or all of them, and at B's end step
pumps only its biggest Walker; it also keeps two damage orders and the two
extreme damage assignments. For B, for each
attacking Walker, B can block with nothing, its own Walker, one chump
Thopter, or enough Thopters to kill it. Thopter trades are all or nothing.
Restricting the protagonist is always sound. On the fortress it shrinks the
compiled turns 4.4× and gives the same result.

The macro does cost B something in the opening. With A first, B Walker cap
4, `tt` = `ot` = `ott` = 10, B never wins either way, but full B moves make
2.55M of the macro table's 17.0M positions better for B (243k of them go from
lost to won, and most of the rest by 1–6 life). Full moves cost 1.5× the
bases and 6.9× the compiled program words. `TCB_BMACRO` lists which of B's
restrictions apply (`blk`, `tr`, `atk`, `dmg`; default all) so that each one's
cost can be measured. A table records the list, and a warm start needs the
old table's list to include the new one's. `atkN` relaxes `atk`: B attacks
with no Thopters, or with all but at most N. Positions of the macro table
that are still worse for B than with full moves, at the caps above:

| B's restrictions | still worse than full | bases | program words |
|---|---|---|---|
| all four (the macro) | 2,551,468 | 849k | 0.27G |
| all but `blk` | 2,550,648 | 849k | 0.43G |
| all but `tr` | 2,320,630 | 849k | 0.29G |
| all but `dmg` | 2,551,468 | 849k | 0.28G |
| all but `atk` | 284,182 | 1.29M | 1.07G |
| `blk,atk1,dmg` | 1,001,415 | 939k | 0.46G |
| `blk,atk2,dmg` | 381,644 | 1.02M | 0.61G |
| none (full moves) | 0 | 1.29M | 1.83G |

Nearly all of the cost is the attack rule: B wants to keep a few Thopters
home as blockers. `blk,atk2,dmg` recovers 85% of it for 2.25× the program.

A's macro has the same shape. `TCB_AMACRO` lists A's restrictions (`atk` or
`atkN`, `pump`, `order`, `dmg`; default all). For A-safe from the A-first
opening at 6/6, full A moves raise the start value from B life ≤ 12 to
≤ 13 and improve 750k of 4.95M positions, for 2.25× the program. Dropping
`atk` alone recovers all but 49k; `atk2,pump,order,dmg` reaches 13 with 112k
left, for 1.46× the program; `atk1` reaches 13 with 216k left, for 1.23×.

## R6. The exploration filter

Like the depth searches, `fix` currently uses `Reduce.moves`: timing
dominance that keeps pumps at end of turn or after blocks, Elixir in upkeep,
end step or after blocks, and X = 1. For the protagonist this is a
restriction, which is sound. For the opponent it must be justified by
dominance lemmas or replaced by `Rules.moves` before a certificate counts.
For the B wins in the results below it has been replaced: every one of them
was re-solved with `TCB_FULLOPP=1` (A gets every move in `Rules.moves`) and
came out the same, so they don't depend on R6.

Written dominance arguments for the opponent. Each removed move m is matched
by a kept plan that leaves the opponent at least as well off. In the cases
marked *mimic*, the opponent delays the action. In between, the plan keeps
an untapped Walker (or unspent card) that it simply doesn't use, and then
acts at the kept window, reaching the same state. The interim difference
can't matter: a Walker tapped by a pump can't attack or block, so its extra
counter is never seen until the delayed pump adds it too.
- **Pumps on your own turn** (any window). The Walker stays tapped through
  the opponent's turn, so it can't block there. Delaying to the opponent's
  end step uses the same City activation of the round, since City untaps
  only in its controller's untap step. *Mimic.* (Attacking Walkers are
  already tapped and can't pump.) The exception is mana left over in main
  phase 2, as when City's 2 mana pays for Elixir (1) and a pump (1): that
  City activation is gone by the end step, so the filter keeps a pump in
  main phase 2 while mana is left over.
- **Pumps on the opponent's turn before blocks** tap the Walker, so it can't
  block; **pumps of a non-blocking Walker after blocks or in later combat
  steps** don't affect combat. Delay to the end step. *Mimic.* The exception
  is mana left over from an earlier pump in the same step: it empties
  before the end step. The filter keeps any pump after blocks while mana is
  left over. Earlier versions of the filter did not, so they took a free
  counter from A. The four B wins above were re-solved with every legal
  move, so they are unaffected.
- **Casting in main phase 1** instead of main phase 2. A Walker is summoning
  sick either way, and the cast before combat only gives the opponent
  information and taps City before blocks. *Mimic.*
- **X = 0** puts the Walker straight into the graveyard. For A, which has no
  Elixir, that only loses the card: keeping it in hand is at least as good.
  For B it is a real option, since Elixir shuffles the graveyard back into
  the library; B's X = 0 is kept only in `TCB_FULLOPP` runs, and for B as
  protagonist dropping it is a restriction.
- **Elixir on your own turn after upkeep**, and **on the opponent's turn
  before blocks**. Delay to the opponent's next blocks or end step. The life
  arrives before any damage it could prevent, and the shuffle still comes
  before B's next draw. *Mimic.* Upkeep is different: shuffling before the
  draw step lets B draw a shuffled-in card that turn, so it is kept.
These arguments are written, not mechanized, and no result depends on them:
every result that counts gives the opponent every legal move
(`TCB_FULLOPP=1`), and the Rocq checkers do the same.

## R7. A's unbounded Walker (A-safe, proved sound)

A's defence going first depends on growth: B can bank 5 life per Elixir
cycle forever, and A stays safe only if its threat keeps growing too. So any
cap on A's own Walkers (R3) loses positions the real A holds, and every
capped A-safe check stalls below 20. `TCB_BIG=1` replaces the cap.

- An A Walker that reaches K = `t` + 1 counters becomes **BIG**: it is
  stored at K and stands for K + n counters, for every n ≥ 0 at once.
- K is above every total of B's (B's Walker saturates at `ot` + 1, R4, and
  B has at most `ott` Thopters), so BIG never dies, and every fight it is in
  comes out the same for all n. The only thing n changes is the damage BIG
  deals to B when unblocked.
- So a position's value is a **line** (c, b): A is safe whenever B's life
  is at most c + b n. An unblocked hit adds 1 to b. A pump on BIG reads the
  next position at n + 1. A pump that makes a new BIG reads it at n = 0. A
  pump that would make a second BIG is not allowed.

`proofs/core/CheckerA.v` checks a table of lines: it runs one turn of the
real model and moves the required line along each edge as above. It
gives B every legal move, and treats B's death as a line that is at most 0
for every n. `proofs/core/SaturationA.v` proves that a real state whose BIG
Walker has K + n counters behaves like the checker's state: the same moves,
the same steps except for B's life, which moves by n more on a hit. The
final theorems, `certified_safe_a` and `certified_opening_a`, are closed
under the global context. They need only `Hb < K` and `1 <= Hb` (`Hb` is B's
saturation size). So any line-valued table whose entries all pass the
checker, and whose opening line reaches 20, proves `safe PA (init PA)`.

## Results so far

Unless a row says otherwise, results use `lmax = 60` and the exploration filter.
The spot check passes in every run.

| start | check | caps | result |
|---|---|---|---|
| fortress¹ | B-safe | 4/4 | **safe with any B life** (155k positions; also with `TCB_FULLOPP=1`, 229k) |
| fortress¹ | A-safe | 6/6 | not safe (508k); still not safe with every rule in R4 relaxed |
| opening, A first | B-safe, A's life pinned | 4/4 | not safe (75k); with every rule in R4 relaxed, B needs 34 life |
| opening, A first | B-safe | 4/4 | not safe (1.43M positions, 10 min) |
| lone-walker fortress² | B-wins (lfp) | B Walker 3, tt 10, A huge > 10 | A on 4 life: **B wins with any life** (161k; also with every legal A move, 207k) |
| same | B-wins | B Walker 3, tt 14, A huge > 12 | A on 8: **any life** (740k; every legal A move, 963k); A on 12: **B life ≥ 3** (1.3M; every legal A move, 1.72M) |
| two A Walkers³ | B-wins, macro B | B Walker 4, tt 10, A huge > 8 | A on 4 life: **B wins with B life ≥ 9** (1.23M; every legal A move, 2.32M) |
| opening, A first | B-wins, macro B | B Walker 4, tt 12, A huge > 10 | **no B win** within these caps (19.3M positions, 5.9 h) |
| same | B-wins, macro B | B Walker 4, tt 14, A huge > 14 | **B wins with B life ≥ 25** (47.8M positions, 2.7 h on 12 workers); the caps above were binding |
| same | B-wins, macro B | B Walker 4, tt 18, A huge > 18 | **B wins with B life ≥ 25** (117M positions = 5.86M bases × 20 A-life levels, 2.0 h on 14 workers, warm-started from the row above). 8.8M of the 47.8M positions above gain value for B (5.1M of them go from lost to won), none lose any; they are mostly positions where A has 11–14 Thopters. The start value does not move. |
| same | B-wins, B macro `blk,atk2,dmg` | B Walker 4, tt 14, A huge > 14 | **B wins with B life ≥ 25** (59.4M positions = 2.97M bases × 20, 43 min on 14 workers, warm-started from the 14/14 macro table). 6.1M of that table's positions improve for B; the start value does not move. |
| opening, A first | A-safe, A macro | 6/6 | **A safe with B life ≤ 12** (4.95M positions, 41 s); A-win gives the same value |
| same | A-safe, A macro | 10/10 | **A safe with B life ≤ 15** (36.1M positions, 26 min). Raising one cap alone from 6/6 to 10 gives 12 (`t`, `tt`, `ott`) or 13 (`ot`): the caps only help together. |
| same | A-safe, A macro `atk2,pump,order,dmg`, `lmax` 100 | 14/14 | **A safe with B life ≤ 15** (162M positions = 8.1M bases × 20, 42 min with `rsolver`; 9.2 GB of packed programs). Bigger caps don't help: the check is stuck on the cap collapse. |
| same | A-wins, A macro `atk2,pump,order,dmg` | 10/10 | **A wins with B life ≤ 15** (40.7M positions, 71 min); the same as A-safe |
| same | A-wins | t 6, tt 6, ott 6, B huge > 6 / 10 / 14 | B life ≤ 13 / **15** / **15**; with B huge > 10 also 15 with A's filter instead of the macro, and 15 with every legal A move (`TCB_FULLMINE=1`, 823k bases). Relaxing every R4 rule (unsound) at 6/6 gives 15 too. |
| same | A-wins, A macro `atk2,…`, **every legal B move** (`TCB_FULLOPP=1`) | t 6, tt 6, ott 6, B huge > 10 | **A wins with B life ≤ 15** (12.0M positions, 10 min). Sound: B is unrestricted, and A's restrictions and caps only weaken A. |
| opening, B first | A-wins, as above, every legal B move | t 6, tt 6, ott 6, B huge > 10 | **A wins with B life ≤ 10** (12.0M positions, 10 min). Sound. |
| opening, A first | B-safe, B macro `blk,atk2,dmg`, `lmax` 100 | B Walker 10, tt 10, A huge > 10, ott 20 | **B safe with B life ≥ 20** (41.3M positions = 2.06M bases × 20, 7.2 min with `rsolver` on 14 threads; the OCaml solver took 42 min for the first A-life level alone). So A can't win from 20 with A's filter. |
| same | same, **every legal A move** (`TCB_FULLOPP=1`) | same | **B safe with B life ≥ 20** (81.7M positions = 4.09M bases × 20, 18.6 min, 3.2G program words). Sound: A is unrestricted, and B's macro, caps, A's saturation and `lmax` only weaken B. **A can't force a win from the real opening.** |
| same | **certificate check** (`main.exe certify`, extracted `Checker.check_node`) | same | **all 90.8M entries pass** (every base, A-life level and Walker order the lookup answers for; 27 min on 14 workers, 6.9 GB). With `Saturation.certified_opening` (closed under the global context) this makes "B does not lose from the A-first opening" a Rocq theorem, trusting only the extraction, the OCaml driver's enumeration of the lookup's domain, and the OCaml toolchain. |
| opening, **B first** | B-safe, B macro `blk,atk2,dmg`, every legal A move, `lmax` 100 | B Walker 10, tt 10, A huge > 10, ott 20 | **B safe with B life ≥ 14** (81.7M positions, the same 4.09M bases as A first; 5.0 min). Sound, so **A can't force a win from the B-first opening either.** Certificate check: all 90.8M entries pass (28 min); certified. |
| opening, B first | B-wins, macro B | B Walker 4, tt 12, A huge > 10 | **no B win** within these caps (19.3M positions, 6.1 h) |
| opening, B first | B-wins, B macro `blk,atk2,dmg`, A filtered | B Walker 4, tt 14, A huge > 14, ott 14 | **B wins with B life ≥ 17** (59.4M positions = 2.97M bases × 20, 4.4 min). B starts on 20, so this matches the folklore that the Elixir player wins going first. Not yet sound: A is filtered. |
| same | same, **every legal A move** (`TCB_FULLOPP=1`) | same | **B wins with B life ≥ 17** (122.7M positions = 6.13M bases × 20, 7.8 min, 5.3 GB). Sound: B's caps and macro only restrict B, A is unrestricted and saturation only adds losses for B. **B, going first, can force a win.** |
| same | **win certificate** (`TCB_RANKS=1`: rounds within each A-life level, every value change logged; `main.exe certify-win`, extracted `WinCert.check_win`) | same | **certified**: the 1.10M records B's strategy uses from the opening (1.51M states with Walker orders) all pass, 0 failures (pass 1 collects them, pass 2 re-checks with the lookup restricted to them; 12 min). The opening record has rank 19000017 (A on 20 life, round 17) and B on 17 life. With `WinCert.certified_win_opening` (closed under the global context) this makes `wins PB (init PB)` a Rocq theorem, trusting the extraction and the driver. |
| opening, A first | B-wins, B macro `blk,atk2,dmg`, A filtered | **B Walker 6**, tt 14, A huge > 14, ott 14 | **B wins with B life ≥ 25** (77.2M positions, 6.6 min): the same as with B's Walker capped at 4. |
| same | same | **B Walker 10**, tt 14, A huge > 14, ott 14 | **B wins with B life ≥ 25** (112M positions, 11 min). A bigger B Walker doesn't help B going second; with A filtered this is optimistic for B, so with every legal A move B needs at least as much. |
| opening, A first | B-wins, **every legal B move** (`TCB_FULLMINE=1`), A filtered | B Walker 4, tt 14, A huge > 14, ott 14 | **B wins with B life ≥ 25** (112M positions, 48 min): B's macro wasn't costing B anything. A is still filtered, which is optimistic for B, so B can't force a win from 20 within these caps. |
| same | B-wins, B macro `blk,atk2,dmg`, A filtered | B Walker 4, tt 14, **A huge > 20**, ott 14 | **B wins with B life ≥ 25** (87M positions = 4.35M bases × 20, 6.6 min). |
| same | same | **B Walker 6, tt 20, A huge > 20, ott 20** | **B wins with B life ≥ 24** (250M positions = 12.5M bases × 20, 78 min, 12 GB). The first change on B's side that moves B's threshold: more Thopters help B a little. Still above 20. |

¹ A active; A: life 10, one 3/3 Walker, 2 Thopters. B: life 6, one 1/1
Walker, 2 Thopters, Elixir in hand.

² A active; A: one 3/3 Walker, no Thopters. B: one 1/1 Walker, no Thopters,
Elixir in hand.

³ A active; A: 3/3 and 3/3, no Thopters. B: a 3/3, no Thopters, Elixir in
hand.

**What the A-first numbers say.** A's win stops at B life 15 whatever is
relaxed on A's side (caps, macro, filter, R4). Only B's filter is left, and
lifting it can only lower the value. B's win stops at 25 under every change
tried on B's side (caps 14 and 18, B's Walker capped at 4, 6 or 10, the
macro and `atk2`) except raising both Thopter caps to 20, which brings it to
24. So the real thresholds are very likely A wins iff B life ≤ 15 and B wins
iff B life ≥ 24 or so: from the real start, at B life 20, **neither player
can force a win**. To prove it, the safety checks must
reach 20: A-safe with B life ≥ 20 (so B can't win) and B-safe with B life
≤ 20 (so A can't). The B half is done and certified: B-safe at B Walker 10,
tt 10, with every legal A move, gives exactly 20. For A, capped Walkers and
Thopters make the check collapse onto the win check (A-safe = A-win = 15 at
6/6, 10/10 and 14/14), because a long game always reaches a cap and the cap
is a loss for the protagonist. This is the growth equilibrium described
below. (Resolved since: R7 removes A's cap, and with A allowed to keep
Thopters home, A-safe reaches exactly 20. See the last two sections.)

**B first is different.** With caps 14, B wins with B life ≥ 17 against
every legal A move, and the win is certified. The earlier "no B win" at tt
12, A huge > 10 was a cap artifact.

`TCB_LINE=N` prints a line of play from a solved B win. Values are computed
in synchronous rounds within each A-life level. B plays a move that keeps
its value as of the previous round, so every turn makes progress: either A's
life drops or the round count does. A plays a move that is worst for B.

A solved table is kept by solving with `TCB_SAVE=DIR`, plus `TCB_RANKS=1`
to keep the rounds a line needs. `main fixload DIR [N [BLIFE]]` reopens one,
prints the start value, and replays N turns. A table takes about 44 bytes
per position, plus 16 per value change with ranks. Tables live in `tables/`,
which git ignores. Old single-file tables are converted on first load, into
`FILE.d`.
`TCB_START=A` or `B` makes `fixload` look up that player's opening instead
of the saved start, if the table reached it.

A B win found this way is sound with no extra assumption beyond R3, R4 and
Thopter monotonicity. Every value comes from a finite strategy: a cycle
that gains B life only lowers the life B needs by looping a bounded number
of times before the winning line. B's own moves may come from the filter,
since it is the protagonist.

The failures are not caused by R4 (relaxing it does not rescue them). They
come from the protagonist's *own* caps (R3) and from `lmax`.

- **A-safe in the fortress.** B gains 5 life per Elixir cycle forever. A
  can only stay safe by threatening lethal, and the threat must grow with
  B's life. A capped Walker can't grow, so the abstraction loses even if the
  real game is a draw.
- **B-safe from the opening.** A's two Walkers can both grow without bound.
  B's defence (matching sizes, then trading or racing in the air) must grow
  with them, and B's Walker and Thopters are capped.

So any draw here is likely a *growth equilibrium*: each side stays safe by
keeping pace with the other's unbounded growth. No absolute cap can certify
that. What this suggests:

- **Symbolic (parametric) invariants.** The game depends on its numbers only
  through linear comparisons and sums: combat deaths, lethal checks,
  Thopters equal to counters, and +5 life. Within one *shape* (zones,
  tapped bits, which creatures exist), each turn line is a piecewise-linear
  condition on sizes, Thopter counts and lives. A safe set can then be
  described as a finite union of shape × linear-inequality cells. Its
  closure under one turn is a Presburger formula, which `lia` in Rocq or an
  SMT solver can decide.
- **Finding the cells.** Compute exact safe sets on growing windows. These
  need caps only on what the *opponent* can do inside the window, plus
  "leaving the window" counted as a loss. From those sets, read off the
  inequalities, for example "B's Walker ≥ A's largest − 1" or "B's life >
  A's largest Walker". Then check them symbolically.

## Why A-safe is the harder half

B's safety plausibly needs no exact sizes. B can chump a huge attacker
forever: each Elixir cycle of three rounds recasts B's Walker, which
gives three chump bodies for six mana. So caps on the opponent's sizes cost
B nothing. A has no recursion, so A can't chump forever. A's defence against
a big B Walker is deterrence: a B Walker that attacks is tapped for A's
counter-swing, and A's two Walkers outgrow it, at 2 counters a round against
B's 1. That argument is about *ratios*: B's life against A's Walker sizes, and
B's Walker against A's life and Thopters. Absolute caps (R4) make a huge B
Walker unanswerable, so A-safety in the R4 abstraction will fail even if the
real game is a draw.

Candidate reductions for A-safety:
- **Relative sizes.** Keep exact sizes up to a bound, and above it keep only
  each size's order and clamped difference against the others, like region
  abstraction for clocks. All life totals are at most 20 + 5k, and A's life
  is at most 20, so above about 25 counters an unblocked Walker is lethal to
  A and the remaining questions are comparisons and counts.
- **A parametric invariant.** Guess a region from the finite results, defined
  by linear inequalities over sizes, lives and Thopters (for example
  "a₁, a₂ ≥ b + 1 and B's life ≤ a₁ + a₂ + …"). Then prove its closure
  symbolically (in Rocq with `lia`) instead of by enumeration.

## A-safe diagnostics (2026-11-01)

To find what makes A-safe collapse, these runs relax the opponent's caps
(`TCB_LAX=dmg,die,many`): B's Walker silently stops at `ot + 1`, and B's
Thopters beyond `ott` are discarded. Each relaxation only takes options from
B, so it is optimistic for A. B's moves are also filtered (optimistic for A).
What stays pessimistic for A is A's own caps: Walkers at most `t`, Thopters
at most `tt`. All runs are A first, from the opening.

| A's moves | A Walker cap `t` | A Thopter cap `tt` | B Walker | B Thopters | A safe with |
|---|---|---|---|---|---|
| macro | 10 | 8 | ≤ 8 | ≤ 8 | B life ≤ 15 |
| macro | 6 | 8 | ≤ 6 | ≤ 8 | B life ≤ 13 |
| macro | 16 | 8 | ≤ 6 | ≤ 8 | B life ≤ 15 |
| macro | 24 | 8 | ≤ 6 | ≤ 8 | B life ≤ 16 |
| macro | 32 | 8 | ≤ 6 | ≤ 8 | B life ≤ 16 |
| macro | 64 | 8 | ≤ 6 | ≤ 8 | B life ≤ 16 (228M positions) |
| every legal move | 10 | 8 | ≤ 6 | ≤ 8 | B life ≤ 15 |
| macro | 10 | 4 | ≤ 6 | ≤ 4 | B life ≤ 19 |
| macro | 10 | 16 | ≤ 6 | ≤ 16 | B life ≤ 15 |
| macro | 24 | 24 | ≤ 6 | ≤ 8 | B life ≤ 16 |
| macro | 24 | 24 | ≤ 6 | ≤ 4 | B life ≤ 20 |
| macro | 24 | 12 | ≤ 4 | ≤ 6 | B life ≤ 19 |
| macro | 24 | 12 | ≤ 4 | ≤ 5 | B life ≤ 19 |
| macro | 24 | 12 | ≤ 6 | ≤ 6 | B life ≤ 16 |
| macro | 24 | 12 | ≤ 6 | ≤ 5 | B life ≤ 17 |

So a B held to a 6/6 Walker and at most 8 Thopters beats A from B life
16–17, whatever A's caps. Bigger A Walkers barely help (15 at `t` 10, 16 at
24, 32 and 64). What decides it is B's Thopter count: held to 4, B can't win
from 20.

The mirrored B-win (B Walker 6, B Thopters 8, A Walkers saturating silently
at 25, A's Thopters cut at 24, A filtered) gives **B wins with B life ≥ 18**
(95M positions). In its line, B banks life with Elixir (20 → 35) while A
grows, then trades its Walker into Thopters and races in the air.

This cuts against the draw hypothesis. The strict B-win probes above (B needs
24–25) count an A Walker past `ot` as a loss for B. That rule, not A's play,
may be what holds B back.

The B-win side, same B (Walker 6, Thopters 8, B's moves filtered), A first:

| A's moves | `ot` | `ott` | rules | B wins with |
|---|---|---|---|---|
| filtered | 24 | 24 | relaxed (`dmg,die,many`) | B life ≥ 18 |
| filtered | 24 | 24 | huge rules relaxed (`dmg,die`) | B life ≥ 18 |
| filtered | 24 | 24 | strict | B life ≥ 24 |
| every legal move | 24 | 24 | strict (sound) | B life ≥ 24 (218M positions, 22 min, 12 GB) |
| filtered | 24 | 12 | strict | B life ≥ 24 |
| filtered | 32 | 12 | strict | B life ≥ 24 |
| filtered, B Walker 6, B Thopters 6 | 40 | 8 | strict | B life ≥ 24 (84M positions, 5.5 min, 3 GB) |
| filtered, B Walker 6, B Thopters 6 | 64 | 8 | strict | B life ≥ 24 (176M positions, 9.3 min, 6.4 GB) |
| filtered, B Walker 9, B Thopters 9 | 32 | 8 | strict | B life ≥ 24 (140M positions, 11 min, 9 GB) |
| filtered, B Walker 12, B Thopters 12 | 32 | 8 | strict | B life ≥ 24 (269M positions, 49 min, 12.8 GB) |

The whole gap between 18 and 24 is the huge-Walker rule: in the strict check,
an A Walker past `ot` that attacks unblocked or fights a big block is a loss
for B. Raising `ot` from 24 to 32 doesn't move B's 24. So, for every cap, a
capped A loses from B life 16–18, but an A that may grow past the cap escapes.
Each side's strategy leans on how unbounded growth plays out (A's Walkers
against B's Elixir life), and no fixed cap settles A first in either direction.

The two results fit together in one of two ways, and these runs can't tell
which:

- **B wins.** B's life outgrows A's threats (Elixir banks 2.5 life a round;
  an A Walker grows 1 a round, and only while it doesn't attack), and the
  strict rule is too pessimistic: it makes B chump every huge attacker, even
  when B's life could take the hit.
- **A is safe by growing forever.** B's capped wins wait until A's Walkers hit
  their cap and stop growing. That would also make A's value flat in `t`, and
  it is the growth equilibrium described below.

What would tell them apart is how long B's capped wins take: a win that ends
before A could reach its cap doesn't depend on the cap.

A note on rates. With B's Walker and Thopters small, an A Walker bigger than
all of B's possible blockers together can never die, and its size matters only
for the damage it deals unblocked. So "A capped at `t`" loses for A only by
damage, and B's Elixir outpaces that: a cycle (activate for 2, recast for 1,
2 rounds) banks 5 life, 2.5 a round, while A's two Walkers together grow at
most 2 counters a round (City makes 2 mana). The strict B-win forbids exactly
this, since B must chump every huge attacker.

Raising B's life and an immortal A Walker together is *not* the same game: it
covers one unblocked hit, but every later hit costs B the Walker's full size.
So cutting such a Walker to K and charging B one life per counter cut is
unsound (tried: it would give B the win from 16, with every legal A move).
A sound treatment has to charge each hit its real size, which keeps the exact
size in the state.

**Growth is A's defence (against a small B).** The strict B-win is sound and
only forces B to chump A Walkers above `ot`; B may take any hit from a smaller
one. With A's Walkers exact up to 64, far above any life B banks in these
lines, B still needs 24. Against the same small B, an A capped at 24–64 loses
from 17. So B's capped wins come from A having to stop growing, not from B
outbanking a growing A. This supports the A-safe hypothesis. A proof has to
show that A can keep growing safely forever, against a B whose Walker and
Thopters may grow too: an argument over unbounded sizes, beyond any table.

`main fixstats TABLE` on that table (A's life 20, A with two Walkers): the
share of positions B can't win with any life grows with A's smaller Walker,
11% at 0–6, 17% at 7–12, 29% at 13–20, 45% at 21–32, 63% at 33–48. For A's
smaller Walker in 21–48 it is decided by B's material:

| B's Thopters + B's Walker | no B win at any life |
|---|---|
| up to about 3 | about 100% |
| about 5–6 | about half |
| 8 or more | about 1% |

So with A's Walkers large, B still wins once it holds about 8 between its
Walker and Thopters (given enough life; values reach lmax). In that table B is
capped at Walker 6 and Thopters 6, but in the real game B's Walker grows
without bound too. Whether A is safe therefore turns on a race between two
unbounded growths: B's material and life against A's Walker sizes and A's
pressure on B's mana (an A Walker attacking every turn forces B to spend
mana on chump blockers). That race is what a symbolic invariant has to
capture.

**Raising B's caps doesn't help B.** Strict B-win at `ot` 32, `ott` 8, with B's
Walker and Thopter caps raised together from 6 to 9 to 12, needs B life ≥ 24
each time (table above). Across every cap tried on either side (A's Walkers
24–64, A's Thopters 8–24, B's material 6–12), B's strict threshold is 24. If
B's material growth outran A's Walkers, larger B caps would lower it. They
don't, which is further evidence for the A-safe hypothesis. Reading B's
fixstats wins at 8+ material: those are positions where B already holds that
material against A's current Walkers, and B can't reach them from the start
while A keeps growing.

**The relaxed huge rules against A's cap.** Same B (Walker 6, Thopters 6,
`ott` 8, filtered), A first, with only the huge-Walker rules relaxed
(`TCB_LAX=dmg,die`: a huge A Walker hits for `ot + 1` and dies to `ot + 1`
damage), against the strict check:

| rules | `ot` | `lmax` | B wins with |
|---|---|---|---|
| relaxed | 24 | 100 | B life ≥ 18 |
| relaxed | 32 | 100 | B life ≥ 18 |
| relaxed | 40 | 100 | B life ≥ 24 |
| relaxed | 64 | 100 | B life ≥ 24 |
| relaxed | 40 | 200 | B life ≥ 18 |
| relaxed | 64 | 300 | B life ≥ 18 (28 min, 6.5 GB) |
| strict | 40 | 200 | B life ≥ 24 |

The jump at `ot` 40 is the life cap: positions where B needs more than `lmax`
count as no B win. Given room, the relaxed B wins from 18 again by banking
past 100 life. The strict check doesn't move with `lmax`. So B's relaxed win
needs both: life banked well past A's Walkers, *and* A's Walkers held to
`ot + 1` once they pass the cap. They do pass it while B banks, and B wins
only because the relaxation caps their hits. Whether B's banking (2.5 life a
round) outruns an A that never stops growing (2 counters a round between its
Walkers, less while attacking) is what the real game turns on, and no fixed
cap answers it: strict gives 24 and relaxed 18 at every cap tried.

`main win-reach DIR A LIFE` collects every record a ranked B win reaches
from the opening with A given all its (table) moves; `main win-line DIR A
LIFE N` prints one line (TCB_LAX=1 for tables solved relaxed, where A's
Walkers then keep their real sizes). On the relaxed `ot` 40, `lmax` 200
table, B's win from 18 reaches 7.39M records; in them A's Walkers reach the
clamp (41) and B needs up to 200 life, the cap itself. With `lmax` 100 the
opening needs 24, so A can force every B strategy to bank past 100 life,
which takes over 30 rounds of Elixir, and A's Walkers grow into the clamp
meanwhile. B's relaxed wins therefore wait out A's cap: against an A that
keeps growing, the relaxed rules give no evidence of a B win, and the strict
24 stands. This supports the A-safe hypothesis again. (A line where A only
grows, or only delays B's records, is short: B wins in about 25 rounds with
two Thopters in the air, so A's defence needs pressure as well as growth.)

**No capped certificate can show A safe.** The relaxed A-safe run with A
capped at 24 (B Walker ≤ 6, Thopters ≤ 6) gives A safe for B life ≤ 16 with
`lmax` 100 and again with `lmax` 300, so B's win there isn't banking past the
life cap. The relaxed B-win at `ot` is the same as capping A at `ot + 1` (a
pump beyond changes nothing it is compared against), and it gives B the win
from 18 at every `ot` tried up to 64. A bigger Walker is never worse for its
controller, so capping A is the only sound way to make A's side finite, and
every capped A loses to B from 17–18. If A first is a draw, it is a draw
because A's Walkers grow without bound: an A-safe proof has to argue about
unbounded sizes (a symbolic invariant), and no finite A-safe table or
certificate in the style of the B results can exist.

**A long stall in B's relaxed win.** `win-reach` also prints the chain of
records from the opening to the first one needing the most life. On the
relaxed `ot` 40 table (B from 18) it is 172 turn starts long. After an
opening skirmish, A is on 11 life with Walkers 4 and 11, and B holds a
6-counter Walker and Elixir. Then nobody attacks for about 70 rounds: B
banks 5 life per Elixir cycle (its life climbs from 20 to 200), and A grows
its bigger Walker from 11 to 40 (about 0.4 a round). The chain stops there
because 200 is `lmax`, the most any record can need, so it does not show
when or how B finally breaks the stall, or whether that needs A's clamp at
41. (The value "B needs" along the chain mostly follows B's own banked life:
more life lets B use an earlier, faster record.) What it does show is a
legal line where A's Walkers grow for 70 rounds while B banks, with no
fighting. If the real game is a draw, a stall like this, with A's fortress (a
small Walker and a big one that keeps growing, both at home) against B's
Walker, Elixir and banked life, is the natural target for the invariant.

**Stall positions, by value.** `main fixval TABLE ACTIVE ALIFE AW ATHOP AHAND
BW BTHOP BHAND ELIXIR` looks up one turn start (and, in a ranked table, its
(round, life) records). A on 11 life with Walkers 5 and `a`, B with a
Walker, Elixir on the battlefield, no Thopters, A to move:

- Relaxed, B Walker 6: B needs `a + 7`, the same at `ot` 40 and 64.
- The ranked `ot` 40 records for `a` = 11 show how: 75 life wins in 16 turn
  starts; 58 in 82; 57 needs 214, a wait of 132 turn starts; below that B
  banks 5 life every 4 turn starts and then waits. The wait shrinks as `a`
  nears the clamp (132 at `a` = 11, 80 at 20, 40 at 30): B is waiting for
  A's Walker to stop. Without the wait B needs about `5a + 3` (58, 103, 153
  at `a` = 11, 20, 30). So against a B Walker of 6, B's banking (2.5 a round)
  catches up only if A grows that Walker by less than half a counter a
  round.
- Strict `ot` 64 (sound for B), by A's big Walker (rows) and B's Walker
  (columns):

  | a \\ b | 1 | 2 | 3 | 4 | 5 | 6 |
  |---|---|---|---|---|---|---|
  | 6 | 28 | 22 | 12 | 10 | 18 | – |
  | 8 | 32 | 24 | 14 | 12 | 26 | 46 |
  | 10 | 36 | 26 | 16 | 14 | 35 | 56 |
  | 11 | 38 | 27 | 16 | 15 | 39 | 61 |
  | 12 | 40 | 28 | 16 | 15 | 43 | 66 |
  | 14 | 44 | 30 | 16 | 15 | 51 | 77 |
  | 16 | 47 | 31 | 17 | 15 | 59 | 88 |
  | 18 | 51 | 32 | 22 | 20 | 67 | – |

  (– : more than `lmax` 100.) A B Walker just under A's small Walker (3 or
  4 against 5) wins from 15–17 life almost whatever A's big Walker is, while
  5 or 6 makes the threshold climb about 4–5 per counter of A's. So the
  stall with B on 6 is a choice B makes when it has life to spare, not a
  forced shape. With A on 11 life, a small attacking B Walker beats A's
  fortress cheaply. An A-safe invariant would have to keep A's life high
  enough and cover thresholds that depend non-monotonically on B's Walker;
  no single linear inequality like "B's life ≤ 5 × A's Walker" will do.


**A parametric big Walker (`TCB_BIG=1`).** `rsolver fix safe A` with
`TCB_BIG=1` makes one A Walker unbounded. With K = `t` + 1 above every B
creature total ((`ot` + 1) + `ott`) and above 20, a pump from `t` makes a
Walker BIG: it is stored at K and stands for K + n counters, n ≥ 0 unknown.
Pumping it again keeps K (n → n + 1). A second Walker stays capped at `t`.
BIG can't die, and every comparison involving it comes out the same for all
n. Only unblocked damage to B depends on n. `TCB_BIGCHECK=1` (always on in
debug builds) checks this for every compiled BIG state against BIG + 3.

Values are lines (c, β): A is safe at B life L ≤ c + βn. The edges are exact:
- B's life changing by d gives c − d;
- an unblocked BIG adds 1 to β;
- a pump on BIG reads the child at n + 1, which gives (c + β, β);
- making BIG reads the child at n = 0, which gives β = 0.

The nodes are sound lower bounds:
- B's nodes take the componentwise min.
- A's nodes keep one child, the larger at n = `TCB_BIGREF` (default 20).
- B's death after damage is the line (−d, 1 if BIG hit), and the larger of it
  and the child at n = `TCB_BIGREF` is kept.

Turn starts clamp c ≤ `lmax` and β ≤ 8, and drop a line to "lost" if it is
below 1 and flat, or if c < −`lmax`. All of these only lower values. Each
evaluation keeps the componentwise min with the old line, so at stability
v ≤ F(v). The spot check confirms that against direct evaluation.

Results, A first, A macro, B filtered, strict R4 (no `TCB_LAX`), `lmax` 100:

| `t`/`tt`, B Walker cap `ot`, `ott` | BIG | A safe with | positions | time, peak RSS |
|---|---|---|---|---|
| 23/8, 14, 8 | yes (K = 24) | B life ≤ 15 (β = 0) | 95.0M | 4.8 min, 2.2–2.7 GB |
| 23/8, 14, 8 | no | B life ≤ 15 | 89.3M | 3.5 min, 2.3 GB |
| 29/8, 20, 8 | yes (K = 30) | not run: 8.8M bases, 2.4 GB of programs, over 3 GB | | |

The BIG Walker doesn't move the opening. It stays at 15 under each of these
changes:
- `TCB_BIGREF` 0 or 100;
- `lmax` 300;
- A pumping both Walkers at B's end step (`TCB_AMACRO=atk,order,dmg`);
- (unsound, optimistic for A) B's huge-Walker rules relaxed (`TCB_LAX=dmg,die`),
  B's Thopters cut at `ott` (`many`), or both.

So in this abstraction neither A's cap nor B's caps set the 15. At A life
20, 64% of the 283k BIG positions are lost. The share rises with B's material:
- B with no Walker: 22% lost;
- B Walker 14: 82%; B Walker huge: 84%;
- B with no Thopters: 37%; B with 8 Thopters: 81%.

Relaxing every B cap only lowers 64% to 58%. Of the BIG positions that
aren't lost, 70% have β = 0, and β never exceeds 6.

The likely limit is the line itself. A must choose one move for every n,
but A's real best play depends on n (attack once K + n beats B's life,
otherwise wait). The best value is then a max of lines, and a single line
can't represent it. On a small configuration (`t` 20, `tt` 4, `ot` 5, `ott` 6),
compare the BIG c at n = 0 with a scalar run capped at 28, which only
restricts A. At `TCB_BIGREF` 20, BIG is lower at 196k of 1.42M BIG positions
(54k of them lost only in BIG). At `TCB_BIGREF` 0, it is lower at 19k, by 1–4.
Choosing for large n gives up value at small n. A union of lines per position,
or an A choice that depends on n, would be the next step.

**The big Walker in the B win (`fix win B` with `TCB_BIG=1`).** The same
idea, mirrored, replaces the strict rule's huge events. A's first Walker past
`ot` becomes BIG at K = `ot` + 1 instead of saturating. K must exceed B's
largest total (`t` + `tt`: B's Walker and Thopters are capped as B is the
protagonist), so BIG never dies and every fight comes out the same for all n.
Its unblocked hit is an `F_HIT` edge, not a huge event.

Lines are upper bounds on the life B needs: B wins whenever L ≥ c + βn.
- A's nodes take the componentwise max.
- B's nodes keep one line, the smaller at n = `TCB_BIGREF`.
- After combat damage, B must also survive: componentwise max with
  (1 − d, 1 if BIG hit).
- Turn starts only raise: c below 1 goes to 1, and c > `lmax` or β > 8
  becomes "never".
- A new line replaces the old one only if it is smaller in B's choice order.
  A componentwise min of two B-win lines would not be an upper bound.

Soundness is by induction on time, not monotonicity. Every stored line was
computed from lines stored earlier, so each is a true B win with a finite
strategy. There are no ranks yet.

A second Walker reaching K counts as a loss for B (`F_SECOND`), which is
sound. Tracking two n's would need to tell the two BIG Walkers apart after the
Walkers are sorted. `TCB_LAX=second` (unsound) drops that A move instead, as a
diagnostic.

Cross-checks:
- **Against a sound A-safe table.** Both sides with every legal opponent
  move: B-win BIG at `t` 4, `tt` 4, `ot` 20 against A-safe BIG at `t` 20,
  B Walker ≤ 7, `ott` 8, both K = 21. Of 11.5M shared positions, every one
  where both are decided has B's line above A's for every n. That includes
  104k BIG positions with β ≠ 0. At 2.4M positions the gap is exactly 1.
- **Against the strict scalar B-win** (`ot` 13, same caps): no position
  contradicts the A-safe table either.
- **`TCB_BIGCHECK=1`** passes on the small configurations, and the debug build
  passes too.

Results, A first, B 6/6 with its moves filtered, `ott` 8, every legal A move
(`TCB_FULLOPP=1`), strict, `lmax` 100:

| `ot` (K) | rules | B wins with | positions | time, peak RSS |
|---|---|---|---|---|
| 20 | strict scalar | B life ≥ 24 | 77.0M | 3.2 min, 2.4 GB |
| 20 (21) | BIG | B life ≥ 24 (c 24, β 0) | 76.9M | 4.5 min, 2.5 GB |
| 24 (25) | BIG | B life ≥ 24 (c 24, β 0) | 101.2M | 5.8 min, 2.9 GB |
| 20 (21) | BIG, second BIG dropped (unsound) | B life ≥ 24 | | |
| 20 (21) | BIG, second BIG dropped and A's Thopters cut at `ott` (unsound) | B life ≥ 24 | | |
| 4/4 B, 13 (14) | strict scalar / BIG | B life ≥ 25 / ≥ 25 | 19.4M | |

So the strict 24 isn't the huge-Walker rule. Removing these doesn't move it:
- huge events for the first Walker (BIG);
- the second-BIG rule;
- the cap on A's Thopters (unsound in B's favour).

The relaxed 18 needed A's Walker to stop at its cap. Against an A whose
Walker grows without bound, B needs 24 within these caps. That is the
strongest evidence yet that B can't force a win from 20.

The BIG table does win more positions than the strict one: at A life 20,
3.23M of 3.85M bases are B wins against 3.02M. 886k positions need less or
go from never to a finite need (836k non-BIG, 50k BIG). It is worse at 166k
(141k non-BIG, 25k BIG).

Among the BIG positions where BIG never wins but strict does, A's other
Walker is mostly within 3 of K (172k of 179k over all levels). That is the
second-BIG rule, which is stricter than the strict rule's "a second huge
Walker saturates". Keeping a second huge Walker under the strict rules
(stored at K + 1) would fix those positions. It can't change the opening:
dropping the second BIG, which only helps B, gives 24. The worse non-BIG
positions read such positions, or lose to the single-line choice.

The rule fires on 187,831 edges in 6,369 compiled turns, 0.17% of the 3.85M
bases. The count is the same at `ot` 20 and 24: the states near two big
Walkers are the same up to the size label.

## Where the A-first gap comes from (`rsolver trace`)

A-safe stops at B life 15–16 and the B win at 24–25 under every single
change tried. `rsolver trace DIR A|B T TT LMAX STARTER L...` (with the
solve's `TCB_*` variables) follows a saved table's deciding play from the
opening at B life L and tallies the leaves by the rule that decided them.
- **A-safe table** (solved with `TCB_RANKS=1`): B's win against every A move.
  A turn lost in round r is followed only into turn starts of its level lost
  by round r − 1, or into lower levels, so every branch ends at a leaf. A
  child is traced at the least B life it was lost with by then.
- **B-win table**: A's escape against every B move, stopping at turn starts
  already seen. With `TCB_BIG=1` it keeps BIG's exact n and searches each
  turn per n, so an escape that only the line arithmetic gives shows up as
  "not confirmed".

Where the traced side has several good moves, it takes the one needing the
fewest abstraction rules in this turn, then the fastest win. A huge event in
which the protagonist dies anyway at the representative size counts as a
real death. `TCB_TRACE_PV=1` follows only the protagonist's best replies by
the table's own values. `TCB_CMP_DIR`/`TCB_CMP_CFG` compare an A-safe trace
with a B-win table, position by position. The trace only reads tables.

Small tables, A first, `lmax` 100:

| table | start | traced at | turn starts | leaves |
|---|---|---|---|---|
| A-safe, macro, `t` 12, `tt` 8, B huge > 10, `ott` 8 | A safe ≤ 15 | B life 16, every A move | 1.09M (all) | A dead 261k (in 164k turns); too_many 85k (21k turns); huge: unblocked 1.0k, huge attacker blocked by ≥ `ot`+1 2.6k, huge blocker 1.3k; lmax 0. A cap removed a pump at 102k A nodes |
| same | | B life 16, A's best replies | 261 | only A dead (141). No cap, no abstraction rule |
| B-win strict, B 4/4, A huge > 13, `ott` 8, every A move | B ≥ 25 | B life 20, every B move | 6.0M (cut off) | B dead 535k (267k turns); huge unblocked 657k (451k turns); lmax 16k |
| same | | B life 20–23, B's best replies | 4–20k | huge unblocked in 17–20% of turns; at 24 none |
| B-win BIG, same caps | B ≥ 25 | B life 24, every B move | 8.0M (cut off) | B dead 2.8M (1.4M turns); F_SECOND 22k (0.3%); no too_many, no lmax, no n bound. Every traced turn confirmed per n |
| same | | B life 20, 24, B's best replies | 150–220 | only B dead |

Example lines, ends only (B's life is the least it needs from there):
- A-safe, huge unblocked: B's Walker reaches 11 (`ot` + 1) and hits A from 18
  to 7. A survives the real hit, but the rule counts it as a loss.
- A-safe, too_many: A's 5 attacks, B blocks with its 1/1 and pumps it. The
  Walker dies, and B's Thopters go from 7 to 9.
- B-win strict, huge unblocked: A on 1 life, its Walker grown 10 → 14 one
  counter a turn. B Elixirs from 10 to 15, and A's 14 leaves B on 1. B
  survives the real hit, but the rule calls it a B loss.
- B-win BIG, F_SECOND: A on 4 life with Walkers 13 and K+0 pumps the 13.

**Comparing the two tables.** The B-win BIG table at B 4/4 against the
A-safe trace above: of the 1.09M traced turn starts, the B-win table agrees
B wins at 416k, says A escapes at 245k, and lacks 426k (B beyond 4/4).
There are 11,321 frontier turns: the B-win table disagrees there, but on
none of the traced children. At 9,033 of them a child is outside the B-win's
B caps. At the other 2,288, A escapes in the B-win table by attacking with
only some of its Thopters, which A's macro forbids.

**Targeted solves**, each matching one more rule between the two sides (B's
caps imposed on A-safe with `TCB_LAX=dmg,die,many`):

| A-safe variant | A safe with | B-win counterpart |
|---|---|---|
| B ≤ 4/4, A `t` 13 capped, `TCB_AMACRO=pump,order,dmg` | B life ≤ 20 | |
| same, A BIG (`t` 20) | ≤ 20 | |
| same, A BIG, every legal A move | ≤ 20 | BIG, B 4/4: B ≥ 25 (also with `TCB_LAX=second`) |
| B ≤ 4/4, A capped at 14, every legal A move | ≤ 20 | B 4/4, A silently capped at 14 (`TCB_LAX=dmg,die,many`): **B ≥ 21** |
| B ≤ 4/4, A BIG, **`TCB_LAX=adapt`** | **≤ 24** | BIG, B 4/4: B ≥ 25 |
| B ≤ 6/6, A BIG, `adapt` | **≤ 23** | BIG, B 6/6: B ≥ 24 |
| B ≤ 8/8, A BIG, `adapt` | ≤ 23 | |

`TCB_LAX=adapt` (new, unsound, A-safe BIG only) makes A's nodes take the
componentwise max of lines instead of one line. That is as if A could pick a
different move for every n, and it is optimistic for A.

**What binds: A-safe's treatment of A's growing Walker.**
- **The rule sets match.** With identical rules on both sides (B ≤ 4/4, A
  capped at 14, every legal A move), A-safe and B-win are complementary:
  20 and 21 at the opening. Position by position over all 19.4M, 0
  inconsistencies. 13.75M positions are exactly complementary. Every gap is
  at the lmax end: 257k positions where A is safe to 94–99 and B never wins,
  plus 28k gaps of 1–6.
- **Each solver reproduces the other.** Imposing B-win's caps on A-safe
  takes it from 15 to 20. A BIG Walker and every legal A move add nothing.
  Letting A choose per n closes the rest exactly: 24 against 25 at B 4/4,
  23 against 24 at B 6/6. More B material (8/8) doesn't lower it.
- **A-safe's abstraction holds A back.** In the capped A-safe, B wins
  honestly against A's best attacking lines (the best-reply trace has only
  real deaths). Against the lines where A keeps growing, it waits for A's cap
  (102k cap-stopped A nodes). BIG removes the cap, but A must still commit to
  one move for every n, and that costs as much.
- **The B win holds no matter how A's Walker is treated.** In the strict
  scalar table, A's escapes lean on the huge rule (a Walker of exactly
  `ot` + 1 is treated as unbounded). The BIG table gives the same 25 without
  that rule, and its escape is real: B dies or the game cycles, confirmed
  per n at every traced turn. Its only abstraction leaf is F_SECOND, and
  dropping that leaves 25.
- **B's caps and A's attack macro are a second, smaller difference.** On
  the main configurations, A-safe's B (Walker to 14, 8 Thopters) is stronger
  than B-win's 6/6, and A-safe's A macro is weaker. Neither moves a
  threshold here: B 8/8 gives 23 like 6/6 under `adapt`, and every legal A
  move gives 20 like the macro.

So within caps B ≤ 6–8, the A-first threshold is very likely "B wins iff B
life ≥ 24". A sound A-safe check needs A's choice to depend on n: a union of
lines per position, or a piecewise choice. The runs here show that this is
the missing piece, not B's caps or any R4 rule.

No sign of a solver bug: the traces found no stored value that the model
search failed to confirm (scalar or BIG), and the matched-rule pair is
complementary everywhere. One thing to know: **the BIG B-win table isn't
deterministic.** Two runs of the same B 4/4 BIG solve, with the same binary
from before this change, differ at 8,411 of 19.4M positions, and a third run
at 21,514. The start value is 25 each time. Its iteration keeps a new line
only if it is smaller in B's order, which isn't a lattice join, so which
sound fixed point it reaches depends on thread timing. Each table is still
sound by the induction-on-time argument above. Scalar tables, and the walk,
are byte-identical with the new binary.

## What holds the adapt A-safe at 19: A's Thopter-attack macro

With B's standard rules (no B caps imposed), the adapt A-safe gives 19, not
the 23–24 of the runs above. That held with B's R4 rules relaxed, with A's
Thopter cap at 8 or 14, and on a smaller configuration: A first,
`TCB_BIG=1 TCB_LAX=adapt TCB_MACRO=1 TCB_OT=10 TCB_OTT=8 fix safe A 20 8 100 A`
(K = 21; 60.0M positions = 3.0M bases × 20). The trace below is on that
configuration, at B life 20.

**Ranks for BIG tables.** `fix safe A` with `TCB_BIG=1` and `TCB_RANKS=1`
now solves in synchronous rounds and logs every line change. In `adapt` the
operator is monotone componentwise (`lmaxc`, `lmin`, `ltrans`, `norm_big`),
so the rounds reach the same fixed point as the worklist: the ranked table is
byte-identical (142M records, 3.5 min). `trace` follows B's win at the BIG
Walker's exact n: a turn start is lost at (L, n) when c + βn < L, its round
is the first logged line with c + βn < L, and each turn is searched per n, so
a win that only the line arithmetic gives shows up as "not confirmed".
`TCB_ROOT=HEX` starts a solve or trace from any turn start (`TCB_TRACE_KEYS=1`
prints the keys).

**The trace.**
- **A's best replies** (`TCB_TRACE_PV=1`): 33 turn starts, 21 turns deep,
  and two leaves, both real A deaths. No cap, R4 rule, clamp or line
  arithmetic is involved. It is a race. Both players cast both Walkers and B
  its Elixir. B's Walker grows to 3 and attacks every turn, while A swings
  with both of its Walkers (3 and 5), so neither side blocks much. B
  Elixirs every other turn (20 → 25, 22 → 24, 9 → 13 …). With A on 3 and
  B on 5, A's two Walkers attack, B blocks the 5 with its 3 and drops to
  1, and its Walker's 3 Thopters fly in for the last 3. B survives the
  race on exactly 1 life, which is why A is safe at 19.
- **Every A move**: complete, 3.08M turn starts, up to 259 turns deep,
  67 s, 2.2 GB.

  | leaf | leaf edges | turns with one |
  |---|---|---|
  | A dead (real) | 886,417 | 593,499 |
  | too_many (B Thopters > 8) | 512,750 | 185,102 |
  | huge: unblocked | 5,445 | 5,379 |
  | huge: huge attacker, blockers total `ot` + 1 | 43,576 | 10,916 |
  | huge: huge blocker | 43,702 | 31,563 |
  | lmax clamp | 1,828 | 1,828 |
  | not confirmed per n (all BIG) | | 10,663 |

  A's Walker cap removed a pump at **0** A nodes of the witness, so A's
  second Walker (capped at `t` while the first is BIG) never binds, and A's
  Thopters were cut to 8 on only 1,436 edges. The R4 leaves can be
  replaced: relaxing them leaves 19 (below). The unconfirmed turn starts
  (0.3%) are where `lmin` at B's nodes, or a clamp, gives B a win that the
  per-n search doesn't.

**Where the two tables part.** Against the strict B-win table with every
legal A move (B Walker 6, B Thopters 8, A huge > 24, `ott` 24; 24 at the
opening), the best-reply trace disagrees at 29 of its 33 turn starts. The
frontier is near the end of the race: B to play, A on 3 with Walkers 3 and
5 (tapped), B on 5 with a 3/3 and Elixir in its library. The A-safe table
says B wins there from 5, and the B-win table says B needs 9. Traced from
that position (`TCB_ROOT`) at B life 5:
- **A-safe** (every A move): complete, 35.6k turn starts, and every leaf is
  a real A death (21,154). Every turn start lies inside the B-win's caps.
  So B beats A's macro there honestly. Against the B-win table, 253 turn
  starts are a frontier, and 144 of them are explained by an escape move the
  A-safe A can't make: **attacking with some of its Thopters** (the other
  109 differ only in turns further on). In the first
  example, A's 3 trades with B's 3 (both get 3 Thopters), and later A is on
  1 with a 5/5 and 3 Thopters against B on 3 with a 2/2, one Thopter and
  Elixir. If A attacks with everything, B blocks a Thopter, Elixirs to
  survive, and its 2/2 kills A on the swing back, since every A creature is
  tapped. A's escape is to attack with the 5/5 and one Thopter (B blocks
  it, Elixirs and drops to 3) and keep two Thopters home to block the 2/2.
- **B-win** (every B move): A escapes over 1.42M turn starts. Its leaves are
  B dead (296k), A's Walker past 24 unblocked (50.5k) and lmax (11.3k), and
  B's Walker cap removed a pump at 54.8k B nodes.

**Targeted solves** (small configuration, A first, `lmax` 100):

| A-safe variant | A safe with | positions | time, peak RSS |
|---|---|---|---|
| `adapt`, A macro (`atk,pump,order,dmg`) | B life ≤ 19 | 60.0M | 2.6 min, 1.4 GB |
| same, B's R4 rules relaxed (`adapt,dmg,die,many`) | ≤ 19 | 60.6M | 3.5 min |
| same, `lmax` 200 | ≤ 19 | | 2.4 min |
| same, without A's pump rule (`atk,order,dmg`) | ≤ 19 | | 2.5 min |
| same, every legal A move | stopped: 9.0M bases, over 3.3 GB | 179M | |
| `adapt`, `TCB_AMACRO=atk1,pump,order,dmg` | **≤ 23** | 63.1M | 3.6 min, 1.6 GB |
| `adapt`, `atk2,pump,order,dmg` | **≤ 23** | 65.8M | 7.3 min, 1.8 GB |
| `adapt`, `pump,order,dmg` (any Thopter count) | **≤ 23** | 72.5M | 5.7 min, 2.6 GB |
| `adapt`, `atk2,…`, standard configuration (`t` 23, `ot` 14) | **≤ 23** | 103M | 6.8 min, 2.9 GB |
| **sound** (single line, `TCB_BIGREF` 20), `atk1,…` | ≤ 18 | 63.1M | 4.8 min, 1.6 GB |
| **sound**, `atk2,…` | **≤ 20** | 65.8M | 4.5 min, 1.8 GB |
| sound, `atk2,…`, B 6/6 (`ot` 6, `ott` 6) | **≤ 20** | 31.1M | 1.8 min, 0.7 GB |
| sound, `atk2,…`, B 6/6, **every legal B move** (`TCB_FULLOPP=1`) | **≤ 20** (also with `TCB_BIGCHECK=1`) | 44.9M | 3.9 min, 1.2 GB |

**The binding rule is A's macro `atk`:** A attacks with all of its Thopters
or none. Relaxing it to `atk1` (A may keep one Thopter home), `atk2`, or
dropping it moves the adapt start on the small configuration from 19 to 23,
and `atk2` does the same on the standard one. 23 is exactly
complementary to the B-win BIG's 24 at B 6/6: B wins from 24 and A is safe up
to 23. The earlier adapt runs (24 and 23 at B 4/4 to 8/8) come from the
`TCB_AMACRO=pump,order,dmg` line of the table above, so they most likely had
`atk` dropped too. That would be why they matched the B win and the standard
runs didn't. None of the other candidates moves the 19: A's
second-Walker cap is never used, and relaxing B's R4 rules, `lmax` 200 or
dropping A's pump rule each leave it. So B's Walker growing to 9–15 was a
red herring. With A allowed to hold Thopters back, B's Walker up to 10 (14
on the standard configuration) gives the same 23 as a B capped at 6.

**It is an abstraction artefact, not a strength of B's.** `atk` restricts A,
which is sound for A-safe but pessimistic. B's honest wins in the trace are
races that end with A trading Walkers into Thopters. A then needs to keep
some Thopters home to block while the rest attack, and the macro forbids
that. The B-win check, with every legal A move, finds exactly that escape.

**A sound A-safe at 20.** With `atk2` in place of `atk` (`atk1` gives 18
here: A's single-line choice needs the extra Thopter), the sound check
(single line per A node at `TCB_BIGREF` 20, strict R4, A capped at 20 with
one BIG Walker, A's Thopters cut at 8) already reaches B life 20, and so it
does with B's Walker capped at 6 and every legal B move. That is the first
A-safe value of 20 from the A-first opening that uses only sound rules. B
starts on 20, so B can't force a win, and with the certified B-safe (A can't
force a win) the A-first game is a draw. There is no margin: the value is
exactly 20.

## Status of the A-first draw proof

Done: `a_first_a_safe` and `a_first_draw` are proved in `Results.v`.

- **The checker and its soundness.** `CheckerA.v` and `SaturationA.v`
  (R7) prove, closed under the global context, that a line-valued table
  that passes the checker proves A safe. This covers the BIG abstraction and
  R4 with A as protagonist. Every legal B move is on, so R6 isn't needed.
- **The table.** Re-solved without the A-life bound (`TCB_NOBOUND=1`): the
  solver's `fin` bound copies a level's values from the level below by
  A-life monotonicity, which the checker can't use at an exact A life. The
  opening's line is still c = 20, b = 0.
- **The extracted check.** `main.exe certify-a` runs the extracted
  `CheckerA.check_node` from the opening's entry, with a memoised oracle
  choosing A's moves, and collects every entry it consults: 5,879,511
  entries, c in −16..100, b in 0..8. All of them pass, also with the lookup
  restricted to exactly that set. The first run found one place where the
  checker was stricter than the solver: after a pump on BIG, n is at least
  1, but lines were compared for every n ≥ 0. `check_node` now carries that
  lower bound `lo` (0 at an entry, +1 per pump on BIG, 0 on a new BIG) and
  compares lines for n ≥ lo.
- **In Rocq.** `certify-a-export` checks those entries once more as Rocq
  will (fuel 200) and writes `proofs/adraw`. `PackedA.v` reads the table:
  each column is cut into parts of 2^20 entries, because a primitive array
  holds at most about 4.2M.
- **A faster search.** Each entry is checked with `MemoA.check_m`, proved
  to imply `CheckerA.check_node` (`check_m_true`). It searches the same
  turn, with two changes. A tries its attacks in reverse order: the model
  lists the empty attack first and the attack with everything last, and
  the bigger attacks find A's safe line sooner. And it keeps a memo of
  the nodes it has searched, keyed by the state, the line and `lo`, so a
  position reached again by another order of moves is not searched twice.
  The memo is a search tree on a hash of the state (`Packed.shash`); a hit
  compares the whole state, so nothing is assumed about the hash. Rocq has
  no proved facts about updating primitive arrays (that would need more
  axioms), so the memo is a tree of inductive data. In OCaml this cuts the
  search from 462 nodes and 54 lookups per entry to 118 nodes and 7.5
  lookups.
- **B's life.** B's life in an entry's certificate state is any number that
  keeps B alive through the turn (`CheckerA.cert_safe` holds for every
  choice), and the checker's nats are unary in Rocq, so smaller is faster.
  Each entry stores its own (bits 20–26 of its `CV` value): the export
  searches the entry with B on 64 life, notes the least life B has at any
  node, and gives the entry 64 minus that plus 1. Entries with B to move
  need 1; entries with A to move need 2 to 42.
- **Cost.** Rocq takes about 3.7 CPU-hours over 128 chunks of 1.2–2.7
  minutes and 0.85 GB each, cut by the nodes and lookups of the
  extracted check (it was 15.5 CPU-hours, 4–10 minutes per chunk, with
  `check_node`, the attacks in order and B on 64 life).
- **The B-side tables** (`proofs/afirst`, `proofs/bfirst`) are checked the
  same way, with `MemoB.check_mb` and `MemoB.check_mw` (proved to imply
  `Checker.check_node` and `WinCert.check_win`). There B tries its moves in
  the model's order (reversing them doesn't help), and a node with a
  single move skips the memo, which costs more there than it saves. On
  samples this makes them 1.2–1.3 times faster; together they take about
  1.75 CPU-hours (it was about 2.5).
