# Reducing the game to a finite one

Working hypothesis: **the game is a draw** for both starting players. A
depth-bounded search can never show this. A draw needs two separate facts:

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
  already tapped and can't pump.)
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
These arguments are written, not mechanized. Every B win that counts is
still re-solved with `TCB_FULLOPP=1`.

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
below.

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
