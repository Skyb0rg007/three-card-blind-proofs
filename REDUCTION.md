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

Monotonicity is proven in `theories/Mono.v`, for either player: `wins_bump`
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
  `theories/Mono.v` as `wins_thop` and `safe_thop`: if `t` matches `s`
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
- More than `tt` opposing Thopters counts as a loss for the protagonist.

## R5. A's life pinned at 20 (B-safe only, sound by monotonicity)

`TCB_FULLA=1` resets A's life to 20 at every turn start. For B-safety this is
pessimistic, since A's life is monotone good for A like B's is for B. It
removes A's life from the position (a factor of 20), and it is valid
whenever B's defence does not rely on threatening to kill A. The
monotonicity used here is `safe_bump` with `p = PA` (`theories/Mono.v`).

## R5b. Solving by A-life level (exact)

A never gains life, so a turn only ends in a position with the same or
lower A life. Positions are therefore solved one A-life level at a time,
lowest first. A level's turns are compiled, solved, and dropped before the
next level. The fixed point is unchanged; memory holds only one level's
compiled turns, plus a 63-bit digest, the state and a value for every
position. Digest collisions are ignored: for n positions they occur with
probability about n²/2⁶⁴, around 10⁻⁵ at ten million.

## R5c. Macro moves for the protagonist (sound by restriction)

`TCB_MACRO=1` restricts B, as protagonist, to `Reduce.b_macro`. For each
attacking Walker, B can block with nothing, its own Walker, one chump
Thopter, or enough Thopters to kill it. Thopter trades are all or nothing.
Restricting the protagonist is always sound. On the fortress it shrinks the
compiled turns 4.4× and gives the same result.

## R6. The exploration filter

Like the depth searches, `fix` currently uses `Reduce.moves`: timing
dominance that keeps pumps at end of turn or after blocks, Elixir in upkeep,
end step or after blocks, and X = 1. For the protagonist this is a
restriction, which is sound. For the opponent it must be justified by
dominance lemmas or replaced by `Rules.moves` before a certificate counts.
For the B wins in the results below it has been replaced: every one of them
was re-solved with `TCB_FULLOPP=1` (A gets every move in `Rules.moves`) and
came out the same, so they don't depend on R6. The dominance lemmas are
still open, and matter only for runs that keep the filter.

## Results so far

All results use `lmax = 60` and the exploration filter for the protagonist.
The spot check passes in every run.

| start | check | caps t/tt | result |
|---|---|---|---|
| fortress¹ | B-safe | 4/4 | **safe with any B life** (155k positions; also with `TCB_FULLOPP=1`, 229k) |
| fortress¹ | A-safe | 6/6 | not safe (508k); still not safe with every rule in R4 relaxed |
| opening, A first | B-safe, A's life pinned | 4/4 | not safe (75k); with every rule in R4 relaxed, B needs 34 life |
| opening, A first | B-safe | 4/4 | not safe (1.43M positions, 10 min) |

| lone-walker fortress² | B-wins (lfp) | B Walker 3, tt 10, A huge > 10 | A on 4 life: **B wins with any life** (161k; also with every legal A move, 207k) |
| same | B-wins | B Walker 3, tt 14, A huge > 12 | A on 8: **any life** (740k; every legal A move, 963k); A on 12: **B life ≥ 3** (1.3M; every legal A move, 1.72M) |

² A active; A: one 3/3 Walker, no Thopters. B: one 1/1 Walker, no Thopters,
Elixir in hand.

| two A Walkers³ | B-wins, macro B | B Walker 4, tt 10, A huge > 8 | A on 4 life: **B wins with B life ≥ 9** (1.23M; every legal A move, 2.32M) |
| opening, A first | B-wins, macro B | B Walker 4, tt 12, A huge > 10 | **no B win** within these caps (19.3M positions, 5.9 h) |

³ A active; A: 3/3 and 3/3, no Thopters. B: a 3/3, no Thopters, Elixir in
hand.

`TCB_LINE=N` prints a line of play from a solved B win. Values are computed
in synchronous rounds within each A-life level. B plays a move that keeps
its value as of the previous round, so every turn makes progress: either A's
life drops or the round count does. A plays a move that is worst for B.

Solved tables can be written to disk with `TCB_SAVE=FILE`, plus
`TCB_RANKS=1` to keep the rounds a line needs. `main fixload FILE [N [BLIFE]]`
reloads one, prints the start value, and replays N turns. Tables live in
`tables/`, which git ignores; they take about 40 bytes per position.

A B win found this way is sound with no extra assumption beyond R3, R4 and
Thopter monotonicity. Every value comes from a finite strategy: a cycle
that gains B life only lowers the life B needs by looping a bounded number
of times before the winning line. B's own moves may come from the filter,
since it is the protagonist.

¹ A active; A: life 10, one 3/3 Walker, 2 Thopters. B: life 6, one 1/1
Walker, 2 Thopters, Elixir in hand.

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
