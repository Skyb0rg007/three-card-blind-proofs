# How the three results are played

**Matchup.** A has Hangarback Walker x2 and City of Traitors. B has Hangarback Walker, Elixir of Immortality and City of Traitors. Both start on 20 life, under the rules in `spec/RULES.md`. Rocq proves three results:

| Opening | Result | Life the certificate needs | Table (Rocq data) |
|---|---|---|---|
| B first | B wins | B wins from 17 life or more | `bwin-bfirst-12-full` (`proofs/bfirst`) |
| A first | B is safe: A can't win | B safe from 20 or more | `bsafe-afirst-ot9` (`proofs/afirst`) |
| A first | A is safe: B can't win | A safe while B has 20 or less | `asafe-afirst-big-o5` (`proofs/adraw`) |

This note is for a Magic player who knows the cards but not Rocq. For each result it gives:

- a short rule strategy, and how far it agrees with the certified one, checked by machine;
- the key lines;
- what the numbers 17 and 20 measure.

None of it is used by the proofs.

## Facts that shape every game

- **City untaps only on its owner's turn.** Each player gets 2 mana a round, and can spend it on their own turn or keep it for the opponent's.
- **A pump costs {1},{T}.** A Walker that attacks can't grow the same round. A Walker grown on your own turn is still tapped on the opponent's turn. So both players grow on the opponent's turn, after the opponent's combat, keeping their Walkers untapped as blockers until then.
- **Thopters fly.** Walkers can't block them. Only Thopters block Thopters.
- **An Elixir cycle costs 3 mana** (1 to cast, 2 to activate) and gives 5 life. With 2 mana a round, and pumps wanting the same mana, B gains 5 about every 2 rounds. The shuffle also brings back B's dead Walker. A's dead Walkers stay dead.
- **A orders B's library after a shuffle.** In every line, and in A's rules below, A puts Elixir on top, so a dead B Walker comes back one draw later. The B certificates cover both orders.

## B's rules

B uses one rule set for both openings, with two changes when A goes first (marked "A first"):

1. **Main phase 2 of your turn.**
   - Walker in hand: cast it for X=1.
   - Otherwise, Elixir in hand: cast it.
   - Then spend any leftover mana on a pump, with the Walker at 4 counters at most.

   Do nothing in main phase 1.
2. **Attack.** Attack with every untapped Thopter. The Walker attacks too, unless Elixir is in hand. Then it stays home and is pumped in main phase 2.
   - *A first:* keep home the fewest Thopters that can chump-block A's biggest Walkers so that an all-out attack by everything A has is not lethal next turn. Count Elixir's 5 life if Elixir is on the battlefield.
3. **A's end step.** Activate Elixir if you can. Otherwise pump the Walker, up to 4 counters.
4. **Block.**
   - Your untapped Walker blocks A's biggest attacking Walker.
   - Your Thopters block A's attacking Thopters one for one.
   - While the damage still coming would kill you, a Thopter chump-blocks A's biggest unblocked Walker.
   - *A first:* when the attack is lethal, Thopters chump A's biggest Walkers first, and only the Thopters left trade with A's Thopters. After blocks, if the unblocked damage still kills you, activate Elixir.
5. **Everywhere else, pass.** That means no Elixir in your upkeep, no pumps before blocks and no tricks in combat.

In the solver (`solver/strat.ml`) these are the filters `bmain2+beot+bquiet+batk_he+bblock` for B first, and `bmain2+beot+bsave+bquiet+batk8+bblock2` for A first.

**Check against the certificates** (`strat-closure`, explained below). The opponent plays every legal move:

| Opening | Turn starts reached | B decision nodes | Rule's move certified | Rule leaves open | Exceptions |
|---|---|---|---|---|---|
| B first | 0.40M | 4.64M | 98.8% | 0.6% | 27,641 (0.60%) |
| A first (B safe) | 1.20M | 14.77M | 97.8% | 0.7% | 222,045 (1.50%) |

"Rule leaves open" counts nodes where the rule allows every move. Nearly always, every move is certified there. The rules are **not complete**: on their own they lose (see "How the rules were checked").

**A first.** The exceptions there:

- **Attack (97.9k).** 66.6k keep even more Thopters home than rule 2's count. 28.5k keep the Walker home, as a blocker, although Elixir is not in hand.
- **Main phase 2 (58.4k).** Mostly no pump with the leftover mana (49.7k), so the Walker stays untapped to block on A's turn. Some don't cast Elixir (7.8k).
- **Blocks (39.6k).** Chump A's Walker with a Thopter even when the attack isn't lethal, or don't block with the Walker into an equal or bigger attacker while B is healthy.
- **A's end step (13.7k).** Pump or pass instead of Elixir.
- **After blocks (7.6k).** Pump a blocking Walker.
- **B's upkeep (4.9k).** Elixir in the upkeep.

The A-first variants tried, all with A playing every move:

| Variant | Turn starts | Decision nodes | Exceptions |
|---|---|---|---|
| **The A-first rules above** | 1.20M | 14.77M | **222,045 (1.50%)** |
| Same, without the Elixir-in-combat rule and with B-first blocks | 1.19M | 14.67M | 263,754 (1.80%) |
| An earlier B-first version (pump before Elixir, no A-first changes) | 1.34M | 16.48M | 405,958 (2.46%) |
| No pump with leftover mana, B-first blocks | stopped at 1.3M | | over 208,000 |

**Where B's rules and the certificate disagree** (B first, 27,641 exceptions):

| Decision | Exceptions | What the certificate does instead |
|---|---|---|
| Attack | 19,077 | Mostly (15.9k) attacks with the Walker although Elixir is in hand. Typically A has no untapped Walker, or only a summoning-sick 1/1. Some (2.4k) keep one or two Thopters home late, as chump blockers. A few (0.7k) keep the Walker home. |
| Main phase 2 | 3,967 | Doesn't pump with the leftover mana (3.4k), or doesn't cast Elixir (0.6k), and keeps the mana for A's turn. |
| A's declare-blockers step | 1,669 | Activates Elixir in combat when the attack would be lethal (1.4k), or pumps the blocking Walker so it dies into one more Thopter (0.3k). |
| A's end step | 1,276 | Pumps (0.7k) or passes (0.6k) instead of activating Elixir. |
| B's upkeep | 1,173 | Activates Elixir in the upkeep when B's Walker is in the graveyard, so the Walker is redrawn sooner. |
| Blocks | 479 | Chump-blocks differently. |

Patching these one at a time made the total worse. Each patch sends the strategy into parts of the table it hadn't visited, which have exceptions of their own (B first):

| Variant | Turn starts | Decision nodes | Exceptions |
|---|---|---|---|
| **The rules above** | 0.40M | 4.64M | **27,641 (0.60%)** |
| Pump before casting Elixir, when the Walker and City are untapped | 0.44M | 5.15M | 36,611 (0.71%) |
| No pump with leftover mana in main phase 2 | stopped at 0.3M | | over 26,000 |
| A 1/1 stays home with Elixir in hand only if A has an untapped Walker; bigger Walkers always attack | stopped at 0.5M | | over 27,000 |
| Pump before Elixir, and: the Walker always attacks. Thopters keep home enough chump blockers that A's all-out attack isn't lethal. Elixir in the upkeep whenever the Walker is in the graveyard | 1.18M | not counted | 315,747 |
| Pump before Elixir, and: only a 1/1 stays home with Elixir in hand facing an untapped A Walker. Chump blockers kept home counting Elixir's 5 life. Elixir in combat when the attack is lethal | 1.06M | 17.1M | 208,203 (1.2%) |

## A's rules (A first)

1. **Your own turn.** Cast a Walker for X=1 in main phase 2 if one is in hand. Do nothing else on your turn: City's mana is for B's turn.
2. **Attack.**
   - If each of your untapped Walkers is bigger than B's Walker, or B has none, attack with all of them.
   - Otherwise, if B's Walker is tapped and you have two untapped Walkers, the bigger with 3+ counters, attack with the bigger. The smaller stays home to be pumped.
   - Otherwise no Walker attacks.

   Thopters always attack.
3. **Block.**
   - If B attacks with a Walker of 4+ counters, bigger than each of your untapped Walkers, block it with your smallest untapped Walker.
   - Otherwise no Walker blocks.
   - Thopters block B's attacking Thopters one for one.
4. **B's end step.** Pump your biggest untapped Walker if it is your biggest Walker or has fewer than 3 counters. In effect, both Walkers grow to 3/3, then only the biggest grows.
5. **After an Elixir shuffle,** put Elixir on top of B's library, the Walker under it.
6. **Everywhere else, pass.**

In the solver: `amain+apump3+ablk+aatk5+ashuf`.

**Check against the A-safe certificate** (`strat-closure asafe`, B plays every legal move). This closure did not finish. An unbounded run reached 3.3M turn starts with 174k still queued, and kept growing. The numbers below are at a checkpoint of a bounded run (`TCB_MAX_ENTRIES`), the first 0.70M turn starts in breadth-first order:

| Opening | Turn starts reached | A decision nodes | Exceptions |
|---|---|---|---|
| A first (A safe), partial | 0.70M of over 3.3M | 4.42M | 65,128 (1.47%) |

The exception rate is about the same as for B's A-first rules, and steady as the run grows (1.49% at 0.1M, 1.36% at 0.5M). Rule 5, A's library order, never fails. The rules are **not complete**.

Where the certificate does something else (68.7k exceptions logged by the time the run stopped):

- **Attack (30.2k).** Mostly (15.7k) the certificate keeps more Thopters home, as blockers against B's Thopters. In 11.1k it keeps home a Walker the rule sends, and in 3.4k it attacks with a Walker the rule keeps home.
- **Blocks (23.8k).** Mostly a Thopter chump-blocks B's attacking 4/4–6/6 Walker when A is low on life (1–13), where the rule takes the damage. Some (3.5k) block B's Walker with a Walker below the rule's 4-counter threshold.
- **B's end step (9.9k).** Pump where the rule passes (6.8k), often a Walker that is neither A's biggest nor under 3 counters, or pass where it pumps (3.1k).
- **After blocks on B's turn (4.8k).** Pump the Walker that is blocking B's Walker.

## How the rules were checked

Two checks, both in `solver/stratcheck.ml`.

**Against the certificate** (`main.exe strat-closure MODE RULE OUT`). This follows the check of the opening through the solver table, as the exports do.

- The opponent plays every legal move.
- At each of its own decisions, the protagonist plays the rule's move if the table certifies it: the move keeps B's life at or above the requirement, at a lower rank for the B-first win, or under A's line for A-safe.
- If the rule's move is not certified, the node is an **exception**. The protagonist then plays a certified move, so the check carries on.
- Real B life is tracked, as in the exports.

The tables give:

- **Turn starts reached**: the entries the rule strategy plus its exceptions needs.
- **Decision nodes**: distinct protagonist positions with two or more legal moves.
- **Exceptions**: distinct nodes where the rule's move is not certified but another move is.
- **Rule leaves open**: nodes where the rule allows every move. Nearly all of them are positions where every move is certified.

An exception is relative to the table. The rule's move may still win or hold in the real game, but these certificates can't show it. Each table is pessimistic for its protagonist at its caps, and the B-first table also asks for progress in rank.

**On its own** (`main.exe strat-fix MODE RULE DIR`). This solves the game (`Fix`) with B restricted to the rule everywhere, with no exceptions, under the certificates' caps. Both B rule sets get **"never"**, even against an A held to the solver's exploration filter (`TCB_AFILTER=1`):

- B first: 121k positions, 36 s, B's Walker capped at 4.
- A first: 73k positions, 15 s.

So within the caps each pure rule set loses to some A line. **No rule set here is complete.** Every one needs exceptions. There is no Fix for A's BIG Walker, so A's rules were only checked against the certificate, and only in part, since that closure did not finish.

## Key lines

### B first: the first four turns

These come from the certified strategy against an A that keeps its Walkers home as blockers (`win-line` with `TCB_ANEED`):

| Turn | B | A |
|---|---|---|
| 1 | Walker, X=1 | Walker, X=1 |
| 2 | Pump to 2/2, cast Elixir (both mana); no attack | Second Walker, X=1 |
| 3 | 2/2 attacks into two untapped 1/1s; A doesn't block (A on 18) | Nothing |
| 4 | 2/2 attacks again (A on 16); after combat A pumps both to 2/2 | B activates Elixir in A's end step (B on 25) |

From then on, B attacks every turn it can with a 2/2 or 3/3, even into bigger untapped Walkers. B activates Elixir in A's end step, then draws it, recasts it and pumps with the other mana.

- **If A blocks,** B's Walker dies into Thopters, which A's Walkers can't block, and the next Elixir shuffle brings the Walker back.
- **If A doesn't block,** A loses 2–3 life a turn.

In the certified line, A blocks for the first time on B's 9th turn with a 6/6. B's 3/3 becomes 3 Thopters, which finish A in the air.

The certificate's opening record has rank 19,000,017: A-life level 19 (A on 20) and round 17, so B forces the first point of damage within 17 turn starts. It needs B on 17 life, so B starts with 3 to spare.

### Why A can't race

- **A Walker can attack or grow in a round, not both.** An attacking A Walker is tapped through B's turn, so it can't be pumped there and can't block. A gets its two Walkers' damage only by giving up all of its growth and defence for that round.
- **B's life comes back.** Elixir gives B about 2.5 life a round for 3 mana. A has nothing that undoes damage, and A's dead Walkers don't come back.
- **Thopters are one-way.** When A's Walker blocks B's, B gets fliers that A can only answer with Thopters. When B's Walker blocks A's, B's Walker comes back with the next shuffle.

**A first, B safe.** The table's line (`fixload` on `bsafe-afirst-ot9`) shows A racing. A attacks with 6/6 and 4/4 every other turn from turn 14, for 10 damage a swing, while B's 4/4 hits back.

- B takes 4 + 10 + 10 + 10 = 34.
- B gains 15 from three Elixir activations.
- B ends on 20 + 15 − 34 = **1 life** and kills A on the next swing.

Without the Elixir, B would be dead by A's second big swing.

### Where the Elixir matters

**Without it, B has nothing** (`strat-fix MODE noel`). This forbids B to cast or activate Elixir, and leaves B every other move. It is checked under each certificate's own caps, and against an A held to the exploration filter, which can only help B:

- B first: "never", within the B-first caps (B's Walker at most 4). B can't force a win from any life up to 100 (10k positions, 2 s). With Elixir, B wins from 17 against every A move.
- A first: "never" for B-safe too (31k positions, 37 s). B can't stay safe from any life up to 100. With Elixir, B is safe from 20. This check counts an A Walker above 9 counters against B, and without the Elixir loop nothing stops A from growing one, so part of this result may come from that cap.

These are capped checks, not theorems. But they put the whole matchup on the Elixir. What it does:

- **Life.** In every racing line, Elixir supplies the margin: +15 in the A-first race above, about +5 every 2 rounds in the B-first lines. B finishes B-first lines on more life than it started with.
- **The Walker comes back.** A dead B Walker returns one draw after the next shuffle, and A orders the library Elixir first, Walker second. Every Walker trade costs A a Walker for good and costs B only time. In the A-safe line played with A's rules (`strat-pv asafe`), A pumps a 3/3 blocker to trade with B's 4/4. Both sides get 4 Thopters, and B redraws Elixir, then its Walker on the following turn, and recasts it as a 1/1.
- **Timing.** B activates in A's end step. The mana is B's own-turn City mana, saved by casting nothing in main phase 1, and the Elixir is back in hand at B's draw. The exceptions to rules 1 and 3 above are almost all about this timing: whether to pump first, or to save the activation for B's upkeep or for a combat on A's turn.
- **A first, A safe.** In A's certificate, B's life and A's line move together. Each activation raises both by 5, so the Elixir never opens a gap A can't close (see below).

## Invariants and potentials

### B first: what the ranks measure

A rank is `level · 1,000,000 + round`. So ranks compare A's life level first, then the round.

- `level` is A's life minus 1. Any damage to A is progress, whatever else happens.
- `round` is the sweep of the solver's least fixed point in which B first won from that position on that life. It bounds the number of turn starts before B either deals damage or wins.

B's move, and every A reply, leads to a turn start of strictly smaller rank that needs no more life than B has. So the game ends.

- The opening needs B on 17 at round 17.
- The largest round at an A-life level is 31 to 63, and 779 summed over the 20 levels. So no game under this strategy lasts more than about 800 turn starts.
- That bound is loose. Sample lines end in 19 to 55 turns.

The life a record needs is B's **potential**: along the strategy it never rises above B's real life. The Elixir pays for the damage A deals along the way.

### A first, A safe: the lines c + b·n

One of A's Walkers is treated as unbounded: a BIG Walker standing for K + n counters, for every n ≥ 0 (K = 21). Each table position stores a line (c, b): A is safe there while B has at most c + b·n life.

- **c** is B's life budget when the BIG Walker is exactly K.
- **b** is how much that budget grows per extra counter: each counter on the BIG Walker is one more damage on each of the b unblocked BIG hits A can still force.

In the opening, A has no BIG Walker yet, so the line is (20, 0): A is safe while B has at most 20.

In the principal variation (B always playing to leave A the least slack), the slack c + b·n − (B's life) stays exactly 0 every turn:

- each Elixir raises B's life and the line together;
- each A hit lowers both together.

A grows one big Walker after B's combat, attacks with the other while B's Walker is tapped, and swings with both at the end. B dies at exactly 0.

### Why the A-first game is a draw at exactly 20

Both certificates have **no margin**. B-safe needs exactly B life ≥ 20, and A-safe allows exactly B life ≤ 20, the starting life. The B-safe race above ends with B on exactly 1, and the A-safe line ends with B on exactly 0.

This tightness belongs to the certificates, not to the game. Each check is pessimistic for its own protagonist at its caps:

- **B-safe** caps B's Walker at 10 counters and B's Thopters at 10, and treats an A Walker above 9 counters ("huge") pessimistically for B. The value is exactly 20 under several nearby caps: A huge above 9 (the certified table) or above 10, A's Thopters cut at 14 or 20, B's Thopters at 8. With A huge above 8 it is "never".
- **A-safe** treats B's Walker above 6 counters pessimistically for A. It counts more than 5 B Thopters as a loss for A, and cuts A's Thopters at 8.

REDUCTION.md describes the uncapped thresholds. A's win stops at B life 15, and B's win starts at about 24, whatever is relaxed. So the real draw window is very likely B life 16–23. The proofs only needed to reach 20 from both sides, and each certificate uses caps just large enough to get there.

The lines show where the last point goes:

- In the B-safe race, B's 20 plus 15 from Elixir, against A's 34 damage, leaves exactly 1.
- In the A-safe lines, A's budget follows B's life point for point.

## The rules as a Rocq hint

The checkers take a `hint : state -> move -> bool`, and the protagonist only tries hinted moves (`MemoB.v`, `MemoA.v`).

- **A short rule set alone can't serve as the hint.** None is complete, so it would fail at its exceptions.
- **Rule plus exceptions would work in principle,** as `hint s m = rule allows m || s is an exception`. But that needs the exception positions in Rocq data.
- **The exported tables don't contain the rule strategy's turn starts.** The Rocq data hold the exporter's own closure, 0.57M positions for B first, not the rule's. A rule-driven export would be needed.
- **A weaker use is safe:** `hint s m = rule allows m || (s is of a kind the rule often gets wrong)`, for instance any position with Elixir on the battlefield, which falls back to all moves there.

I have not measured whether any of these compiles faster than the current hints. That is the other agent's work.

## What this note does not explain

- **Why the certificate deviates at most exception nodes.** Some deviations have a game reason:
  - Elixir in response to a lethal attack.
  - Pumping a doomed blocker for one more Thopter.
  - Elixir in the upkeep to redraw a dead Walker.

  Most have none I could find. Examples:
  - Passing instead of activating Elixir in A's end step on 19–23 life.
  - Pumping before Elixir on some turns and not on others.

  These probably come from the certificate itself. The B-first table must reach a strictly lower rank every turn with no more life. The other tables treat their caps as losses. A move the rules prefer may well be as good in the real game.
- **Whether a pure rule set wins or holds in the real game.** `strat-fix` says "never" for the pure B rules, but under caps that count against B: B's Walker at most 4, and A Walkers above 12 counted as huge. So it doesn't show the rules lose in uncapped Magic. I did not find the A line that beats them.
- **The real thresholds.** That A-first B wins from about 24 and A wins up to 15 is the solver's estimate, not a proof.
- **The b·n part of A's lines.** In every line I traced, A's Walkers stayed far below K = 21 (7–10 at most), so b stayed 0 and the BIG Walker was never in play. It matters only off these lines, where B lets A grow.
- **A's block threshold.** A blocks B's Walker once it reaches 4 counters. The A-safe table treats B's Walker above 6 pessimistically, so this threshold may come from the cap rather than from the game.
- **A's Thopter blocks.** Most of A's exceptions keep Thopters home, or chump B's Walker with one when A is low. The A-safe table counts more than 5 B Thopters as a loss for A, so some of this may also come from the cap.
- **The whole of A's rule strategy.** The A-safe closure grows past 3.3M turn starts without finishing, so the A numbers above cover only its first 0.70M.
