# How B wins on the play (B first)

**Matchup.** A has Hangarback Walker x2 and City of Traitors. B has Hangarback Walker, Elixir of Immortality and City of Traitors. The rules are pre-Foundations and both players start at 20 life. Rocq proves that when B goes first, B can force a win. This note describes the strategy in the certified table (`tables/bwin-bfirst-14-full`) as it appears in sample games printed by `win-line`. I ran 27 lines: three A behaviours, with B starting on 17 to 40 life. I also ran one `win-reach` pass, which follows every A move.

## Facts that shape the game

- City untaps only on its owner's turn. B therefore gets **2 mana per round**, and can split it between its own turn and A's turn.
- Thopters fly, so **A's Walkers can never block B's Thopters**. Only A's own Thopters can.
- Elixir shuffles B's graveyard back in with it. **B's dead Walker comes back. A's dead Walkers stay dead.**
- The table needs **17 life** for B to win from the opening, so B starts with 3 to spare.

## B's game plan

**Opening.** In every line where B starts on 20 life, all three A behaviours get the same opening:

1. B's turn 1: cast Walker for X=1.
2. B's turn 2: pump the Walker to 2/2 and cast Elixir, which uses both mana. B doesn't attack.
3. B's turn 3: attack with the 2/2.

With 25 or more life, B sometimes attacks with the 1/1 on turn 2 instead of pumping.

**X=1, never X=0.** B cast its Walker 48 times across the lines, and every time for X=1.

**Elixir loop.** B activates Elixir on A's turn, using mana it saved on its own turn. B draws it again and recasts it for 1. That gives +5 life about every two rounds.

- Inference from the mana: a loop costs 3 mana, and B only gets 2 per round.
- If the Walker is in the graveyard, the shuffle also returns it. A always ordered the library Elixir-then-Walker, so B gets the Walker back one turn later and recasts it for X=1.
- B finishes every line on more life than it started with: 30 to 35 from a start of 20, and 23 to 55 across all the lines.

**Attacking.** B attacks with its Walker almost every turn, even into larger untapped Walkers.

- Unblocked, the Walker deals damage.
- Blocked, it dies and turns into Thopters that A's Walkers can't block.
- B's Walker stays small: 1 to 3 counters in the lines. The certified strategy is capped at 4, and `win-reach` shows it reaches 4.
- B pumps only on turns it doesn't attack, or on A's turn.

**Converting counters into Thopters.** In the lines, B's Walker becomes Thopters only by dying in combat, because A blocks it.

- A blocks with an equal Walker, or pumps a blocker to match: both die and each side gets Thopters. B then wins the air war. The likely reason (inference) is that the Elixir shuffle brings B's Walker back, while A's stay dead. In the default line, B recasts the Walker and attacks with it and 3 Thopters. A's 3 Thopters trade with B's 3, and the Walker gets through.
- A blocks with a bigger Walker: B's Walker dies, and its counters come back as Thopters that A has no way to block. In two endgames, B casts a fresh 1/1 and attacks into A's big Walker. A blocks, and the dead 1/1 leaves B one Thopter ahead of A. B then swings with all its Thopters, and one gets through after the trades.

**Blocking.** B had only one chance to block in all the lines, and its Walker was tapped then. B's life buffer from Elixir does the defending (inference).

## How B answers A's defences

- **A trades everything (default heuristic).** By turn 6 A has traded both Walkers for Thopters, and B has recycled its own Walker. B clears A's Thopters with an all-out attack, then deals 1 damage a turn with an unpumped 1/1 for 19 more turns, winning on its 28th turn. This slow finish is an artefact of how the solver picks moves (see caveats), not good Magic.
- **A grows its Walkers (TCB_AGROW).** A pumps both Walkers every turn, up to 8 to 13 counters. Because it pumps on its own turn, the Walkers are still tapped on B's turn. B's 2/2 or 3/3 attacks unblocked every turn, and B wins in 10 to 15 of its own turns before A's Walkers matter.
- **A holds back blockers (TCB_ANEED).** A keeps its Walkers untapped and pumps after B's combat. B attacks into them anyway. When A finally blocks, B's 3/3 becomes 3 Thopters, which finish A in the air (example below).
- **A racing.** The sample lines barely show this. A attacked once in all 27 lines: a 3/3 into B's tapped Walker. B took 3 and gained 5 from Elixir the same turn. What `win-reach` shows over every A move:
  - The strategy reaches 1.1M turn-start positions.
  - B never needs more than 27 life at any of them.
  - A's Walkers do reach 15+ counters in some of them. The certificate guarantees such a Walker never hits B unblocked and never dies.
  - The position needing the most life has A with one Walker of 10 counters.
  - How B handles a real racing A in detail isn't visible from these tools.

## How long it takes

- In the sample lines, B wins on its 10th to 28th turn, which is 19 to 55 turns in all.
- The ranks give a hard upper bound of 844 turn starts for any game under this strategy. That bound is loose.

## Example game (TCB_ANEED, both players on 20)

| Turn | What happens | A life | B life |
|---|---|---|---|
| B1 | B casts Walker for X=1 | 20 | 20 |
| A1 | A casts Walker for X=1 | 20 | 20 |
| B2 | B pumps its Walker to 2/2 and casts Elixir | 20 | 20 |
| A2 | A casts its second Walker for X=1 | 20 | 20 |
| B3 | B's 2/2 attacks, unblocked | 18 | 20 |
| B4 | B's 2/2 attacks, unblocked; after combat A pumps both Walkers to 2/2 | 16 | 20 |
| A4 | B activates Elixir; it is the only card shuffled in | 16 | 25 |
| B5 | B draws Elixir, pumps its Walker to 3/3 and recasts Elixir; A pumps both to 3/3 | 16 | 25 |
| B6 | B's 3/3 attacks into A's two untapped 3/3s; A doesn't block; A then pumps both to 4/4 | 13 | 25 |
| A6 | A pumps both Walkers to 5/5 (they stay tapped); B activates Elixir | 13 | 30 |
| B7 | B's 3/3 attacks, unblocked; B recasts Elixir | 10 | 30 |
| A7 | A pumps both to 6/6, tapped again | 10 | 30 |
| B8 | B's 3/3 attacks, unblocked | 7 | 30 |
| B9 | B's 3/3 attacks; A blocks with a 6/6; B's Walker dies and leaves 3 Thopters | 7 | 30 |
| B10 | B's 3 Thopters attack; A's 7/7s can't block fliers | 4 | 30 |
| B11 | B's 3 Thopters attack again | 1 | 30 |
| B12 | One Thopter attacks: B wins | 0 | 30 |

## Rules of thumb in the lines

1. Walker for X=1 on turn 1. On turn 2, grow it to 2/2 and cast Elixir.
2. Attack with the Walker every turn you can, whatever A has untapped.
3. Recycle Elixir about every two rounds, for the life and to bring a dead Walker back.
4. Keep the Walker small. Its job is to deal damage or become Thopters, not to win a size race.
5. In the air, trade Thopters 1-for-1. B's returning Walker supplies the extra body, and A has no way to replace its losses.

## Caveats

- These are sample lines from **one** certified strategy. Other winning strategies may exist.
- B's moves are chosen to reach the **earliest next record** in the table, not to win fastest or play naturally. Any damage to A counts as progress, which explains the 1-damage-a-turn finishes. B's choice also assumes A's heuristic reply, so B's play changes with A's mode and B's life.
- A's moves come from three simple heuristics: delay B, grow Walkers, or maximise the life B needs. None of them is A's best defence, and none of them really races. The proof covers every A move, but these lines show only a few.
- The table is a restricted model:
  - B's Walker is capped at 4 counters.
  - B's Thopters above 14 are discarded.
  - A's Walkers above 14 counters, and A's Thopters above 14, are treated pessimistically for B.

  These restrictions only make B's task harder, so the proof still stands.
