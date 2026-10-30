# Rules specification

This document fixes the rules that the Rocq model implements and justifies
every place where the model is simpler than the full Magic rules. The model is
meant to be the *simplest correct* model: anything that cannot happen with
these six cards is omitted, and every simplification below comes with a
written argument that it does not change the outcome of the game.

Rule numbers refer to the pinned Comprehensive Rules (CR) below.

## 1. Sources

### 1.1 Comprehensive Rules

- **Pinned version:** *Magic: The Gathering Comprehensive Rules*, "effective
  as of July 30, 2024", published as
  `https://media.wizards.com/2024/downloads/MagicCompRules%2020240802.txt`,
  SHA-256 `072395073f9b79f840c36f458b0d35997787b741f2357cfe3dd8ed9f74c7884d`.
  `scripts/fetch-cr.sh` downloads and verifies it.
- This version still has **damage assignment order** (CR 509.2, 509.3,
  510.1c, 510.1d). The order was removed by the Foundations update, effective
  November 8, 2024 (`MagicCompRules 20241108.txt`, SHA-256
  `c5bf04bff59654d843d6897b9ee83c736af69b126a0fa96ad3f5efdf12b06096`).
- Diffing the two versions over every rule cited here (rules 100–122,
  302–307, 500–514, 601–605, 700–704, 702.9) shows that damage assignment
  order is the only relevant change. The other differences are renumbering
  and rules for cards that aren't in this matchup.

### 1.2 Oracle text

Retrieved from Scryfall on 2026-10-30.

| Card | Cost | Type | Text |
| --- | --- | --- | --- |
| Hangarback Walker | {X}{X} | Artifact Creature — Construct, 0/0 | This creature enters with X +1/+1 counters on it. When this creature dies, create a 1/1 colorless Thopter artifact creature token with flying for each +1/+1 counter on this creature. {1}, {T}: Put a +1/+1 counter on this creature. |
| City of Traitors | — | Land | When you play another land, sacrifice this land. {T}: Add {C}{C}. |
| Elixir of Immortality | {1} | Artifact | {2}, {T}: You gain 5 life. Shuffle this artifact and your graveyard into their owner's library. |

### 1.3 3-Card Blind format rules

From <https://www.3cardblind.com/format-info/rules>, retrieved 2026-10-30
(short quotes, paraphrased elsewhere):

- **F1 Starting state.** Each player starts with their three cards in hand,
  with no library and no sideboard. Players can't mulligan. Starting life is
  20 (CR 103.4).
- **F2 Decking.** Players "do not lose the game for drawing cards while they
  have no cards remaining in their library". This overrides CR 121.4. If
  cards end up in a library, they are drawn as normal.
- **F3 Randomness.** Random effects "resolve in whatever way would be most
  favorable to the opponent" of the card's owner. This includes shuffling
  libraries.
- **F4 Perfect information.** Decisions are made "assuming they have
  visibility to all cards at all times".
- **F5 Outcome.** Players only make decisions that lead to a win, or a draw if
  a win isn't possible. A draw is "a game state where no player has any action
  they can take that will result in a win". Players can't force a draw by
  deliberately looping an action to avoid passing the turn or priority.
  CR 104.4b (a mandatory loop is a draw) still applies.
- **F6 Matches.** Each matchup is played twice, once with each player going
  first.

## 2. The game

- **Players.** Player **A** has Hangarback Walker ×2 and City of Traitors.
  Player **B** has Hangarback Walker, Elixir of Immortality and City of
  Traitors.
- **Starting player.** A parameter of the model. That player skips the draw
  step of their first turn (CR 103.8a).
- **Outcome.** Defined by F5:
  - A player wins if they have a strategy that reduces the opponent to 0 or
    less life (CR 704.5a) after finitely many moves, whatever the opponent
    does.
  - If neither player has such a strategy, the game is a draw.
  - A play that never ends is a draw. A finite "draw by loop" can't happen,
    because every priority window ends after finitely many actions (§3.3).
- **Simultaneous loss.** Players can only lose life to combat damage from the
  active player's unblocked attackers. Both players can therefore never reach
  0 life at the same moment, and CR 104.4a never applies.

## 3. Model

### 3.1 Objects and state

Each player has:

- **Life:** an integer, starting at 20. It is only lowered by combat damage
  and only raised by Elixir.
- **City of Traitors:** on the battlefield, tapped or untapped (see S1).
- **Mana pool:** 0–2 colorless mana. It empties at the end of every step
  (CR 106.4, 500.4).
- **Walkers on the battlefield:** each has a number of +1/+1 counters, a
  tapped flag and a summoning-sickness flag. A's battlefield holds at most 2
  and B's at most 1.
- **Thopters:** counted by status (see S6):
  - untapped and able to attack;
  - untapped and summoning sick;
  - tapped.
- **Hand:** A holds 0–2 Walkers. B holds a subset of {Walker, Elixir}.
- **B's other zones:**
  - The library is an ordered list of cards. It is always visible (F4).
  - The graveyard is a multiset of cards.
  - Elixir can be on the battlefield. It is always untapped there, because
    activating it removes it (see S12).
- **A's graveyard** is a count of dead Walkers. A's library is always empty.
  Nothing ever reads either of them.

The global state holds:

- the active player;
- the current step;
- which player has priority, and whether the last action was a pass;
- whether this is the starting player's first turn;
- the combat state: attackers, blocks and damage assignment orders;
- a pending A decision, when a shuffle needs A to choose an order (see S9).

### 3.2 Turn structure

Each turn follows CR 500–514. The model includes every step in which players
get priority. In each of these steps, a *priority window* runs as described in
§3.3.

1. **Untap** (CR 502, no priority). The active player untaps their City,
   Walkers, thopters (and Elixir). Every creature they control stops being
   summoning sick, because it has now been under their control since their
   most recent turn began (CR 302.6). The model treats the turn-based actions
   of CR 502.1–2 as no-ops.
2. **Upkeep.** Priority window.
3. **Draw.** The active player draws the top card of their library, if there
   is one. No card is drawn if the library is empty (F2), or if this is the
   starting player's first turn (CR 103.8a). Then a priority window.
4. **Precombat main.** Priority window. The active player may also take
   sorcery-speed actions (§3.4).
5. **Beginning of combat.** Priority window.
6. **Declare attackers.** The active player chooses attackers (§3.5) and taps
   them (CR 508.1f). Then a priority window. If there are no attackers, skip
   to step 9 (CR 508.8).
7. **Declare blockers.** The defending player chooses blocks. Then the active
   player announces the damage assignment order for each attacker blocked by
   two or more creatures (CR 509.2). CR 509.3 is always trivial here, because
   every blocker blocks exactly one attacker. Then a priority window.
8. **Combat damage.** Damage is assigned and dealt (§3.6). Then state-based
   actions and Walker death triggers are handled (§3.7), followed by a
   priority window.
9. **End of combat.** Priority window. Afterwards, everything is removed from
   combat (CR 511.3).
10. **Postcombat main.** The same as step 4.
11. **End.** Priority window.
12. **Cleanup.** No priority (see S8, S11). The turn passes to the other
    player.

### 3.3 Priority windows

- **Who acts.** The active player receives priority first (CR 117.3a).
- **Possible actions.** The player with priority may take one action from
  §3.4 and receive priority again (CR 117.3c), or pass.
- **Passing.** On a pass, the other player receives priority (CR 117.3d).
- **Ending the window.** The window ends when both players pass in succession
  (CR 117.4, 500.2). There is no stack: every action resolves as soon as it is
  taken (S3).
- **Termination.** Every action uses up something finite: a tapped permanent,
  a card from hand, or a land drop. Windows therefore always end. Holding
  priority forever without acting is the loop F5 forbids, and the model has no
  such move.

### 3.4 Actions

These are all the actions available to the player with priority.

**Paying costs.** Generic mana is paid from the pool. If the pool is short,
City is tapped for {C}{C} as part of paying (a mana ability, CR 605). An
action whose cost can't be paid is illegal.

Instant speed, in any priority window:

- **Pump:** `{1},{T}` on one of your Walkers. The Walker must be untapped and
  not summoning sick (CR 302.6, 602.5a). Put a +1/+1 counter on it.
- **Activate Elixir (B only):** `{2},{T}` on Elixir.
  - B gains 5 life.
  - B's library, Elixir and B's graveyard are combined.
  - **A chooses the order of the combined library** (F3, S9).
  - B's graveyard becomes empty.

Sorcery speed, active player only, during a main phase:

- **Cast Walker for X:** costs `2X` and needs X ∈ {0, 1} (see S5).
  - It enters with X counters and is summoning sick.
  - With X = 0 it dies straight away (CR 704.5f). It goes to the graveyard
    without making any thopters.
- **Cast Elixir (B only):** costs `{1}`. Elixir enters untapped. It isn't a
  creature, so summoning sickness doesn't apply and it could be activated the
  same turn if B could pay for it. B can't, because only `{C}` is left in the
  pool after casting it.

Playing City of Traitors isn't an action in the model; see S1.

### 3.5 Attacking and blocking

- **Who can attack.** Attackers are any of the active player's untapped
  creatures that aren't summoning sick (CR 508.1a): Walkers and thopters. They
  all attack the defending player.
- **Who can block.** Blockers are any of the defending player's untapped
  creatures (CR 509.1a). Each one blocks exactly one attacker.
  - Thopters (flying) can block anything.
  - Walkers can't block thopters (CR 702.9b).
- **Multi-blocked thopters.** A thopter blocked by more than one thopter is
  modelled as blocked by exactly one (S7).
- **Attackers after combat.** Attacking creatures remain tapped. They can't be
  pumped later in the turn, and they can't block during the opponent's next
  turn, because they only untap during their controller's next untap step.
- **Blockers after blocks.** Blocking doesn't tap. A blocking Walker can be
  pumped after blocks are declared and stays a blocker: tapping doesn't
  remove a creature from combat (CR 506.4). It still deals and receives
  combat damage (CR 510.1a).

### 3.6 Combat damage (pre-Foundations rules)

- **Power and toughness.** A creature's power and toughness are read at the
  moment damage is assigned. This includes pumps made after blocks.
  - A Walker with n counters is n/n.
  - A thopter is 1/1.
  - There are no other damage sources, so creatures never have damage marked
    on them from earlier in the turn. Lethal damage for a creature is
    therefore its toughness.
- **Unblocked attacker:** deals damage equal to its power to the defending
  player.
- **Attacker blocked by one creature:** deals all its damage to that creature.
- **Attacker blocked by blockers b₁, …, bₖ (k ≥ 2), in the announced order:**
  the active player assigns all P damage following CR 510.1c. This allows
  exactly the following sets of killed blockers:
  - Let `jmax` be the largest j with `t(b₁) + … + t(bⱼ) ≤ P`.
  - If `P < t(b₁)`, nothing dies: all damage must go on b₁ without killing it.
  - Otherwise the killed set is the prefix `b₁…bⱼ` for some chosen
    `1 ≤ j ≤ jmax`.
  - **Why these are all the options.** Damage can't go to bᵢ₊₁ until every
    earlier creature has lethal damage, so the killed set is always a prefix.
    Any prefix up to `jmax` can be killed by giving each member lethal damage
    and putting the leftover on b₁. If `P ≥ t(b₁)`, b₁ always dies, because
    all damage then goes to b₁ unless b₁ is already getting lethal damage.
  - The choice matters: killing an opposing Walker gives its owner thopters,
    so the attacker may prefer to kill fewer blockers.
- **Each blocker:** deals its power to the one attacker it blocks. An attacker
  dies if the total damage dealt to it is at least its toughness.
- **Comparison mode (post-Foundations, for the check in PLAN.md only).** The
  attacker divides damage freely (current CR 510.1c):
  - Any non-empty set S of blockers can be the killed set if the toughness of
    S adds up to at most P.
  - The empty set can be the killed set if P is at most the sum of
    `t(bᵢ) − 1` over all the blockers.

### 3.7 After damage

- **Life.** A player with 0 or less life loses (CR 704.5a).
- **Death.** Every creature with lethal damage dies (CR 704.5g).
- **Dead thopters** cease to exist (CR 704.5d).
- **Dead Walkers** go to their owner's graveyard. Their death trigger makes
  one thopter per counter for the Walker's controller, using last known
  information (CR 603.10a, 608.2h).
  - The new thopters are untapped and summoning sick. They aren't in combat.
  - They can block straight away. They can attack once their controller's
    next turn has begun.
- **Leftover damage** on creatures that survive is dropped (see S8).

## 4. Simplifications and their justifications

**S1 City is on the battlefield, untapped, from its controller's first turn
onward.**

- In the real game City is played in the first main phase of that turn.
- Before that main phase, its controller has nothing to spend mana on:
  - no permanent with an activated ability is on the battlefield;
  - no instant-speed card is in hand.
- City's sacrifice trigger needs another land to be played, and neither deck
  has one.
- Nothing in either deck interacts with lands. Having City on the battlefield
  only adds options compared with keeping it in hand, so playing it on turn 1
  is never worse.

**S2 Only the cards and zones listed in §3.1 exist.**

- Exile, the command zone and other zones are never used.
- A's library stays empty, and nothing reads A's graveyard.
- Hand size is at most 3, so the cleanup discard (CR 514.1) never happens.

**S3 No stack: every spell and ability resolves as soon as it is cast or
activated.**

- In the real game an opponent may respond. In the model they act after the
  resolution instead.
- These are all the objects that can go on the stack:
  - Walker spell;
  - Elixir spell;
  - pump ability;
  - Elixir ability;
  - Walker death trigger.
- None of them targets anything, counters anything, or reads the stack.
- **The effects commute.** Each pump touches one Walker. The Elixir ability
  only touches B's life, library, graveyard and Elixir. Spells only add a
  permanent. Death triggers only add thopters, and the number is fixed by
  last known information. Applying any two of them in either order gives the
  same result.
- **Legality doesn't depend on what is on the stack.** Costs such as tapping
  and mana are paid when the action is taken, in the real game as well as in
  the model. Sorcery-speed actions need an empty stack, and in the model the
  stack is always empty.
- **The only thing that could add to B's graveyard while an Elixir ability is
  on the stack** is casting a Walker for X=0. That is sorcery speed, so it
  can't happen then.
- **Neither player loses an option.** In both the real game and the model, a
  window only ends after both players pass in succession. Any action can
  therefore always be followed by any other legal action from either player.
- Together, these mean any order of actions with responses reaches the same
  state as taking the same actions one after another in the model.

**S4 City is only tapped while paying a cost.**

- Tapping City for nothing just loses the mana when the step ends (CR 500.4).
- An untapped City offers a superset of the options of a tapped City, and
  nothing else in the game looks at City.

**S5 Walkers are only cast for X ∈ {0, 1}.**

- City is the only mana source. It can be tapped once per untap, so the pool
  never holds more than 2 mana.
- Mana doesn't carry over between steps, so a cost of `2X` needs `X ≤ 1`.

**S6 Thopters are counted by status, not tracked individually.**

- Thopter tokens all have the same characteristics.
- Two thopters with the same status (tapped, summoning sick, in combat) are
  interchangeable for every rule and every action.

**S7 A thopter blocked by several thopters is treated as blocked by one.**

- The attacking thopter has 1 power. It must assign that damage to the first
  creature in its damage assignment order, which then dies (CR 510.1c).
- It takes at least 1 damage, so it dies too.
- The extra blockers neither deal nor take damage that changes anything.
  Blocking doesn't tap them, and thopters have no abilities that could act
  after blocks.
- The result is therefore identical to a single block. Walkers can't block
  thopters at all.

**S8 Marked damage is dropped after combat damage.**

- Combat damage is the only damage in the game, and it happens at most once
  per turn (there is no first strike).
- Marked damage is removed during cleanup anyway (CR 514.2).
- Pumps only raise toughness, so a creature that survived combat damage
  can't later die from it.

**S9 The order of B's library is chosen by A when Elixir's ability
resolves.**

- F3 says a shuffle resolves in the way most favorable to the opponent. That
  makes the shuffle an A decision.
- The model fixes the order at the moment of the shuffle, because that is
  when the randomness happens. A can't wait to see B's later actions before
  choosing.
- The library holds at most two cards, and all cards are visible (F4).

**S10 Decking never matters.**

- Drawing from an empty library does nothing (F2).
- A never has a library.

**S11 Cleanup never gives priority.**

- Priority is only given in cleanup if a state-based action or trigger
  happens there (CR 514.3a).
- Nothing can die or trigger during cleanup, because no creature has 0 or
  less toughness and damage is removed there.

**S12 Elixir is never tapped while on the battlefield.**

- Its only `{T}` ability shuffles it into the library as part of the same
  resolution.

## 5. Interpretation points (decided)

1. **When the shuffle order is chosen (S9).** At the shuffle, not lazily at
   each draw. A lazy choice would give A information it couldn't have from a
   real shuffle.
2. **Pre-Foundations damage assignment order** is authoritative. The solver
   also runs the comparison mode in §3.6. Any difference in the result will be
   reported, but it doesn't change the authoritative answer.
