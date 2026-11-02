(** * What this repository claims

    Read [Model.v] (the game: states, legal moves, and how moves change the
    state) and [Game.v] (what winning and not losing mean) first. This file
    states the results; [proofs/results/Results.v] proves each of them. *)

From Stdlib Require Import List Arith.
Import ListNotations.
From TCB.Spec Require Import Model Game.

(** Player A plays two Hangarback Walkers and City of Traitors; player B plays
    Hangarback Walker, Elixir of Immortality and City of Traitors. [init p] is
    the opening with player [p] taking the first turn. *)

(** The game never gets stuck: in every position without a winner, the
    player to move has a legal move. This holds for every state, so in
    particular for every state reached from [init] by legal moves. It is why
    [wins] and [safe] can quantify over [moves s] without checking that it is
    nonempty: an opponent can never escape a forced loss, or a safe player be
    left without a reply, because nobody can move. *)
Definition never_stuck : Prop := forall s, winner s = None -> moves s <> nil.

(** No legal move leaves the state as it was. Otherwise a player could
    repeat that move forever and stall into a draw the real game doesn't
    have. (Long games are still possible, for instance both players passing
    every turn; under rule F5 that is a draw, and each step of it is a real
    game action.) [step] on an illegal move returns its input, but nothing
    in [Game.v] applies [step] to an illegal move. *)
Definition no_idle_moves : Prop := forall s m, In m (moves s) -> step s m <> s.

(** Legal moves keep a state well formed (as type preservation goes with
    progress). A well-formed state holds each player's cards, no more and no
    fewer, and its combat only refers to Walkers and Thopters that exist.
    This keeps the default [0] of [nth] in [walker_power] out of play, and
    keeps the Thopter subtractions of [do_damage] from truncating at 0. *)

(** The cards of [p] being shuffled into [p]'s library (S9). *)
Definition shuffling (p : player) (s : state) : list card :=
  match s.(pend) with
  | ChooseShuffle _ q cards => if player_eqb q p then cards else []
  | _ => []
  end.

(** [p]'s Walkers and Elixirs, in hand, on the battlefield, in the graveyard
    and in the library. *)
Definition walker_count (p : player) (s : state) : nat :=
  let sd := get_side p s in
  sd.(hand_w) + length sd.(bf) + sd.(gy_w)
  + count_occ card_eq_dec (sd.(library) ++ shuffling p s) CWalker.

Definition elixir_count (p : player) (s : state) : nat :=
  let sd := get_side p s in
  Nat.b2n sd.(hand_e) + Nat.b2n sd.(elixir_bf)
  + count_occ card_eq_dec (sd.(library) ++ shuffling p s) CElixir.

(** No card is ever created or lost. *)
Definition cards_conserved (s : state) : Prop :=
  walker_count PA s = 2 /\ elixir_count PA s = 0 /\
  walker_count PB s = 1 /\ elixir_count PB s = 1.

(** During a shuffle, the shuffled cards are not also left in the library. *)
Definition shuffled_library_empty (s : state) : Prop :=
  forall st p cards, s.(pend) = ChooseShuffle st p cards -> (get_side p s).(library) = [].

(** The blocking Walkers (indices into the defender's [bf]) and Thopters. *)
Definition blocking_walkers (c : combat) : list nat :=
  flat_map (fun b => match b with BW i => [i] | BT => [] end) (concat c.(blk)).

Definition blocking_thopters (c : combat) : nat :=
  count_occ blocker_eq_dec (concat c.(blk)) BT.

(** The attacking Walkers are distinct Walkers of the active player, and
    each has one list of blockers. *)
Definition attackers_exist (s : state) : Prop :=
  NoDup s.(cmb).(atk) /\
  Forall (fun i => i < length (get_side s.(active) s).(bf)) s.(cmb).(atk) /\
  length s.(cmb).(blk) = length s.(cmb).(atk).

(** The blocking Walkers are distinct Walkers of the defender: none blocks twice. *)
Definition blockers_exist (s : state) : Prop :=
  NoDup (blocking_walkers s.(cmb)) /\
  Forall (fun i => i < length (get_side (defender s) s).(bf)) (blocking_walkers s.(cmb)).

(** The attacking Thopters are tapped Thopters of the active player, and
    those that trade with a blocking Thopter (S7) are among them. The
    Thopters blocking Walkers and those blocking Thopters (one per trade) are
    distinct untapped Thopters of the defender. *)
Definition thopters_exist (s : state) : Prop :=
  s.(cmb).(trades) <= s.(cmb).(atk_thop) <= (get_side s.(active) s).(thop_t) /\
  blocking_thopters s.(cmb) + s.(cmb).(trades) <= (get_side (defender s) s).(thop_u).

Definition well_formed (s : state) : Prop :=
  cards_conserved s /\ shuffled_library_empty s /\
  attackers_exist s /\ blockers_exist s /\ thopters_exist s.

(** The openings are well formed ... *)
Definition init_well_formed : Prop := forall p, well_formed (init p).

(** ... and every legal move keeps a state well formed, so every state
    reached by legal play is well formed. *)
Definition preservation : Prop :=
  forall s m, well_formed s -> In m (moves s) -> well_formed (step s m).

(** When B plays first, B can force a win. *)
Definition b_first_b_wins : Prop := wins PB (init PB).

(** When A plays first, B can avoid losing forever ... *)
Definition a_first_b_safe : Prop := safe PB (init PA).

(** ... so A has no winning strategy. *)
Definition a_first_a_cannot_win : Prop := ~ wins PA (init PA).
