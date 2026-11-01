(** * What this repository claims

    Read [Model.v] (the game: states, legal moves, and how moves change the
    state) and [Game.v] (what winning and not losing mean) first. This file
    states the results; [proofs/results/Results.v] proves each of them. *)

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

(** When B plays first, B can force a win. *)
Definition b_first_b_wins : Prop := wins PB (init PB).

(** When A plays first, B can avoid losing forever ... *)
Definition a_first_b_safe : Prop := safe PB (init PA).

(** ... so A has no winning strategy. *)
Definition a_first_a_cannot_win : Prop := ~ wins PA (init PA).
