(** * Game semantics (RULES.md §2, 3CB rule F5)

    A player *wins* from a state if they can force the opponent to lose in
    finitely many moves. A player is *safe* from a state if they can avoid
    losing forever: there is a set of states containing it that the opponent
    can never force them out of. The game is a draw when both players are
    safe. *)

From Stdlib Require Import List.
Import ListNotations.
From TCB.Spec Require Import Model.

Inductive wins (p : player) : state -> Prop :=
| wins_over s :
    winner s = Some p -> wins p s
| wins_mine s m :
    winner s = None -> to_move s = p ->
    In m (moves s) -> wins p (step s m) -> wins p s
| wins_theirs s :
    winner s = None -> to_move s = opp p -> moves s <> [] ->
    (forall m, In m (moves s) -> wins p (step s m)) -> wins p s.

(** [S] is a set of states from which [p] never loses. *)
Definition safe_set (p : player) (S : state -> Prop) : Prop :=
  forall s, S s ->
    winner s <> Some (opp p) /\
    (winner s = None -> to_move s = p ->
       exists m, In m (moves s) /\ S (step s m)) /\
    (winner s = None -> to_move s = opp p ->
       forall m, In m (moves s) -> S (step s m)).

Definition safe (p : player) (s : state) : Prop :=
  exists S, safe_set p S /\ S s.

Inductive result := AWins | BWins | Draw.

Definition has_result (r : result) (s : state) : Prop :=
  match r with
  | AWins => wins PA s
  | BWins => wins PB s
  | Draw => safe PA s /\ safe PB s
  end.
