(** * Game semantics (RULES.md §2, 3CB rule F5)

    A player *wins* from a state if they can force the opponent to lose in
    finitely many moves. A player is *safe* from a state if they can avoid
    losing forever: there is a set of states containing it that the opponent
    can never force them out of. The game is a draw when both players are
    safe. *)

From Stdlib Require Import List.
Import ListNotations.
From TCB Require Import Model.

Lemma opp_involutive : forall p, opp (opp p) = p.
Proof. destruct p; reflexivity. Qed.

Lemma opp_neq : forall p, opp p <> p.
Proof. destruct p; discriminate. Qed.

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

(** ** Consistency: the three results are mutually exclusive *)

Lemma wins_not_safe : forall p s, wins p s -> safe (opp p) s -> False.
Proof.
  intros p s Hw [S [HS Hs]].
  induction Hw as [s Hwin | s m Hnone Hturn Hin Hw IH | s Hnone Hturn Hne Hall IH].
  - destruct (HS s Hs) as [Hnot _]. rewrite opp_involutive in Hnot. contradiction.
  - destruct (HS s Hs) as [_ [_ Hopp]].
    apply IH. apply Hopp; auto. rewrite opp_involutive. assumption.
  - destruct (HS s Hs) as [_ [Hmine _]].
    destruct (Hmine Hnone Hturn) as [m [Hin HSm]].
    exact (IH m Hin HSm).
Qed.

Lemma wins_winner : forall p s, wins p s -> winner s <> Some (opp p).
Proof.
  intros p s Hw. destruct Hw; rewrite ?H; try discriminate.
  intros Heq. injection Heq. apply not_eq_sym, opp_neq.
Qed.

Lemma wins_safe : forall p s, wins p s -> safe p s.
Proof.
  intros p s Hw. exists (wins p). split; [| exact Hw].
  intros t Ht. split; [apply wins_winner; exact Ht |]. split.
  - intros Hnone Hturn. inversion Ht as [t' Hwin | t' m Hnone' Hturn' Hin Hm | t' Hnone' Hturn' Hne Hall].
    + congruence.
    + exists m. auto.
    + exfalso. rewrite Hturn in Hturn'. symmetry in Hturn'. exact (opp_neq p Hturn').
  - intros Hnone Hturn m Hin. inversion Ht as [t' Hwin | t' m' Hnone' Hturn' Hin' Hm | t' Hnone' Hturn' Hne Hall].
    + congruence.
    + exfalso. rewrite Hturn in Hturn'. exact (opp_neq p Hturn').
    + auto.
Qed.

Theorem results_exclusive : forall r1 r2 s,
  has_result r1 s -> has_result r2 s -> r1 = r2.
Proof.
  intros [] [] s H1 H2; simpl in *; try reflexivity; exfalso.
  - apply (wins_not_safe PA s H1). apply wins_safe. exact H2.
  - exact (wins_not_safe PA s H1 (proj2 H2)).
  - apply (wins_not_safe PB s H1). apply wins_safe. exact H2.
  - exact (wins_not_safe PB s H1 (proj1 H2)).
  - exact (wins_not_safe PA s H2 (proj2 H1)).
  - exact (wins_not_safe PB s H2 (proj1 H1)).
Qed.

(** ** The statements this repository proves

    [Solution.v] proves [has_result] for the results listed there, for each
    starting player. *)

Definition solves (r_a_first r_b_first : result) : Prop :=
  has_result r_a_first (init PA) /\ has_result r_b_first (init PB).
