(** * Basic facts about the game semantics

    The three results of [Game.has_result] are mutually exclusive. *)

From Stdlib Require Import List.
Import ListNotations.
From TCB.Spec Require Import Model Game.

Lemma opp_involutive : forall p, opp (opp p) = p.
Proof. destruct p; reflexivity. Qed.

Lemma opp_neq : forall p, opp p <> p.
Proof. destruct p; discriminate. Qed.

Lemma wins_not_safe : forall p s, wins p s -> safe (opp p) s -> False.
Proof.
  intros p s Hw [S [HS Hs]].
  induction Hw as [s Hwin | s m Hnone Hturn Hin Hw IH | s Hnone Hturn Hall IH].
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
  - intros Hnone Hturn. inversion Ht as [t' Hwin | t' m Hnone' Hturn' Hin Hm | t' Hnone' Hturn' Hall].
    + congruence.
    + exists m. auto.
    + exfalso. rewrite Hturn in Hturn'. symmetry in Hturn'. exact (opp_neq p Hturn').
  - intros Hnone Hturn m Hin. inversion Ht as [t' Hwin | t' m' Hnone' Hturn' Hin' Hm | t' Hnone' Hturn' Hall].
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
