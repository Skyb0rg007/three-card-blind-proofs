(** * Determinacy (classical)

    Every position has exactly one result: with [Game.results_exclusive],
    a player who cannot force a win against a safe opponent leaves a draw.
    This file uses excluded middle; the certificate theorems do not depend
    on it. *)
From Stdlib Require Import List Classical Arith.
Import ListNotations.
From TCB.Spec Require Import Model Game.
From TCB.Proofs Require Import GameFacts.

(** Reachability games are determined: the complement of the opponent's
    attractor is a safe set. *)
Theorem determined : forall p s, wins (opp p) s \/ safe p s.
Proof.
  intros p s. destruct (classic (wins (opp p) s)) as [H | H]; [left; exact H | right].
  exists (fun s => ~ wins (opp p) s). split; [| exact H].
  intros t Ht. repeat split.
  - intros Hw. apply Ht. apply wins_over. exact Hw.
  - intros Hn Hturn. apply NNPP. intros Hno. apply Ht. apply wins_theirs; auto.
    + rewrite opp_involutive. exact Hturn.
    + intros m Hin. apply NNPP. intros Hm. apply Hno. exists m. auto.
  - intros Hn Hturn m Hin Hm. apply Ht. eapply wins_mine; eauto.
Qed.

Corollary results_exhaustive : forall s, exists r, has_result r s.
Proof.
  intros s. destruct (determined PB s) as [HA | HB]; [exists AWins; exact HA |].
  destruct (determined PA s) as [HB' | HA']; [exists BWins; exact HB' |].
  exists Draw. split; assumption.
Qed.
