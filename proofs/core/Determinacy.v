(** * Determinacy (classical)

    Every position has exactly one result: with [Game.results_exclusive],
    a player who cannot force a win against a safe opponent leaves a draw.
    This file uses excluded middle; the certificate theorems do not depend
    on it. [moves_ne] (every unfinished position has a move) is also what
    makes [wins_theirs] apply to every opponent node. *)
From Stdlib Require Import List Classical Arith.
Import ListNotations.
From TCB.Spec Require Import Model Game.
From TCB.Proofs Require Import GameFacts.

Lemma flat_map_ne : forall {A B} (f : A -> list B) l x,
  In x l -> f x <> [] -> flat_map f l <> [].
Proof.
  intros A B f l x Hin Hf Heq. destruct (f x) as [| y ys] eqn:E; [contradiction |].
  assert (In y (flat_map f l)) by (apply in_flat_map; exists x; rewrite E; auto with datatypes).
  rewrite Heq in H. contradiction.
Qed.

Lemma map_ne : forall {A B} (f : A -> B) l, l <> [] -> map f l <> [].
Proof. intros A B f [|]; cbn; congruence. Qed.

Lemma product_ne : forall {A} (cs : list (list A)), (forall c, In c cs -> c <> []) -> product cs <> [].
Proof.
  intros A cs. induction cs as [| c cs IH]; intros Hc; cbn; [discriminate |].
  destruct c as [| x xs] eqn:E; [exfalso; apply (Hc []); auto with datatypes |].
  apply flat_map_ne with x; [auto with datatypes |]. apply map_ne. apply IH. auto with datatypes.
Qed.

Lemma bounded_vectors_ne : forall n t, bounded_vectors n t <> [].
Proof.
  induction n; intros t; cbn; [discriminate |].
  intros E. apply app_eq_nil in E as [E _]. revert E. apply map_ne, IHn.
Qed.

Lemma subsets_nil : forall l, In [] (subsets l).
Proof. induction l; cbn; auto with datatypes. Qed.

Lemma orders_ne : forall {A} dec f (l : list A), orders_fuel dec f l <> [].
Proof.
  intros A dec f. induction f as [| f IH]; intros l; [cbn; discriminate |].
  destruct l as [| y r]; [cbn; discriminate |]. cbn [orders_fuel].
  apply flat_map_ne with y; [apply nodup_In; left; reflexivity | apply map_ne, IH].
Qed.

Lemma kill_choices_ne : forall p ts, kill_choices p ts <> [].
Proof.
  intros p [| t ts]; unfold kill_choices; [discriminate |].
  destruct (p <? t) eqn:E1; [discriminate |]. apply Nat.ltb_ge in E1.
  cbn [max_prefix]. destruct (t <=? p) eqn:E2; [cbn; discriminate |].
  apply Nat.leb_gt in E2. exfalso. apply (Nat.lt_irrefl p). eapply Nat.lt_le_trans; eauto.
Qed.

Lemma moves_ne : forall s, winner s = None -> moves s <> [].
Proof.
  intros [act ft a b c pd] Hw. unfold moves, moves_gen.
  destruct pd; cbn [Model.pend].
  - unfold window_moves. discriminate.
  - unfold attack_moves. apply flat_map_ne with []; [apply subsets_nil | cbn; discriminate].
  - unfold block_moves. destruct (product _) as [| wb ?] eqn:E.
    + exfalso. revert E. apply product_ne. intros ch Hin. apply in_map_iff in Hin as (w & <- & _).
      destruct (Model.wtapped w); discriminate.
    + apply flat_map_ne with wb; [left; reflexivity |].
      destruct (bounded_vectors _ _) as [| tb ?] eqn:E2; [exfalso; eapply bounded_vectors_ne; eauto |].
      apply flat_map_ne with tb; [left; reflexivity | apply map_ne; discriminate].
  - unfold order_moves. apply map_ne, product_ne. intros ch Hin.
    apply in_map_iff in Hin as (l & <- & _). apply orders_ne.
  - unfold damage_moves. apply map_ne, product_ne. intros ch Hin.
    apply in_map_iff in Hin as ([p bs] & <- & _). apply kill_choices_ne.
  - apply map_ne, orders_ne.
  - discriminate Hw.
Qed.

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
    + apply moves_ne. exact Hn.
    + intros m Hin. apply NNPP. intros Hm. apply Hno. exists m. auto.
  - intros Hn Hturn m Hin Hm. apply Ht. eapply wins_mine; eauto.
Qed.

Corollary results_exhaustive : forall s, exists r, has_result r s.
Proof.
  intros s. destruct (determined PB s) as [HA | HB]; [exists AWins; exact HA |].
  destruct (determined PA s) as [HB' | HA']; [exists BWins; exact HB' |].
  exists Draw. split; assumption.
Qed.
