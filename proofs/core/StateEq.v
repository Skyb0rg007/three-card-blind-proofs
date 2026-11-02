(** * Boolean equality of states, and the hint that allows every move

    Used by the table lookups ([Packed], [PackedA]) and by the memos of
    [MemoA] and [MemoB]. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
From TCB.Spec Require Import Model.

(** The checks try every move of the protagonist: the hint allows them all. *)
Definition hint (_ : state) (_ : move) : bool := true.

(** ** Boolean equality of states

    A plain field-by-field comparison: much faster under [vm_compute] than
    evaluating a [decide equality] proof. *)

Fixpoint lbeq {A} (eqb : A -> A -> bool) (l l' : list A) : bool :=
  match l, l' with
  | [], [] => true
  | x :: r, y :: r' => eqb x y && lbeq eqb r r'
  | _, _ => false
  end.

Lemma lbeq_eq : forall {A} (eqb : A -> A -> bool), (forall x y, eqb x y = true -> x = y) ->
  forall l l', lbeq eqb l l' = true -> l = l'.
Proof.
  intros A eqb He l. induction l as [| x r IH]; intros [| y r'] Hl; cbn in Hl; try discriminate; auto.
  apply andb_true_iff in Hl as [Hx Hr]. f_equal; auto.
Qed.

Definition walker_beq (x y : walker) : bool :=
  Nat.eqb x.(counters) y.(counters) && Bool.eqb x.(wtapped) y.(wtapped) && Bool.eqb x.(sick) y.(sick).

Definition card_beq (x y : card) : bool :=
  match x, y with CWalker, CWalker | CElixir, CElixir => true | _, _ => false end.

Definition side_beq (x y : side) : bool :=
  Nat.eqb x.(life) y.(life) && Bool.eqb x.(city) y.(city) && Nat.eqb x.(pool) y.(pool)
  && Nat.eqb x.(hand_w) y.(hand_w) && Bool.eqb x.(hand_e) y.(hand_e) && lbeq walker_beq x.(bf) y.(bf)
  && Bool.eqb x.(elixir_bf) y.(elixir_bf) && Nat.eqb x.(thop_u) y.(thop_u) && Nat.eqb x.(thop_t) y.(thop_t)
  && lbeq card_beq x.(library) y.(library) && Nat.eqb x.(gy_w) y.(gy_w).

Definition stepk_beq (x y : stepk) : bool :=
  match x, y with
  | Upkeep, Upkeep | DrawStep, DrawStep | Main1, Main1 | BeginCombat, BeginCombat
  | DeclAtk, DeclAtk | DeclBlk, DeclBlk | DamageStep, DamageStep | EndCombat, EndCombat
  | Main2, Main2 | EndStep, EndStep => true
  | _, _ => false
  end.

Definition blocker_beq (x y : blocker) : bool :=
  match x, y with BW i, BW j => Nat.eqb i j | BT, BT => true | _, _ => false end.

Definition combat_beq (x y : combat) : bool :=
  lbeq Nat.eqb x.(atk) y.(atk) && Nat.eqb x.(atk_thop) y.(atk_thop)
  && lbeq (lbeq blocker_beq) x.(blk) y.(blk) && Nat.eqb x.(trades) y.(trades).

Definition pending_beq (x y : pending) : bool :=
  match x, y with
  | Window st p b, Window st' p' b' => stepk_beq st st' && player_eqb p p' && Bool.eqb b b'
  | ChooseAttack, ChooseAttack | ChooseBlock, ChooseBlock | ChooseOrder, ChooseOrder
  | ChooseDamage, ChooseDamage => true
  | ChooseShuffle st p cs, ChooseShuffle st' p' cs' =>
      stepk_beq st st' && player_eqb p p' && lbeq card_beq cs cs'
  | Over w, Over w' => player_eqb w w'
  | _, _ => false
  end.

Definition state_eqb (x y : state) : bool :=
  player_eqb x.(active) y.(active) && Bool.eqb x.(first_turn) y.(first_turn)
  && side_beq x.(sideA) y.(sideA) && side_beq x.(sideB) y.(sideB)
  && combat_beq x.(cmb) y.(cmb) && pending_beq x.(pend) y.(pend).

Lemma player_eqb_eq : forall x y, player_eqb x y = true -> x = y.
Proof. intros [] []; cbn; congruence. Qed.

Lemma card_beq_eq : forall x y, card_beq x y = true -> x = y.
Proof. intros [] []; cbn; congruence. Qed.

Lemma stepk_beq_eq : forall x y, stepk_beq x y = true -> x = y.
Proof. intros [] []; cbn; congruence. Qed.

Lemma blocker_beq_eq : forall x y, blocker_beq x y = true -> x = y.
Proof. intros [i |] [j |]; cbn; try congruence. intros E. apply Nat.eqb_eq in E. congruence. Qed.

Lemma nat_eqb_eq : forall x y, Nat.eqb x y = true -> x = y.
Proof. apply Nat.eqb_eq. Qed.

Lemma walker_beq_eq : forall x y, walker_beq x y = true -> x = y.
Proof.
  intros [] [] E. unfold walker_beq in E. cbn in E.
  repeat rewrite andb_true_iff in E. destruct E as [[E1 E2] E3].
  apply Nat.eqb_eq in E1. apply Bool.eqb_prop in E2, E3. congruence.
Qed.

(** Turn every comparison hypothesis into an equality. *)
Ltac beq_split :=
  repeat match goal with
  | H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
  | H : player_eqb _ _ = true |- _ => apply player_eqb_eq in H
  | H : stepk_beq _ _ = true |- _ => apply stepk_beq_eq in H
  | H : lbeq Nat.eqb _ _ = true |- _ => apply (lbeq_eq _ nat_eqb_eq) in H
  | H : lbeq walker_beq _ _ = true |- _ => apply (lbeq_eq _ walker_beq_eq) in H
  | H : lbeq card_beq _ _ = true |- _ => apply (lbeq_eq _ card_beq_eq) in H
  | H : lbeq (lbeq blocker_beq) _ _ = true |- _ => apply (lbeq_eq _ (lbeq_eq _ blocker_beq_eq)) in H
  end.

Lemma side_beq_eq : forall x y, side_beq x y = true -> x = y.
Proof. intros [] [] E. unfold side_beq in E. cbn in E. beq_split. congruence. Qed.

Lemma combat_beq_eq : forall x y, combat_beq x y = true -> x = y.
Proof. intros [] [] E. unfold combat_beq in E. cbn in E. beq_split. congruence. Qed.

Lemma pending_beq_eq : forall x y, pending_beq x y = true -> x = y.
Proof. intros [] [] E; cbn in E; try discriminate; beq_split; congruence. Qed.

Lemma state_eqb_eq : forall x y, state_eqb x y = true -> x = y.
Proof.
  intros [] [] E. unfold state_eqb in E. cbn in E. beq_split.
  repeat match goal with
  | H : side_beq _ _ = true |- _ => apply side_beq_eq in H
  | H : combat_beq _ _ = true |- _ => apply combat_beq_eq in H
  | H : pending_beq _ _ = true |- _ => apply pending_beq_eq in H
  end.
  congruence.
Qed.

