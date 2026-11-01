(** * Certificates as Rocq data

    [Saturation.certified_opening] and [WinCert.certified_win_opening] need
    a [lookup] for which every entry passes the checker. Here [lookup] reads
    a table kept in primitive arrays of 63-bit integers, so that the check
    can run inside Rocq by computation ([vm_compute]) instead of in
    extracted code.

    A record is a turn start packed into two integers ([enc]) and a value
    (for wins, a rank and a value) packed into a third. The arrays are
    sorted by key (then rank).
    Nothing about the packing needs to be trusted: [lookup] only answers for
    a state that decodes back to itself ([dec], checked with [state_eqb]),
    and every record is checked as the state it decodes to. *)

From Stdlib Require Import List Bool Arith ZArith Lia Uint63 PArray.
Import ListNotations.
From TCB.Spec Require Import Model Game.
From TCB.Proofs Require Import Checker Saturation WinCert.

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

(** ** Packing turn starts into two integers *)

Definition iand := PrimInt63.land.
Definition ior := PrimInt63.lor.
Definition shl := PrimInt63.lsl.
Definition shr := PrimInt63.lsr.

Fixpoint int_of_nat (n : nat) : int :=
  match n with O => 0%uint63 | S n => add (int_of_nat n) 1 end.

(** The low [k] bits of [i]. *)
Fixpoint nat_of_int (k : nat) (i : int) : nat :=
  match k with
  | O => O
  | S k => let r := nat_of_int k (shr i 1) in if eqb (iand i 1) 1 then S (r + r) else r + r
  end.

Definition b2i (b : bool) : int := if b then 1%uint63 else 0%uint63.
Definition put (off w : int) (x : int) : int := shl (iand x (sub (shl 1 w) 1)) off.
Definition field (i off : int) (k : nat) : nat := nat_of_int k (shr i off).
Definition bit (i off : int) : bool := eqb (iand (shr i off) 1) 1.

Definition enc_walker (w : walker) : int :=
  ior (put 0 5 (int_of_nat w.(counters))) (ior (put 5 1 (b2i w.(wtapped))) (put 6 1 (b2i w.(sick)))).
Definition dec_walker (x : int) : walker := mkWalker (nat_of_int 5 x) (bit x 5) (bit x 6).

Definition enc_card (c : card) : int := match c with CWalker => 0%uint63 | CElixir => 1%uint63 end.
Definition dec_card (b : bool) : card := if b then CElixir else CWalker.

(** Bit layout of a side (53 bits): life 0–4, City 5, pool 6–8, Walkers in
    hand 9–10, Elixir in hand 11, Elixir on the battlefield 12, untapped
    Thopters 13–17, tapped Thopters 18–22, graveyard 23–24, number of
    Walkers on the battlefield 25–26, three Walker slots of 7 bits from 27,
    library length 48–49, three library slots 50–52. *)
Definition enc_side (sd : side) : int :=
  let ws := sd.(bf) in
  let lib := sd.(library) in
  let wslot n := match nth_error ws n with Some w => enc_walker w | None => 0%uint63 end in
  let cslot n := match nth_error lib n with Some c => enc_card c | None => 0%uint63 end in
  fold_right ior 0%uint63
    [put 0 5 (int_of_nat sd.(life)); put 5 1 (b2i sd.(city)); put 6 3 (int_of_nat sd.(pool));
     put 9 2 (int_of_nat sd.(hand_w)); put 11 1 (b2i sd.(hand_e)); put 12 1 (b2i sd.(elixir_bf));
     put 13 5 (int_of_nat sd.(thop_u)); put 18 5 (int_of_nat sd.(thop_t)); put 23 2 (int_of_nat sd.(gy_w));
     put 25 2 (int_of_nat (List.length ws)); put 27 7 (wslot 0); put 34 7 (wslot 1); put 41 7 (wslot 2);
     put 48 2 (int_of_nat (List.length lib)); put 50 1 (cslot 0); put 51 1 (cslot 1); put 52 1 (cslot 2)].

Definition dec_side (x : int) : side :=
  mkSide (field x 0 5) (bit x 5) (field x 6 3) (field x 9 2) (bit x 11)
    (firstn (field x 25 2) [dec_walker (shr x 27); dec_walker (shr x 34); dec_walker (shr x 41)])
    (bit x 12) (field x 13 5) (field x 18 5)
    (firstn (field x 48 2) [dec_card (bit x 50); dec_card (bit x 51); dec_card (bit x 52)])
    (field x 23 2).

Definition player_bit (p : player) : bool := match p with PA => false | PB => true end.

(** A's side, plus the active player (bit 53) and the first-turn flag (bit 54);
    then B's side. Only turn starts are packed: no combat, upkeep window. *)
Definition enc (s : state) : int * int :=
  (ior (enc_side s.(sideA)) (ior (put 53 1 (b2i (player_bit s.(active)))) (put 54 1 (b2i s.(first_turn)))),
   enc_side s.(sideB)).

Definition dec (k1 k2 : int) : state :=
  let p := if bit k1 53 then PB else PA in
  mkState p (bit k1 54) (dec_side k1) (dec_side k2) no_combat (Window Upkeep p false).

(** ** Checking every index of a table *)

Section Ranges.

Variable ok : int -> bool.

(** Every index in [j, hi) checks. *)
Fixpoint range_ok (f : nat) (j hi : int) : bool :=
  if ltb j hi then match f with O => false | S f => ok j && range_ok f (add j 1) hi end
  else true.

(** Ranges between consecutive boundaries check; each is proved on its own. *)
Fixpoint chain (f : nat) (bs : list int) : Prop :=
  match bs with
  | b :: ((b' :: _) as rest) => range_ok f b b' = true /\ chain f rest
  | _ => True
  end.

Lemma range_ok_spec : forall f j hi, range_ok f j hi = true ->
  forall k, (to_Z j <= to_Z k < to_Z hi)%Z -> ok k = true.
Proof.
  induction f as [| f IH]; intros j hi Hr k Hk; cbn [range_ok] in Hr;
    destruct (ltb j hi) eqn:Hlt.
  - discriminate.
  - apply not_true_iff_false in Hlt. exfalso. apply Hlt, ltb_spec. lia.
  - apply andb_true_iff in Hr as [Hj Hr]. apply ltb_spec in Hlt.
    destruct (Z.eq_dec (to_Z j) (to_Z k)) as [E | E].
    + apply to_Z_inj in E. subst. exact Hj.
    + apply (IH _ _ Hr). rewrite add_spec, to_Z_1. pose proof (to_Z_bounded hi). pose proof (to_Z_bounded j).
      rewrite Z.mod_small; lia.
  - apply not_true_iff_false in Hlt. exfalso. apply Hlt, ltb_spec. lia.
Qed.

Lemma chain_spec : forall f bs, chain f bs ->
  forall k, (to_Z (hd 0%uint63 bs) <= to_Z k < to_Z (last bs 0%uint63))%Z -> ok k = true.
Proof.
  intros f bs. induction bs as [| b [| b' bs] IH]; intros Hc k Hk.
  - cbn [hd last] in Hk. lia.
  - cbn [hd last] in Hk. lia.
  - destruct Hc as [Hr Hc]. change (hd 0%uint63 (b :: b' :: bs)) with b in Hk.
    change (last (b :: b' :: bs) 0%uint63) with (last (b' :: bs) 0%uint63) in Hk.
    destruct (Z.lt_ge_cases (to_Z k) (to_Z b')).
    + exact (range_ok_spec f b b' Hr k ltac:(lia)).
    + apply IH; [exact Hc |]. change (hd 0%uint63 (b' :: bs)) with b'. lia.
Qed.

(** A chain from 0 to [n] covers every index below [n]. *)
Lemma chain_all : forall f bs n, chain f bs -> hd 0%uint63 bs = 0%uint63 -> last bs 0%uint63 = n ->
  forall j, ltb j n = true -> ok j = true.
Proof.
  intros f bs n Hc H0 Hl j Hj. apply (chain_spec f bs Hc j).
  rewrite H0, Hl, to_Z_0. apply ltb_spec in Hj. pose proof (to_Z_bounded j). lia.
Qed.

End Ranges.

(** ** Finding a key *)

Section Keys.

Variables K1 K2 : array int.

Definition key_lt (a1 a2 b1 b2 : int) : bool := ltb a1 b1 || (eqb a1 b1 && ltb a2 b2).

(** The first index in [lo, hi) whose key is not below [(k1, k2)]. *)
Fixpoint lower (f : nat) (lo hi k1 k2 : int) : int :=
  match f with
  | O => lo
  | S f =>
      if ltb lo hi then
        let mid := shr (add lo hi) 1 in
        if key_lt K1.[mid] K2.[mid] k1 k2 then lower f (add mid 1) hi k1 k2 else lower f lo mid k1 k2
      else lo
  end.

Definition start (k1 k2 : int) : int := lower 32 0 (PArray.length K1) k1 k2.

Definition at_key (j k1 k2 : int) : bool := ltb j (PArray.length K1) && eqb K1.[j] k1 && eqb K2.[j] k2.

Lemma at_key_spec : forall j k1 k2, at_key j k1 k2 = true ->
  ltb j (PArray.length K1) = true /\ K1.[j] = k1 /\ K2.[j] = k2.
Proof.
  intros j k1 k2 Ha. unfold at_key in Ha.
  apply andb_true_iff in Ha as [Ha E2]. apply andb_true_iff in Ha as [Hl E1].
  apply eqb_spec in E1, E2. auto.
Qed.

End Keys.

(** B's moves are all tried: the checks are then plain searches. *)
Definition hint (_ : state) (_ : move) : bool := true.

(** ** Win tables: keys, then rank and value *)

Section WinTable.

Variables H ott tt fuel : nat.
Variables K1 K2 RV : array int.

Definition rank_of (j : int) : nat := nat_of_int 16 (shr RV.[j] 6).
Definition val_of (j : int) : nat := nat_of_int 6 RV.[j].

(** The record of [(k1, k2)] with rank [r], scanning from [j]. *)
Fixpoint scan (f : nat) (j k1 k2 : int) (r : nat) : option int :=
  match f with
  | O => None
  | S f => if at_key K1 K2 j k1 k2 then if Nat.eqb (rank_of j) r then Some j else scan f (add j 1) k1 k2 r else None
  end.

(** The highest rank of [(k1, k2)] below [r], scanning from [j]. *)
Fixpoint scan_below (f : nat) (j k1 k2 : int) (r : nat) (best : option nat) : option nat :=
  match f with
  | O => best
  | S f =>
      if at_key K1 K2 j k1 k2 then
        scan_below f (add j 1) k1 k2 r (if Nat.ltb (rank_of j) r then Some (rank_of j) else best)
      else best
  end.

Definition lookup (s : state) (r : nat) : option nat :=
  let '(k1, k2) := enc s in
  match scan 64 (start K1 K2 k1 k2) k1 k2 r with
  | Some j => if state_eqb (dec k1 k2) s then Some (val_of j) else None
  | None => None
  end.

Definition below (s : state) (r : nat) : option nat :=
  let '(k1, k2) := enc s in scan_below 64 (start K1 K2 k1 k2) k1 k2 r None.

Definition record_ok (j : int) : bool :=
  check_win H ott tt lookup below hint (rank_of j) fuel true (entry (dec K1.[j] K2.[j]) (val_of j)).

Lemma scan_spec : forall f j k1 k2 r i, scan f j k1 k2 r = Some i ->
  ltb i (PArray.length K1) = true /\ K1.[i] = k1 /\ K2.[i] = k2 /\ rank_of i = r.
Proof.
  induction f as [| f IH]; intros j k1 k2 r i Hs; [discriminate |]. cbn [scan] in Hs.
  destruct (at_key K1 K2 j k1 k2) eqn:Ha; [| discriminate].
  destruct (Nat.eqb (rank_of j) r) eqn:Er; [| exact (IH _ _ _ _ _ Hs)].
  injection Hs as <-. apply at_key_spec in Ha as (Hl & E1 & E2). apply Nat.eqb_eq in Er. auto.
Qed.

Lemma lookup_spec : forall s r v, lookup s r = Some v ->
  exists j, ltb j (PArray.length K1) = true /\ s = dec K1.[j] K2.[j] /\ r = rank_of j /\ v = val_of j.
Proof.
  intros s r v. unfold lookup. destruct (enc s) as [k1 k2].
  destruct (scan 64 (start K1 K2 k1 k2) k1 k2 r) as [j |] eqn:Hs; [| discriminate].
  destruct (state_eqb (dec k1 k2) s) eqn:Hq; [| discriminate].
  intros Hv. injection Hv as <-. apply state_eqb_eq in Hq.
  destruct (scan_spec _ _ _ _ _ _ Hs) as (Hj & E1 & E2 & Er).
  exists j. subst. auto.
Qed.

(** B wins from the opening if every record checks and the opening has a
    record on at most 20 life. *)
Theorem table_wins : forall bs r v, chain record_ok fuel bs -> hd 0%uint63 bs = 0%uint63 ->
  last bs 0%uint63 = PArray.length K1 -> lookup (key H tt (init PB)) r = Some v -> v <= 20 ->
  wins PB (init PB).
Proof.
  intros bs r v Hc H0 Hl Hr Hv.
  refine (certified_win_opening H ott tt lookup below hint fuel PB r v _ Hr Hv).
  intros s r' v' Hlk. destruct (lookup_spec s r' v' Hlk) as (j & Hj & -> & -> & ->).
  exact (chain_all record_ok fuel bs _ Hc H0 Hl j Hj).
Qed.

End WinTable.

(** ** Safety tables: keys, then value *)

Section SafeTable.

Variables H ott tt fuel : nat.
Variables K1 K2 V : array int.

Definition sval_of (j : int) : nat := nat_of_int 6 V.[j].

Definition slookup (s : state) : option nat :=
  let '(k1, k2) := enc s in
  let j := start K1 K2 k1 k2 in
  if at_key K1 K2 j k1 k2 then if state_eqb (dec k1 k2) s then Some (sval_of j) else None else None.

Definition entry_ok (j : int) : bool :=
  check_node H ott tt slookup hint fuel true (entry (dec K1.[j] K2.[j]) (sval_of j)).

Lemma slookup_spec : forall s v, slookup s = Some v ->
  exists j, ltb j (PArray.length K1) = true /\ s = dec K1.[j] K2.[j] /\ v = sval_of j.
Proof.
  intros s v. unfold slookup. destruct (enc s) as [k1 k2].
  destruct (at_key K1 K2 (start K1 K2 k1 k2) k1 k2) eqn:Ha; [| discriminate].
  destruct (state_eqb (dec k1 k2) s) eqn:Hq; [| discriminate].
  intros Hv. injection Hv as <-. apply state_eqb_eq in Hq. apply at_key_spec in Ha as (Hl & E1 & E2).
  exists (start K1 K2 k1 k2). rewrite E1, E2. auto.
Qed.

(** B does not lose from the opening of [p] if every entry checks and the
    opening's entry asks for at most 20 life. *)
Theorem table_safe : forall p bs v, chain entry_ok fuel bs -> hd 0%uint63 bs = 0%uint63 ->
  last bs 0%uint63 = PArray.length K1 -> slookup (key H tt (init p)) = Some v -> v <= 20 ->
  safe PB (init p).
Proof.
  intros p bs v Hc H0 Hl Hr Hv.
  refine (certified_opening H ott tt slookup hint fuel p v _ Hr Hv).
  intros s v' Hlk. destruct (slookup_spec s v' Hlk) as (j & Hj & -> & ->).
  exact (chain_all entry_ok fuel bs _ Hc H0 Hl j Hj).
Qed.

End SafeTable.
