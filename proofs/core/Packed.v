(** * Certificates as Rocq data

    [Saturation.certified_opening] and [WinCert.certified_win_opening] need
    a [lookup] for which every entry passes the checker. Here [lookup] reads
    a table kept in primitive arrays of 63-bit integers, so that the check
    can run inside Rocq by computation ([vm_compute]) instead of in
    extracted code.

    A record is a turn start packed into two integers ([enc]) and a value
    (for wins, a rank and a value) packed into a third. The arrays are
    sorted by the second integer of the key, then the first, whose low
    bits are A's life.

    A lookup may answer with the record of the same position at a higher A
    life (B safe or winning against more A life also is against less), and
    with A's two Walkers in the other order: the table stores each position
    with them sorted ([sortA], which is [Sym.normA]), and a lookup sorts
    the state it is asked about. [SymCert]'s versions of the checkers'
    theorems allow both ([certified_opening_sym],
    [certified_win_opening_sym]), so the table only needs one order of the
    positions that dominate the others.

    Nothing about the packing needs to be trusted: [lookup] only answers
    with a record that decodes to the sorted state with A's life raised
    (checked with [state_eqb]), and every record is checked as the state it
    decodes to. *)

From Stdlib Require Import List Bool Arith ZArith Lia Uint63 PArray.
Import ListNotations.
From TCB.Spec Require Import Model Game.
From TCB.Proofs Require Import Mono Checker Saturation WinCert Sym SymCert.
From TCB.Proofs Require Export StateEq.
From TCB.Proofs Require MemoB.

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

(** ** A hash of states, for the memos of [MemoA] and [MemoB]

    Any function would be sound; this one is cheap under [vm_compute] and
    separates the states of a turn well. It leaves out what rarely changes
    within a turn on its own (lives, hands, libraries, graveyards), and
    mixes once, with one multiplication: the memo is an unbalanced search
    tree on the hashes. *)

(** A natural, capped at 15. *)
Definition hn (n : nat) : int :=
  match n with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7
  | 8 => 8 | 9 => 9 | 10 => 10 | 11 => 11 | 12 => 12 | 13 => 13 | 14 => 14 | _ => 15
  end.
Definition hbit (b : bool) (k : int) : int := if b then k else 0.
Definition hwalker (w : walker) : int := ior (hn w.(counters)) (ior (hbit w.(wtapped) 16) (hbit w.(sick) 32)).
Fixpoint hbf (l : list walker) : int :=
  match l with [] => 0 | w :: l => ior (add (hwalker w) 1) (shl (hbf l) 7) end.
Definition hside (sd : side) : int :=
  ior (hbit sd.(city) 1) (ior (hbit sd.(elixir_bf) 2) (ior (shl (hn sd.(pool)) 2)
  (ior (shl (hn sd.(thop_u)) 6) (ior (shl (hn sd.(thop_t)) 10) (shl (hbf sd.(bf)) 14))))).
Definition hstep (st : stepk) : int :=
  match st with
  | Upkeep => 0 | DrawStep => 1 | Main1 => 2 | BeginCombat => 3 | DeclAtk => 4
  | DeclBlk => 5 | DamageStep => 6 | EndCombat => 7 | Main2 => 8 | EndStep => 9
  end.
Definition hpend (p : pending) : int :=
  match p with
  | Window st p b => ior (hstep st) (ior (hbit (player_bit p) 16) (hbit b 32))
  | ChooseAttack => 64 | ChooseBlock => 65 | ChooseOrder => 66 | ChooseDamage => 67
  | ChooseShuffle _ p cs => ior 68 (ior (hbit (player_bit p) 16) (shl (hn (List.length cs)) 7))
  | Over _ => 69
  end.
Fixpoint hblk (l : list (list blocker)) : int :=
  match l with [] => 0 | bs :: l => add (hn (List.length bs)) (shl (hblk l) 4) end.
Fixpoint hatk (l : list nat) : int :=
  match l with [] => 0 | i :: l => ior (add (hn i) 1) (shl (hatk l) 4) end.
Definition hcombat (c : combat) : int :=
  ior (hatk c.(atk)) (ior (shl (hn c.(atk_thop)) 12) (ior (shl (hblk c.(blk)) 16) (shl (hn c.(trades)) 28))).
Definition shash (s : state) : int :=
  add (PrimInt63.mul (ior (hside s.(sideA)) (shl (hside s.(sideB)) 28)) 1000003)
    (ior (hpend s.(pend)) (shl (hcombat s.(cmb)) 11)).

(** ** Checking every index of a table *)

Section Ranges.

Variable ok : int -> bool.

(** Every index in [j, hi) checks. *)
Fixpoint range_ok (f : nat) (j hi : int) : bool :=
  if ltb j hi then match f with O => false | S f => ok j && range_ok f (add j 1) hi end
  else true.

(** Ranges between consecutive boundaries check; each is proved on its own. *)
Fixpoint chain (bs : list int) : Prop :=
  match bs with
  | b :: ((b' :: _) as rest) => (exists f, range_ok f b b' = true) /\ chain rest
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

Lemma chain_spec : forall bs, chain bs ->
  forall k, (to_Z (hd 0%uint63 bs) <= to_Z k < to_Z (last bs 0%uint63))%Z -> ok k = true.
Proof.
  intro bs. induction bs as [| b [| b' bs] IH]; intros Hc k Hk.
  - cbn [hd last] in Hk. lia.
  - cbn [hd last] in Hk. lia.
  - destruct Hc as [[f Hr] Hc]. change (hd 0%uint63 (b :: b' :: bs)) with b in Hk.
    change (last (b :: b' :: bs) 0%uint63) with (last (b' :: bs) 0%uint63) in Hk.
    destruct (Z.lt_ge_cases (to_Z k) (to_Z b')).
    + exact (range_ok_spec f b b' Hr k ltac:(lia)).
    + apply IH; [exact Hc |]. change (hd 0%uint63 (b' :: bs)) with b'. lia.
Qed.

(** A chain from 0 to [n] covers every index below [n]. *)
Lemma chain_all : forall bs n, chain bs -> hd 0%uint63 bs = 0%uint63 -> last bs 0%uint63 = n ->
  forall j, ltb j n = true -> ok j = true.
Proof.
  intros bs n Hc H0 Hl j Hj. apply (chain_spec bs Hc j).
  rewrite H0, Hl, to_Z_0. apply ltb_spec in Hj. pose proof (to_Z_bounded j). lia.
Qed.

End Ranges.

(** ** One order of A's Walkers

    The tables store each position with A's two Walkers sorted as
    [Sym.normA] sorts them, and a lookup sorts the state it is asked about
    the same way: [SymCert]'s certificates may answer for a state with the
    entry of the state with A's Walkers swapped. [sortA] is [normA],
    computed with one comparison of the counters instead of [wcode]'s
    arithmetic (the model's naturals are unary). *)

Definition wlt (v w : walker) : bool :=
  match Nat.compare v.(counters) w.(counters) with
  | Lt => true
  | Gt => false
  | Eq =>
      match v.(wtapped), w.(wtapped) with
      | false, true => true
      | true, false => false
      | _, _ => negb v.(sick) && w.(sick)
      end
  end.

Lemma wlt_walker_ltb : forall v w, wlt v w = walker_ltb v w.
Proof.
  intros [c t k] [c' t' k']. unfold wlt, walker_ltb, wcode. cbn [Model.counters Model.wtapped Model.sick].
  destruct (Nat.compare_spec c c') as [E | E | E].
  - subst. destruct t, k, t', k'; cbn; symmetry; apply Nat.ltb_lt || apply Nat.ltb_ge; lia.
  - symmetry. apply Nat.ltb_lt. destruct t, k, t', k'; cbn; lia.
  - symmetry. apply Nat.ltb_ge. destruct t, k, t', k'; cbn; lia.
Qed.

Definition sortA (s : state) : state :=
  match s.(sideA).(bf) with
  | w0 :: w1 :: _ => if wlt w1 w0 then swapA s else s
  | _ => s
  end.

Lemma sortA_normA : forall s, sortA s = normA s.
Proof.
  intros s. unfold sortA, normA, unsorted.
  destruct (bf (sideA s)) as [| w0 [| w1 r]]; [reflexivity | reflexivity |].
  rewrite wlt_walker_ltb. reflexivity.
Qed.

Lemma sortA_sw : forall s, exists sw : bool, sortA s = if sw then swapA s else s.
Proof. intros s. rewrite sortA_normA. apply normA_sw. Qed.

(** ** Finding a key

    The records are sorted by the second integer of their key, then by
    the first. A's life is the low 5 bits of the first, so all of A's lives
    of a position are next to each other, in increasing order: its run.
    A lookup finds the record it wants by binary search on the whole key,
    and is checked: the record it returns must be the looked-up state with
    A's life changed ([state_eqb] against a [bump] of one by the other),
    which is all the soundness theorems need. *)

Section Keys.

Variables K1 K2 : array int.

(** The first index in [lo, hi) whose key is not below [(k1, k2)]. *)
Fixpoint lower (f : nat) (lo hi k1 k2 : int) : int :=
  match f with
  | O => lo
  | S f =>
      if ltb lo hi then
        let mid := shr (add lo hi) 1 in
        let m2 := K2.[mid] in
        if ltb m2 k2 || (eqb m2 k2 && ltb K1.[mid] k1) then lower f (add mid 1) hi k1 k2 else lower f lo mid k1 k2
      else lo
  end.

(** The first record of the run of [(k1, k2)] at [k1]'s A life or more. *)
Definition start (k1 k2 : int) : int := lower 32 0 (PArray.length K1) k1 k2.

(** Index [j] is in the run of [(k1, k2)]. *)
Definition in_run (j k1 k2 : int) : bool :=
  ltb j (PArray.length K1) && eqb K2.[j] k2 && eqb (shr K1.[j] 5) (shr k1 5).

End Keys.

(** A's life in [e] is at least that in [s]: [e] is [s] with [d] more. *)
Definition up_by (e s : state) : nat := e.(sideA).(life) - s.(sideA).(life).

(** ** Win tables: keys, then rank and value *)

Section WinTable.

Variables H ott tt fuel : nat.
Variables K1 K2 RV : array int.

Definition rank_of (j : int) : nat := nat_of_int 16 (shr RV.[j] 6).
Definition val_of (j : int) : nat := nat_of_int 6 RV.[j].

(** Among the records of the run of [(k1, k2)] from [j] with a rank
    passing [ok], the one needing the least life ([best] if none). *)
Fixpoint wbest (f : nat) (ok : int -> bool) (j k1 k2 best : int) : int :=
  match f with
  | O => best
  | S f =>
      if in_run K1 K2 j k1 k2 then
        let best :=
          if ok (shr RV.[j] 6) && (negb (ltb best (PArray.length K1)) || ltb (iand RV.[j] 63) (iand RV.[best] 63))
          then j else best in
        wbest f ok (add j 1) k1 k2 best
      else best
  end.

(** A record of rank [r] for [s] (its Walkers sorted), at A's life or
    more. *)
Definition lookup (s : state) (r : nat) : option nat :=
  let s := sortA s in
  let '(k1, k2) := enc s in
  let ri := int_of_nat r in
  let j := wbest 256 (fun x => eqb x ri) (start K1 K2 k1 k2) k1 k2 (PArray.length K1) in
  if ltb j (PArray.length K1) && Nat.eqb (rank_of j) r then
    let e := dec K1.[j] K2.[j] in
    if state_eqb e (bump PA (up_by e s) s) then Some (val_of j) else None
  else None.

(** The rank of the record below rank [r] for [s] needing the least life. *)
Definition below (s : state) (r : nat) : option nat :=
  let '(k1, k2) := enc (sortA s) in
  let ri := int_of_nat r in
  let j := wbest 256 (fun x => ltb x ri) (start K1 K2 k1 k2) k1 k2 (PArray.length K1) in
  if ltb j (PArray.length K1) then Some (rank_of j) else None.

(** Record [j] checks, searched with [MemoB.check_mw] (which implies
    [WinCert.check_win] with every move of B's allowed). *)
Definition record_ok (j : int) : bool :=
  fst (MemoB.check_mw H ott tt shash lookup below (rank_of j) fuel true (entry (dec K1.[j] K2.[j]) (val_of j))
         MemoA.MLeaf).

Lemma lookup_spec : forall s r v, lookup s r = Some v ->
  exists j d, ltb j (PArray.length K1) = true /\ dec K1.[j] K2.[j] = bump PA d (sortA s) /\
    r = rank_of j /\ v = val_of j.
Proof.
  intros s r v. unfold lookup. destruct (enc (sortA s)) as [k1 k2]. cbv zeta.
  match goal with |- context [wbest ?f ?ok ?j ?a ?b ?c] => generalize (wbest f ok j a b c) end. intros j.
  destruct (ltb j (PArray.length K1)) eqn:Hj; [| discriminate].
  destruct (Nat.eqb (rank_of j) r) eqn:Er; [| discriminate]. cbn [andb].
  destruct (state_eqb (dec K1.[j] K2.[j]) (bump PA (up_by (dec K1.[j] K2.[j]) (sortA s)) (sortA s))) eqn:Hq;
    [| discriminate].
  intros Hv. injection Hv as <-. apply state_eqb_eq in Hq. apply Nat.eqb_eq in Er.
  exists j, (up_by (dec K1.[j] K2.[j]) (sortA s)). auto.
Qed.

(** B wins from the opening if every record checks and the opening has a
    record on at most 20 life. *)
Theorem table_wins : forall bs r v, chain record_ok bs -> hd 0%uint63 bs = 0%uint63 ->
  last bs 0%uint63 = PArray.length K1 -> lookup (key H tt (init PB)) r = Some v -> v <= 20 ->
  wins PB (init PB).
Proof.
  intros bs r v Hc H0 Hl Hr Hv.
  refine (certified_win_opening_sym H ott tt lookup below hint PB r v _ Hr Hv).
  intros s r' v' Hlk. destruct (lookup_spec s r' v' Hlk) as (j & d & Hj & E & -> & ->).
  destruct (sortA_sw s) as [sw Esw]. rewrite Esw in E.
  destruct (MemoB.check_mw_true H ott tt shash lookup below _ _ _ (chain_all record_ok bs _ Hc H0 Hl j Hj))
    as [f Hf].
  exists d, f, sw. rewrite <- E. exact Hf.
Qed.

End WinTable.

(** ** Safety tables: keys, then value *)

Section SafeTable.

Variables H ott tt fuel : nat.
Variables K1 K2 V : array int.

Definition sval_of (j : int) : nat := nat_of_int 6 V.[j].

(** Among the entries of the run of [(k1, k2)] from [j], the one needing
    the least life ([best] if none). *)
Fixpoint sbest (f : nat) (j k1 k2 best : int) : int :=
  match f with
  | O => best
  | S f =>
      if in_run K1 K2 j k1 k2 then
        let best := if negb (ltb best (PArray.length K1)) || ltb V.[j] V.[best] then j else best in
        sbest f (add j 1) k1 k2 best
      else best
  end.

(** An entry for [s] (its Walkers sorted), at A's life or more. *)
Definition slookup (s : state) : option nat :=
  let s := sortA s in
  let '(k1, k2) := enc s in
  let j := sbest 64 (start K1 K2 k1 k2) k1 k2 (PArray.length K1) in
  if ltb j (PArray.length K1) then
    let e := dec K1.[j] K2.[j] in
    if state_eqb e (bump PA (up_by e s) s) then Some (sval_of j) else None
  else None.

(** Entry [j] checks, searched with [MemoB.check_mb] (which implies
    [Checker.check_node] with every move of B's allowed). *)
Definition entry_ok (j : int) : bool :=
  fst (MemoB.check_mb H ott tt shash slookup fuel true (entry (dec K1.[j] K2.[j]) (sval_of j)) MemoA.MLeaf).

Lemma slookup_spec : forall s v, slookup s = Some v ->
  exists j d, ltb j (PArray.length K1) = true /\ dec K1.[j] K2.[j] = bump PA d (sortA s) /\ v = sval_of j.
Proof.
  intros s v. unfold slookup. destruct (enc (sortA s)) as [k1 k2]. cbv zeta.
  match goal with |- context [sbest ?f ?j ?a ?b ?c] => generalize (sbest f j a b c) end. intros j.
  destruct (ltb j (PArray.length K1)) eqn:Hj; [| discriminate].
  destruct (state_eqb (dec K1.[j] K2.[j]) (bump PA (up_by (dec K1.[j] K2.[j]) (sortA s)) (sortA s))) eqn:Hq;
    [| discriminate].
  intros Hv. injection Hv as <-. apply state_eqb_eq in Hq.
  exists j, (up_by (dec K1.[j] K2.[j]) (sortA s)). auto.
Qed.

(** B does not lose from the opening of [p] if every entry checks and the
    opening's entry asks for at most 20 life. *)
Theorem table_safe : forall p bs v, chain entry_ok bs -> hd 0%uint63 bs = 0%uint63 ->
  last bs 0%uint63 = PArray.length K1 -> slookup (key H tt (init p)) = Some v -> v <= 20 ->
  safe PB (init p).
Proof.
  intros p bs v Hc H0 Hl Hr Hv.
  refine (certified_opening_sym H ott tt slookup hint p v _ Hr Hv).
  intros s v' Hlk. destruct (slookup_spec s v' Hlk) as (j & d & Hj & E & ->).
  destruct (sortA_sw s) as [sw Esw]. rewrite Esw in E.
  destruct (MemoB.check_mb_true H ott tt shash slookup _ _ (chain_all entry_ok bs _ Hc H0 Hl j Hj)) as [f Hf].
  exists d, f, sw. rewrite <- E. exact Hf.
Qed.

End SafeTable.
