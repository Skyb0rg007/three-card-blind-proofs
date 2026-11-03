(** * Line-valued certificates as Rocq data

    The A-safe counterpart of the safety tables of [Packed]:
    [SaturationA.certified_opening_a] needs a [lookup] for which every entry
    passes [CheckerA.check_node]. Here [lookup] reads a table of [N] entries
    kept in primitive arrays of 63-bit integers. The keys are turn starts
    packed with [Packed.enc], A's Walkers sorted ([Packed.sortA]), and the
    keys sorted as in [Packed] (the second integer, then the first, whose
    low bits are A's life); the third column holds each entry's
    line [(c, b)], with [c + 2048] in bits 8–19 and [b] in bits 0–7, and in
    bits 20–26 the life B has in the entry's certificate state (any life is
    sound, [CheckerA.entry]; a small one makes the check faster, since the
    model's naturals are unary).

    The table is larger than a primitive array may be ([PArray.max_length]
    is about 4.2M), so each column is cut into parts of [2^20] entries:
    entry [j] is at index [j mod 2^20] of part [j / 2^20].

    A lookup may answer with the entry of the same position at a lower A
    life (A safe with less life is safe with more, [CheckerA.cert_ok]),
    and with A's Walkers in the other order
    ([SymCertA.certified_opening_a_sym]). As in [Packed], nothing about the
    packing needs to be trusted: [lookup] only answers with an entry that
    decodes to the sorted state with A's life lowered, and every entry is
    checked as the state and the line it decodes to. *)

From Stdlib Require Import List Bool Arith ZArith Lia Uint63 PArray.
Import ListNotations.
From TCB.Spec Require Import Model Game.
From TCB.Proofs Require Import Mono Packed.
From TCB.Proofs Require CheckerA SaturationA MemoA SymCertA.

(** The low [k] bits of [i], as an integer. *)
Fixpoint zfield (k : nat) (i : int) : Z :=
  match k with
  | O => 0%Z
  | S k => let r := zfield k (shr i 1) in if eqb (iand i 1) 1 then Z.succ_double r else Z.double r
  end.

(** Entry [j] of a column cut into parts of [2^20]. *)
Definition get (col : array (array int)) (j : int) : int := col.[shr j 20].[iand j 1048575].

Section ATable.

(** CheckerA's parameters: A's BIG size, B's saturation size, B's Thopter
    limit and A's Thopter cut; and the fuel. *)
Variables K Hb ott tt fuel : nat.

(** The columns and the number of entries. *)
Variables C1 C2 CV : array (array int).
Variable N : int.

Definition line_of (j : int) : Z * Z := (zfield 12 (shr (get CV j) 8) - 2048, zfield 8 (get CV j))%Z.

(** B's life in entry [j]'s certificate state. *)
Definition life_of (j : int) : nat := nat_of_int 7 (shr (get CV j) 20).

(** The first index in [lo, hi) whose key is above [(k1, k2)] (keys
    sorted as in [Packed]: the second integer, then the first). *)
Fixpoint aupper (f : nat) (lo hi k1 k2 : int) : int :=
  match f with
  | O => lo
  | S f =>
      if ltb lo hi then
        let mid := shr (add lo hi) 1 in
        let m2 := get C2 mid in
        if ltb m2 k2 || (eqb m2 k2 && leb (get C1 mid) k1) then aupper f (add mid 1) hi k1 k2 else aupper f lo mid k1 k2
      else lo
  end.

(** An entry for [s] (its Walkers sorted, [Packed.sortA]), at A's life or
    less: A safe with less life is safe with more. It is the last entry
    whose key is not above [s]'s, if that is in [s]'s run: the entry of
    [s]'s position at the highest A life up to [s]'s. A position's lines
    almost always grow with A's life; and an entry at exactly [s]'s A life
    is always the one chosen, so any state can be given the line of its
    own position. Only the entry is checked, as [s] with A's life
    lowered. *)
Definition alookup (s : state) : option (Z * Z) :=
  let s := sortA s in
  let '(k1, k2) := enc s in
  let j := sub (aupper 32 0 N k1 k2) 1 in
  if ltb j N && eqb (get C2 j) k2 && eqb (shr (get C1 j) 5) (shr k1 5) then
    let e := dec (get C1 j) (get C2 j) in
    if state_eqb (bump PA (up_by s e) e) s then Some (line_of j) else None
  else None.

(** The hints of A's moves ([Packed.hint_of]): the part of [CV] after the
    entries' parts. *)
Definition ahints : array int := CV.[shr (add N 1048575) 20].

(** Entry [j] checks, searched with [MemoA.check_m] (which implies
    [CheckerA.check_node] with every move allowed, A's hinted move first). *)
Definition aentry_ok (j : int) : bool :=
  let '(c, b) := line_of j in
  fst (MemoA.check_m K Hb ott tt alookup shash (hint_of ahints 0) fuel true
         (CheckerA.entry (life_of j) (dec (get C1 j) (get C2 j))) c b O MemoA.MLeaf).

Lemma alookup_spec : forall s l, alookup s = Some l ->
  exists j d, ltb j N = true /\ sortA s = bump PA d (dec (get C1 j) (get C2 j)) /\ l = line_of j.
Proof.
  intros s l. unfold alookup. destruct (enc (sortA s)) as [k1 k2]. cbv zeta.
  generalize (sub (aupper 32 0 N k1 k2) 1). intros j.
  destruct (ltb j N) eqn:Hj; [| discriminate]. cbn [andb].
  destruct (eqb (get C2 j) k2 && eqb (shr (get C1 j) 5) (shr k1 5)); [| discriminate].
  destruct (state_eqb (bump PA (up_by (sortA s) (dec (get C1 j) (get C2 j))) (dec (get C1 j) (get C2 j))) (sortA s))
    eqn:Hq; [| discriminate].
  intros Hl. injection Hl as <-. apply state_eqb_eq in Hq.
  exists j, (up_by (sortA s) (dec (get C1 j) (get C2 j))). auto.
Qed.

(** A does not lose going first if every entry checks and the opening's
    line allows B's starting 20 life. *)
Theorem table_safe_a : forall bs c b, chain aentry_ok bs -> hd 0%uint63 bs = 0%uint63 ->
  last bs 0%uint63 = N -> Hb < K -> 1 <= Hb ->
  alookup (CheckerA.key Hb tt (init PA)) = Some (c, b) -> (20 <= c)%Z ->
  safe PA (init PA).
Proof.
  intros bs c b Hc H0 Hl HbK Hb1 Hk Hc20.
  refine (SymCertA.certified_opening_a_sym K Hb ott tt alookup hint c b HbK Hb1 _ Hk Hc20).
  intros s c' b' Hlk. destruct (alookup_spec s _ Hlk) as (j & d & Hj & Es & E).
  destruct (sortA_sw s) as [sw Esw]. rewrite Esw in Es.
  pose proof (chain_all aentry_ok bs _ Hc H0 Hl j Hj) as Hok.
  unfold aentry_ok in Hok. rewrite <- E in Hok.
  destruct (MemoA.check_m_true K Hb ott tt alookup shash (hint_of ahints 0) _ _ _ _ _ Hok) as [f Hf].
  exists d, (dec (get C1 j) (get C2 j)), (life_of j), f, sw. auto.
Qed.

End ATable.
