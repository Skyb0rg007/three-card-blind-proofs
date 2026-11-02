(** * The simulation facts behind [CheckerA.cert_safe] (REDUCTION.md, BIG mode)

    [CheckerA.RA n s t] says the certificate state [s] abstracts the real
    state [t] whose BIG Walker has [K + n] counters: B's saturated Walkers
    (at least [Hb] counters) may differ in size, A may have more Thopters
    and another graveyard in [t], and B's life is not related. This file
    proves what [cert_safe] assumes about it, then the closed theorems.

    The proof follows [Saturation], with the roles mirrored. [RA] factors
    through [RB], which has A's Thopters equal and tracks B's life by a
    fixed offset, and [Mono.thop_le] for A's extra Thopters. *)

From Stdlib Require Import List Bool Arith ZArith Lia.
Import ListNotations.
From TCB.Spec Require Import Model Game.
From TCB.Proofs Require Import Mono Checker.
From TCB.Proofs Require Saturation Preservation.
From TCB.Proofs Require Import CheckerA.

Open Scope nat_scope.

(** ** Lists *)

(** [update_nth] as a recursive function. *)
Lemma upd_shift : forall {X} (f : X -> X) l st i,
  map (fun '(j, x) => if j =? S i then f x else x) (combine (seq (S st) (length l)) l) =
  map (fun '(j, x) => if j =? i then f x else x) (combine (seq st (length l)) l).
Proof.
  intros X f l. induction l as [| x l IH]; intros st i; [reflexivity |].
  cbn [length seq combine map]. rewrite IH. reflexivity.
Qed.

Lemma upd_skip : forall {X} (f : X -> X) l st i, i < st ->
  map (fun '(j, x) => if j =? i then f x else x) (combine (seq st (length l)) l) = l.
Proof.
  intros X f l. induction l as [| x l IH]; intros st i Hi; [reflexivity |].
  cbn [length seq combine map]. destruct (Nat.eqb_spec st i); [lia |]. f_equal. apply IH. lia.
Qed.

Lemma upd_0 : forall {X} (f : X -> X) x l, update_nth 0 f (x :: l) = f x :: l.
Proof. intros. unfold update_nth, enum. cbn [length seq combine map Nat.eqb]. f_equal. apply upd_skip. lia. Qed.

Lemma upd_S : forall {X} (f : X -> X) i x l, update_nth (S i) f (x :: l) = x :: update_nth i f l.
Proof. intros. unfold update_nth, enum. cbn [length seq combine map Nat.eqb]. f_equal. apply upd_shift. Qed.

Lemma F2_upd : forall {X Y} (P : X -> Y -> Prop) f g i l l', Forall2 P l l' ->
  (forall x y, nth_error l i = Some x -> P x y -> P (f x) (g y)) ->
  Forall2 P (update_nth i f l) (update_nth i g l').
Proof.
  intros X Y P f g i l l' Hl. revert i.
  induction Hl as [| x y l l' Hxy Hl IH]; intros [| i] Hf; [constructor | constructor | |].
  - rewrite !upd_0. constructor; [apply Hf; auto | exact Hl].
  - rewrite !upd_S. constructor; [exact Hxy | apply IH; exact Hf].
Qed.

Lemma map_upd_same : forall {X Y} (g : X -> Y) f i l,
  (forall x, nth_error l i = Some x -> g (f x) = g x) -> map g (update_nth i f l) = map g l.
Proof.
  intros X Y g f i l. revert i. induction l as [| x l IH]; intros [| i] Hf; [reflexivity | reflexivity | |].
  - rewrite upd_0. cbn. rewrite Hf; reflexivity.
  - rewrite upd_S. cbn. f_equal. apply IH. exact Hf.
Qed.

Lemma nth_map_error : forall {X} (g : X -> nat) l i x, nth_error l i = Some x -> nth i (map g l) 0 = g x.
Proof.
  intros X g l. induction l as [| y l IH]; intros [| i] x E; cbn in E; try discriminate.
  - injection E as ->. reflexivity.
  - cbn. apply IH. exact E.
Qed.

Lemma F2_remove_gen : forall {X Y} (P : X -> Y -> Prop) dead l l', Forall2 P l l' ->
  Forall2 P (remove_indices dead l) (remove_indices dead l').
Proof.
  intros X Y P dead l l' Hl. unfold remove_indices, enum.
  rewrite <- (Forall2_length Hl). generalize 0.
  induction Hl as [| x y l l' Hxy Hl IH]; intros i; cbn [length seq combine filter map]; [constructor |].
  destruct (existsb (Nat.eqb i) dead); cbn [negb map]; [apply IH | constructor; [exact Hxy | apply IH]].
Qed.

(** An element of [l] whose index is not removed stays. *)
Lemma remove_keep : forall {X} dead (l : list X) i x, nth_error l i = Some x -> ~ In i dead ->
  In x (remove_indices dead l).
Proof.
  intros X dead l i x E Hi. unfold remove_indices, enum.
  assert (Hg : forall st, nth_error l (i - st) = Some x -> st <= i ->
    In x (map snd (filter (fun '(j, _) => negb (existsb (Nat.eqb j) dead)) (combine (seq st (length l)) l)))).
  { clear E. induction l as [| y l IH]; intros st E Hst; [destruct (i - st); discriminate |].
    cbn [length seq combine filter].
    destruct (Nat.eq_dec i st) as [-> | Hne].
    - rewrite Nat.sub_diag in E. cbn in E. injection E as ->.
      destruct (existsb (Nat.eqb st) dead) eqn:Ex.
      + exfalso. apply existsb_exists in Ex as [j [Hj Ej]]. apply Nat.eqb_eq in Ej. subst. contradiction.
      + cbn. left. reflexivity.
    - assert (E' : nth_error l (i - S st) = Some x).
      { replace (i - st) with (S (i - S st)) in E by lia. exact E. }
      destruct (negb (existsb (Nat.eqb st) dead)); cbn [map]; [right |]; apply IH; auto; lia. }
  apply Hg; [rewrite Nat.sub_0_r; exact E | lia].
Qed.

Lemma remove_sublist_len : forall {X} (h : X -> bool) dead l,
  length (filter h (remove_indices dead l)) <= length (filter h l).
Proof.
  intros X h dead l. unfold remove_indices, enum. generalize 0.
  induction l as [| x l IH]; intros st; cbn [length seq combine filter map]; [lia |].
  specialize (IH (S st)).
  destruct (h x) eqn:Ehx; match goal with |- context [if negb ?b then _ else _] => destruct b end;
    cbn [negb length map filter snd]; rewrite ?Ehx; cbn [length]; lia.
Qed.

Lemma NoDup_fst_combine : forall {X Y} (l : list X) (l2 : list Y), NoDup l -> NoDup (map fst (combine l l2)).
Proof.
  intros X Y l. induction l as [| x l IH]; intros [| y l2] Hn; cbn; [constructor .. |].
  apply NoDup_cons_iff in Hn as [Hx Hn]. constructor; [| apply IH; exact Hn].
  intros Hin. apply Hx. apply in_map_iff in Hin as [[a b] [<- Hin]]. apply in_combine_l in Hin. exact Hin.
Qed.


Lemma upd_upd : forall {X} (f g : X -> X) i l,
  update_nth i f (update_nth i g l) = update_nth i (fun x => f (g x)) l.
Proof.
  intros X f g i l. revert i. induction l as [| x l IH]; intros [| i]; try reflexivity.
  - rewrite !upd_0. reflexivity.
  - rewrite !upd_S. f_equal. apply IH.
Qed.

(** Attacks name each Walker once. *)
Lemma attack_nodup : forall l ws, In ws (subsets (indices_where (fun _ w => can_pump w) l)) -> NoDup ws.
Proof.
  intros l ws Hin. eapply Preservation.sublist_NoDup; [apply Preservation.subsets_sublist; exact Hin |].
  exact (proj1 (Preservation.indices_where_below _ l)).
Qed.

Section SaturationA.

(** A's BIG size, B's saturation size, B's Thopter limit, A's Thopter cut,
    and B's life in certificate states. *)
Variables K Hb ott tt : nat.
Hypothesis HbK : Hb < K.
Hypothesis Hb1 : 1 <= Hb.

Notation big_rel := (big_rel K).
Notation bigs := (bigs K).

(** ** A's Walkers

    [bigA n] packs [sideA_rel]'s three facts about A's Walkers. *)

Definition bigA (n : nat) (l l' : list walker) : Prop :=
  Forall2 (big_rel n) l l' /\ (Forall (fun w => w.(counters) <> K) l -> n = 0) /\ bigs l <= 1.

Definition kst (w : walker) : bool := Nat.eqb w.(counters) K.

Lemma bigs_cons : forall x l, bigs (x :: l) = (if kst x then 1 else 0) + bigs l.
Proof. intros x l. unfold CheckerA.bigs, kst. cbn [filter]. destruct (Nat.eqb _ _); reflexivity. Qed.

Lemma bigs_kst : forall l l', map kst l = map kst l' -> bigs l = bigs l'.
Proof.
  induction l as [| x l IH]; intros [| y l'] E; cbn in E; try discriminate; [reflexivity |].
  injection E as E1 E2. rewrite !bigs_cons, E1, (IH l' E2). reflexivity.
Qed.

Lemma nobig_kst : forall l l', map kst l = map kst l' ->
  Forall (fun w => w.(counters) <> K) l' -> Forall (fun w => w.(counters) <> K) l.
Proof.
  induction l as [| x l IH]; intros [| y l'] E Hf; cbn in E; try discriminate; [constructor |].
  injection E as E1 E2. inversion Hf as [| ? ? Hy Hl]; subst. constructor; [| exact (IH l' E2 Hl)].
  unfold kst in E1. intros Ex. apply Hy. apply Nat.eqb_eq. rewrite <- E1. apply Nat.eqb_eq. exact Ex.
Qed.

Lemma nobig_bigs : forall l, Forall (fun w => w.(counters) <> K) l -> bigs l = 0.
Proof.
  intros l Hf. induction Hf as [| x l Hx _ IH]; [reflexivity |].
  rewrite bigs_cons. unfold kst. destruct (Nat.eqb_spec (counters x) K); [contradiction | exact IH].
Qed.

Lemma bigs0_nobig : forall l, bigs l = 0 -> Forall (fun w => w.(counters) <> K) l.
Proof.
  induction l as [| x l IH]; intros E; constructor; rewrite bigs_cons in E; unfold kst in E;
    destruct (Nat.eqb_spec (counters x) K); try discriminate; auto.
Qed.

Lemma nth_K_bigs : forall l i, nth i (map counters l) 0 = K -> 1 <= bigs l.
Proof.
  induction l as [| x l IH]; intros [| i] Hi; cbn in Hi; try lia; rewrite bigs_cons.
  - unfold kst. rewrite Hi, Nat.eqb_refl. lia.
  - specialize (IH i Hi). lia.
Qed.

Lemma bigs_upd_le : forall f i l, bigs (update_nth i f l) <= S (bigs l).
Proof.
  intros f i l. revert i. induction l as [| x l IH]; intros [| i]; try (cbn; lia).
  - rewrite upd_0, !bigs_cons. destruct (kst (f x)), (kst x); lia.
  - rewrite upd_S, !bigs_cons. specialize (IH i). lia.
Qed.

Lemma bigA_kst : forall n l l' k k', bigA n l l' -> map kst k = map kst l ->
  Forall2 (big_rel n) k k' -> bigA n k k'.
Proof.
  intros n l l' k k' (_ & Hn & Hbg) E Hk. split; [exact Hk |]. split.
  - intros Hf. apply Hn. apply (nobig_kst l k); [symmetry; exact E | exact Hf].
  - rewrite (bigs_kst k l E). exact Hbg.
Qed.

Lemma F2_big_change : forall n n' l l', Forall2 (big_rel n) l l' ->
  Forall (fun w => w.(counters) <> K) l -> Forall2 (big_rel n') l l'.
Proof.
  intros n n' l l' Hl Hf. induction Hl as [| x y l l' Hxy Hl IH]; constructor; inversion Hf; subst; auto.
  destruct Hxy as (E1 & E2 & [(E3 & E4) | (E3 & E4)]); [contradiction |]. repeat split; auto.
Qed.

Lemma big_pump : forall n i l l', Forall2 (big_rel n) l l' -> bigs l <= 1 -> nth i (map counters l) 0 = K ->
  Forall2 (big_rel (S n)) (update_nth i (fun x => mkWalker K (pump_walker x).(wtapped) (pump_walker x).(sick)) l)
                          (update_nth i pump_walker l').
Proof.
  intros n i l l' Hl. revert i.
  induction Hl as [| x y l l' Hxy Hl IH]; intros [| i] Hbg Hi; cbn in Hi; try lia.
  - rewrite !upd_0. rewrite bigs_cons in Hbg. unfold kst in Hbg. rewrite Hi, Nat.eqb_refl in Hbg.
    constructor.
    + destruct Hxy as (E1 & E2 & [(E3 & E4) | (E3 & E4)]); [| lia].
      unfold CheckerA.big_rel, pump_walker. cbn. rewrite E4. repeat split; auto; try (left; split; [reflexivity | lia]).
    + apply (F2_big_change n); [exact Hl |]. apply bigs0_nobig. lia.
  - rewrite !upd_S. pose proof (nth_K_bigs l i Hi) as H1. rewrite bigs_cons in Hbg. constructor.
    + destruct (kst x) eqn:Ex; [lia |]. unfold kst in Ex. apply Nat.eqb_neq in Ex.
      destruct Hxy as (E1 & E2 & [(E3 & E4) | (E3 & E4)]); [contradiction |]. repeat split; auto.
    + apply IH; [lia | exact Hi].
Qed.

Lemma bigA_pump_big : forall n i l l', bigA n l l' -> nth i (map counters l) 0 = K ->
  bigA (S n) (update_nth i (fun w => mkWalker K w.(wtapped) w.(sick)) (update_nth i pump_walker l))
             (update_nth i pump_walker l').
Proof.
  intros n i l l' (Hl & Hn & Hbg) Hi. rewrite upd_upd.
  assert (E : map kst (update_nth i (fun x => mkWalker K (pump_walker x).(wtapped) (pump_walker x).(sick)) l) = map kst l).
  { apply map_upd_same. intros x Ex. pose proof (nth_map_error counters l i x Ex) as Ec. rewrite Hi in Ec.
    unfold kst. cbn. rewrite <- Ec, Nat.eqb_refl. reflexivity. }
  split; [apply big_pump; assumption |]. split.
  - intros Hf. exfalso. apply (nobig_kst l _ (eq_sym E)) in Hf. apply nobig_bigs in Hf.
    pose proof (nth_K_bigs l i Hi). lia.
  - rewrite (bigs_kst _ _ E). exact Hbg.
Qed.

Lemma bigA_pump_create : forall n i l l', bigA n l l' -> bigs l = 0 ->
  bigA 0 (update_nth i pump_walker l) (update_nth i pump_walker l').
Proof.
  intros n i l l' (Hl & Hn & Hbg) H0. pose proof (bigs0_nobig l H0) as Hf.
  split; [| split].
  - apply F2_upd; [apply (F2_big_change n 0); assumption |].
    intros x y Ex (E1 & E2 & [(E3 & E4) | (E3 & E4)]).
    + exfalso. rewrite Forall_forall in Hf. exact (Hf x (nth_error_In _ _ Ex) E3).
    + unfold CheckerA.big_rel, pump_walker; cbn. rewrite E4. repeat split; auto.
      destruct (Nat.eq_dec (S (counters x)) K); [left | right]; lia.
  - intros _. reflexivity.
  - pose proof (bigs_upd_le pump_walker i l). lia.
Qed.

Lemma bigA_pump_small : forall n i l l', bigA n l l' ->
  nth i (map counters l) 0 <> K -> S (nth i (map counters l) 0) <> K ->
  bigA n (update_nth i pump_walker l) (update_nth i pump_walker l').
Proof.
  intros n i l l' HA Hi Hs. pose proof HA as (Hl & _ & _). apply (bigA_kst n l l'); [exact HA | |].
  - apply map_upd_same. intros x Ex. rewrite (nth_map_error counters l i x Ex) in Hi, Hs. unfold kst, pump_walker. cbn [counters].
    destruct (Nat.eqb_spec (S (counters x)) K), (Nat.eqb_spec (counters x) K); try reflexivity; contradiction.
  - apply F2_upd; [exact Hl |]. intros x y Ex Hxy. rewrite (nth_map_error counters l i x Ex) in Hi, Hs.
    destruct Hxy as (E1 & E2 & [(E3 & E4) | (E3 & E4)]); [contradiction |].
    unfold CheckerA.big_rel, pump_walker; cbn. rewrite E4. repeat split; auto. right. lia.
Qed.

Lemma bigA_taps : forall n ws l l', bigA n l l' ->
  bigA n (fold_right (fun i l => update_nth i tap_walker l) l ws)
         (fold_right (fun i l => update_nth i tap_walker l) l' ws).
Proof.
  intros n ws l l' HA. induction ws as [| i ws IH]; cbn [fold_right]; [exact HA |].
  pose proof IH as (Hl & _ & _). apply (bigA_kst n _ _ _ _ IH).
  - apply map_upd_same. intros x _. reflexivity.
  - apply F2_upd; [exact Hl |]. intros x y _ (E1 & E2 & E3). unfold CheckerA.big_rel, tap_walker; cbn. auto.
Qed.

Lemma bigA_untap : forall n l l', bigA n l l' ->
  bigA n (map (fun w => mkWalker w.(counters) false false) l) (map (fun w => mkWalker w.(counters) false false) l').
Proof.
  intros n l l' HA. pose proof HA as (Hl & _ & _). apply (bigA_kst n _ _ _ _ HA).
  - rewrite map_map. apply map_ext. reflexivity.
  - clear HA. induction Hl as [| x y l l' (E1 & E2 & E3) _ IH]; cbn [map]; [constructor |].
    constructor; [| exact IH]. unfold CheckerA.big_rel; cbn. auto.
Qed.

Lemma bigA_snoc : forall n l l' x, bigA n l l' -> x < K ->
  bigA n (l ++ [mkWalker x false true]) (l' ++ [mkWalker x false true]).
Proof.
  intros n l l' x (Hl & Hn & Hbg) Hx. split; [| split].
  - apply Forall2_app; [exact Hl |]. constructor; [| constructor].
    unfold CheckerA.big_rel; cbn. repeat split; auto.
  - intros Hf. apply Forall_app in Hf as [Hf _]. apply Hn. exact Hf.
  - unfold CheckerA.bigs in *. rewrite filter_app, length_app. cbn [filter counters].
    destruct (Nat.eqb_spec x K); [lia |]. cbn [length]. lia.
Qed.

Lemma bigA_remove : forall n dead l l', bigA n l l' ->
  (forall i, In i dead -> nth i (map counters l) 0 <> K) ->
  bigA n (remove_indices dead l) (remove_indices dead l').
Proof.
  intros n dead l l' (Hl & Hn & Hbg) Hd. split; [| split].
  - apply F2_remove_gen. exact Hl.
  - intros Hf. apply Hn. apply Forall_forall. intros x Hx Ex.
    apply In_nth_error in Hx as [i Ei].
    assert (Hi : ~ In i dead).
    { intros Hi. apply (Hd i Hi). rewrite (nth_map_error counters l i x Ei). exact Ex. }
    pose proof (remove_keep dead l i x Ei Hi) as Hk. rewrite Forall_forall in Hf. exact (Hf x Hk Ex).
  - unfold CheckerA.bigs in *. pose proof (remove_sublist_len (fun w => Nat.eqb w.(counters) K) dead l). lia.
Qed.

Lemma big_power : forall n l l' i, Forall2 (big_rel n) l l' ->
  (nth i (map counters l) 0 = K /\ nth i (map counters l') 0 = K + n) \/
  (nth i (map counters l) 0 < K /\ nth i (map counters l') 0 = nth i (map counters l) 0).
Proof.
  intros n l l' i Hl. revert i.
  induction Hl as [| x y l l' (_ & _ & Hc) _ IH]; intros [| i]; cbn; [right; lia | right; lia | exact Hc | apply IH].
Qed.

Lemma big_power_eq : forall n l l' i, Forall2 (big_rel n) l l' -> nth i (map counters l) 0 <> K ->
  nth i (map counters l') 0 = nth i (map counters l) 0.
Proof. intros n l l' i Hl Hi. destruct (big_power n l l' i Hl) as [[E _] | [_ E]]; [contradiction | exact E]. Qed.

(** ** Sides *)

(** A's side, with A's Thopters equal: [sideA_rel] lets the real side have
    more. *)
Definition sa (n : nat) (a a' : side) : Prop :=
  a.(life) = a'.(life) /\ a.(city) = a'.(city) /\ a.(pool) = a'.(pool) /\
  a.(hand_w) = a'.(hand_w) /\ a.(hand_e) = false /\ a'.(hand_e) = false /\
  a.(elixir_bf) = false /\ a'.(elixir_bf) = false /\
  Forall (eq CWalker) a.(library) /\ a.(library) = a'.(library) /\
  bigA n a.(bf) a'.(bf) /\ a.(thop_u) = a'.(thop_u) /\ a.(thop_t) = a'.(thop_t).

Ltac sa_destruct HA :=
  let Hl := fresh "Hl" in let Hc := fresh "Hc" in let Hp := fresh "Hp" in
  let Hw := fresh "Hw" in let He := fresh "He" in let He' := fresh "He'" in
  let Hx := fresh "Hx" in let Hx' := fresh "Hx'" in let Hlib := fresh "Hlib" in
  let Elib := fresh "Elib" in let Hbf := fresh "Hbf" in let Hu := fresh "Hu" in
  let Ht := fresh "Ht" in
  destruct HA as (Hl & Hc & Hp & Hw & He & He' & Hx & Hx' & Hlib & Elib & Hbf & Hu & Ht).

Lemma sa_fields : forall n l c p hw he bf e tu t2 lib g l' c' p' hw' he' bf' e' tu' t2' lib' g',
  l = l' -> c = c' -> p = p' -> hw = hw' -> he = false -> he' = false -> e = false -> e' = false ->
  Forall (eq CWalker) lib -> lib = lib' -> bigA n bf bf' -> tu = tu' -> t2 = t2' ->
  sa n (mkSide l c p hw he bf e tu t2 lib g) (mkSide l' c' p' hw' he' bf' e' tu' t2' lib' g').
Proof. intros. unfold sa; cbn. repeat (split; [assumption |]); assumption. Qed.

Ltac sa_solve HA :=
  sa_destruct HA; cbn in *; apply sa_fields; try assumption; try congruence.

Lemma sa_bf : forall n a a', sa n a a' -> bigA n a.(bf) a'.(bf).
Proof. intros n a a' HA. sa_destruct HA. exact Hbf. Qed.

Lemma sa_set_pool : forall n x a a', sa n a a' -> sa n (set_pool x a) (set_pool x a').
Proof. intros n x [] [] HA. unfold set_pool. sa_solve HA. Qed.

Lemma sa_set_city : forall n x a a', sa n a a' -> sa n (set_city x a) (set_city x a').
Proof. intros n x [] [] HA. unfold set_city. sa_solve HA. Qed.

Lemma sa_set_life : forall n x a a', sa n a a' -> sa n (set_life x a) (set_life x a').
Proof. intros n x [] [] HA. unfold set_life. sa_solve HA. Qed.

Lemma sa_set_thop_t : forall n x a a', sa n a a' -> sa n (set_thop_t x a) (set_thop_t x a').
Proof. intros n x [] [] HA. unfold set_thop_t. sa_solve HA. Qed.

Lemma sa_set_thop_u : forall n x a a', sa n a a' -> sa n (set_thop_u x a) (set_thop_u x a').
Proof. intros n x [] [] HA. unfold set_thop_u. sa_solve HA. Qed.

Lemma sa_set_bf : forall n n' l l' a a', sa n a a' -> bigA n' l l' -> sa n' (set_bf l a) (set_bf l' a').
Proof. intros n n' l l' [] [] HA Hl. unfold set_bf. sa_solve HA. Qed.

Lemma sa_pay : forall n x a a', sa n a a' ->
  match pay x a, pay x a' with
  | Some y, Some y' => sa n y y'
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros n x a a' HA. pose proof HA as HA'. sa_destruct HA'. unfold pay. rewrite Hp, Hc.
  destruct (x <=? pool a'); [apply sa_set_pool; exact HA |].
  destruct (city a' && (x <=? pool a' + 2)); [| exact I].
  apply sa_set_pool, sa_set_city. exact HA.
Qed.

Lemma sa_untap : forall n a a', sa n a a' -> sa n (untap_side a) (untap_side a').
Proof.
  intros n [] [] HA. pose proof (sa_bf _ _ _ HA) as Hba.
  unfold untap_side, set_thop_t, set_thop_u, set_bf, set_city.
  sa_solve HA. apply bigA_untap; exact Hba.
Qed.

Lemma sa_draw : forall n a a', sa n a a' -> sa n (draw a) (draw a').
Proof.
  intros n [] [] HA. pose proof HA as HA'. sa_destruct HA'. cbn in *. subst library0.
  unfold draw; cbn. destruct library as [| [] r].
  - sa_solve HA.
  - unfold set_library, set_hand_w. sa_solve HA. inversion Hlib; assumption.
  - inversion Hlib. discriminate.
Qed.

Lemma sa_cast_walker : forall n a a' x, sa n a a' -> x < K ->
  sa n (match x with
        | 0 => set_gy_w (S (set_hand_w (pred a.(hand_w)) a).(gy_w)) (set_hand_w (pred a.(hand_w)) a)
        | _ => set_bf ((set_hand_w (pred a.(hand_w)) a).(bf) ++ [mkWalker x false true]) (set_hand_w (pred a.(hand_w)) a)
        end)
       (match x with
        | 0 => set_gy_w (S (set_hand_w (pred a'.(hand_w)) a').(gy_w)) (set_hand_w (pred a'.(hand_w)) a')
        | _ => set_bf ((set_hand_w (pred a'.(hand_w)) a').(bf) ++ [mkWalker x false true]) (set_hand_w (pred a'.(hand_w)) a')
        end).
Proof.
  intros n [] [] [| x] HA Hx; pose proof (sa_bf _ _ _ HA) as Hba; unfold set_gy_w, set_hand_w, set_bf; sa_solve HA.
  apply bigA_snoc; assumption.
Qed.

Lemma sa_attack : forall n ws k a a', sa n a a' ->
  sa n
    (set_thop_t (a.(thop_t) + k) (set_thop_u (a.(thop_u) - k)
      (set_bf (fold_right (fun i l => update_nth i tap_walker l) a.(bf) ws) a)))
    (set_thop_t (a'.(thop_t) + k) (set_thop_u (a'.(thop_u) - k)
      (set_bf (fold_right (fun i l => update_nth i tap_walker l) a'.(bf) ws) a'))).
Proof.
  intros n ws k [] [] HA. pose proof (sa_bf _ _ _ HA) as Hba.
  unfold set_thop_t, set_thop_u, set_bf. sa_solve HA. apply bigA_taps. exact Hba.
Qed.

(** Burying A Walkers that are not BIG. *)
Lemma sa_bury : forall n dead a a', sa n a a' ->
  (forall i, In i dead -> walker_power a i <> K) ->
  sa n (bury dead a) (bury dead a').
Proof.
  intros n dead a a' HA Hd. pose proof (sa_bf _ _ _ HA) as Hba.
  assert (Es : list_sum (map (walker_power a) dead) = list_sum (map (walker_power a') dead)).
  { f_equal. apply map_ext_in. intros i Hi. unfold walker_power. symmetry.
    apply (big_power_eq n); [exact (proj1 Hba) | exact (Hd i Hi)]. }
  unfold bury. rewrite Es.
  assert (Hbr : bigA n (remove_indices dead a.(bf)) (remove_indices dead a'.(bf)))
    by (apply bigA_remove; [exact Hba | exact Hd]).
  clear Es Hd Hba. destruct a, a'. unfold set_gy_w, set_thop_u, set_bf. sa_solve HA.
Qed.

(** B's side: [sideB_rel], and B's real life is at least 1 and [D] more
    than the certificate's. *)
Definition sb (D : Z) (b b' : side) : Prop :=
  sideB_rel Hb b b' /\ 1 <= b'.(life) /\ Z.of_nat b'.(life) = (Z.of_nat b.(life) + D)%Z.

Lemma sbr_get : forall b b', sideB_rel Hb b b' ->
  Forall2 (walker_rel Hb) b.(bf) b'.(bf) /\ b.(city) = b'.(city) /\ b.(pool) = b'.(pool) /\
  b.(hand_w) = b'.(hand_w) /\ b.(hand_e) = b'.(hand_e) /\ b.(elixir_bf) = b'.(elixir_bf) /\
  b.(thop_u) = b'.(thop_u) /\ b.(thop_t) = b'.(thop_t) /\ b.(library) = b'.(library) /\
  b.(gy_w) = b'.(gy_w).
Proof.
  intros [] [] (Hw & E). unfold set_bf, set_life in E. cbn in *. injection E. intros. subst.
  repeat split; auto.
Qed.

Ltac sb_destruct HB :=
  let Hw := fresh "Hbw" in let H1 := fresh "Hl1" in let HD := fresh "HD" in
  let Hc := fresh "Hbc" in let Hp := fresh "Hbp" in let Hh := fresh "Hbh" in
  let He := fresh "Hbe" in let Hx := fresh "Hbx" in let Hu := fresh "Hbu" in
  let Ht := fresh "Hbt" in let Hlb := fresh "Hblib" in let Hg := fresh "Hbg" in
  let Hr := fresh "Hr" in
  destruct HB as (Hr & H1 & HD);
  apply sbr_get in Hr; destruct Hr as (Hw & Hc & Hp & Hh & He & Hx & Hu & Ht & Hlb & Hg).

Lemma sb_fields : forall D l c p hw he bf e tu t2 lib g l' c' p' hw' he' bf' e' tu' t2' lib' g',
  1 <= l' -> Z.of_nat l' = (Z.of_nat l + D)%Z -> c = c' -> p = p' -> hw = hw' -> he = he' ->
  Forall2 (walker_rel Hb) bf bf' -> e = e' -> tu = tu' -> t2 = t2' -> lib = lib' -> g = g' ->
  sb D (mkSide l c p hw he bf e tu t2 lib g) (mkSide l' c' p' hw' he' bf' e' tu' t2' lib' g').
Proof.
  intros. subst. unfold sb, CheckerA.sideB_rel, set_bf, set_life; cbn.
  split; [split; [assumption | reflexivity] |]. split; assumption.
Qed.

Ltac sb_solve HB :=
  sb_destruct HB; cbn in *; apply sb_fields; try assumption; try congruence; try lia.

Lemma sb_bf : forall D b b', sb D b b' -> Forall2 (walker_rel Hb) b.(bf) b'.(bf).
Proof. intros D b b' HB. sb_destruct HB. exact Hbw. Qed.

Lemma sb_set_pool : forall D x b b', sb D b b' -> sb D (set_pool x b) (set_pool x b').
Proof. intros D x [] [] HB. unfold set_pool. sb_solve HB. Qed.

Lemma sb_set_city : forall D x b b', sb D b b' -> sb D (set_city x b) (set_city x b').
Proof. intros D x [] [] HB. unfold set_city. sb_solve HB. Qed.

Lemma sb_set_thop_t : forall D x b b', sb D b b' -> sb D (set_thop_t x b) (set_thop_t x b').
Proof. intros D x [] [] HB. unfold set_thop_t. sb_solve HB. Qed.

Lemma sb_set_thop_u : forall D x b b', sb D b b' -> sb D (set_thop_u x b) (set_thop_u x b').
Proof. intros D x [] [] HB. unfold set_thop_u. sb_solve HB. Qed.

Lemma sb_set_library : forall D x b b', sb D b b' -> sb D (set_library x b) (set_library x b').
Proof. intros D x [] [] HB. unfold set_library. sb_solve HB. Qed.

Lemma sb_pay : forall D x b b', sb D b b' ->
  match pay x b, pay x b' with
  | Some y, Some y' => sb D y y'
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros D x b b' HB. pose proof HB as HB'. sb_destruct HB'. unfold pay. rewrite Hbp, Hbc.
  destruct (x <=? pool b'); [apply sb_set_pool; exact HB |].
  destruct (city b' && (x <=? pool b' + 2)); [| exact I].
  apply sb_set_pool, sb_set_city. exact HB.
Qed.

Lemma sb_untap : forall D b b', sb D b b' -> sb D (untap_side b) (untap_side b').
Proof.
  intros D [] [] HB. pose proof (sb_bf _ _ _ HB) as Hw.
  unfold untap_side, set_thop_t, set_thop_u, set_bf, set_city.
  sb_solve HB. apply Saturation.F2_untap. exact Hw.
Qed.

Lemma sb_draw : forall D b b', sb D b b' -> sb D (draw b) (draw b').
Proof.
  intros D [] [] HB. pose proof HB as HB'. sb_destruct HB'. cbn in *. subst library0.
  unfold draw; cbn. destruct library as [| [] r]; unfold set_library, set_hand_w, set_hand_e; sb_solve HB.
Qed.

Lemma sb_pump : forall D i b b', sb D b b' ->
  sb D (set_bf (update_nth i pump_walker b.(bf)) b) (set_bf (update_nth i pump_walker b'.(bf)) b').
Proof.
  intros D i [] [] HB. pose proof (sb_bf _ _ _ HB) as Hw. unfold set_bf. sb_solve HB.
  apply Saturation.F2_update; [exact Hw | apply Saturation.walker_rel_pump].
Qed.

Lemma sb_elixir : forall D b b', sb D b b' ->
  sb D (set_gy_w 0 (set_library [] (set_elixir_bf false (set_life (b.(life) + 5) b))))
       (set_gy_w 0 (set_library [] (set_elixir_bf false (set_life (b'.(life) + 5) b')))).
Proof.
  intros D [] [] HB. pose proof (sb_bf _ _ _ HB) as Hw.
  unfold set_gy_w, set_library, set_elixir_bf, set_life. sb_solve HB.
Qed.

Lemma sb_cast_walker : forall D b b' x, sb D b b' ->
  sb D (match x with
        | 0 => set_gy_w (S (set_hand_w (pred b.(hand_w)) b).(gy_w)) (set_hand_w (pred b.(hand_w)) b)
        | _ => set_bf ((set_hand_w (pred b.(hand_w)) b).(bf) ++ [mkWalker x false true]) (set_hand_w (pred b.(hand_w)) b)
        end)
       (match x with
        | 0 => set_gy_w (S (set_hand_w (pred b'.(hand_w)) b').(gy_w)) (set_hand_w (pred b'.(hand_w)) b')
        | _ => set_bf ((set_hand_w (pred b'.(hand_w)) b').(bf) ++ [mkWalker x false true]) (set_hand_w (pred b'.(hand_w)) b')
        end).
Proof.
  intros D [] [] [| x] HB; pose proof (sb_bf _ _ _ HB) as Hw; unfold set_gy_w, set_hand_w, set_bf; sb_solve HB.
  apply Saturation.F2_snoc. exact Hw.
Qed.

Lemma sb_cast_elixir : forall D b b', sb D b b' ->
  sb D (set_elixir_bf true (set_hand_e false b)) (set_elixir_bf true (set_hand_e false b')).
Proof. intros D [] [] HB. unfold set_elixir_bf, set_hand_e. sb_solve HB. Qed.

Lemma sb_attack : forall D ws k b b', sb D b b' ->
  sb D
    (set_thop_t (b.(thop_t) + k) (set_thop_u (b.(thop_u) - k)
      (set_bf (fold_right (fun i l => update_nth i tap_walker l) b.(bf) ws) b)))
    (set_thop_t (b'.(thop_t) + k) (set_thop_u (b'.(thop_u) - k)
      (set_bf (fold_right (fun i l => update_nth i tap_walker l) b'.(bf) ws) b'))).
Proof.
  intros D ws k [] [] HB. pose proof (sb_bf _ _ _ HB) as Hw.
  unfold set_thop_t, set_thop_u, set_bf. sb_solve HB. apply Saturation.F2_taps. exact Hw.
Qed.

(** Burying B Walkers whose sizes agree. *)
Lemma sb_bury : forall D dead b b', sb D b b' ->
  (forall i, In i dead -> walker_power b i = walker_power b' i) ->
  sb D (bury dead b) (bury dead b').
Proof.
  intros D dead b b' HB Hd. pose proof (sb_bf _ _ _ HB) as Hw.
  assert (Es : list_sum (map (walker_power b) dead) = list_sum (map (walker_power b') dead))
    by (f_equal; apply map_ext_in; exact Hd).
  unfold bury. rewrite Es. clear Es Hd.
  destruct b, b'. unfold set_gy_w, set_thop_u, set_bf. sb_solve HB. apply Saturation.F2_remove. exact Hw.
Qed.

(** Combat damage to B: the offset moves by the difference. *)
Lemma sb_damage : forall D D' x x' b b', sb D b b' -> x < b.(life) -> x' < b'.(life) ->
  D' = (D - (Z.of_nat x' - Z.of_nat x))%Z ->
  sb D' (set_life (b.(life) - x) b) (set_life (b'.(life) - x') b').
Proof. intros D D' x x' [] [] HB H1 H2 ->. unfold set_life. cbn in *. sb_solve HB. Qed.

(** ** The relation [RB] *)

(** As [RA], but with A's Thopters equal and B's real life [D] more than
    the certificate's. *)
Definition RB (n : nat) (D : Z) (s u : state) : Prop :=
  s.(active) = u.(active) /\ s.(first_turn) = u.(first_turn) /\
  s.(cmb) = u.(cmb) /\ s.(pend) = u.(pend) /\ no_a_shuffle s.(pend) /\
  sa n s.(sideA) u.(sideA) /\ sb D s.(sideB) u.(sideB) /\ NoDup s.(cmb).(atk).

Lemma RB_intro : forall n D act ft a a' b b' c pd, no_a_shuffle pd -> sa n a a' -> sb D b b' ->
  NoDup c.(atk) -> RB n D (mkState act ft a b c pd) (mkState act ft a' b' c pd).
Proof.
  intros. unfold RB; cbn [Model.active Model.first_turn Model.cmb Model.pend Model.sideA Model.sideB].
  repeat (split; [reflexivity |]). auto.
Qed.

Ltac rb_cbn := cbn [Model.active Model.first_turn Model.cmb Model.pend Model.sideA Model.sideB] in *.

Ltac rb_destruct HR :=
  let E1 := fresh "E1" in let E2 := fresh "E2" in let E3 := fresh "E3" in let E4 := fresh "E4" in
  let Hn := fresh "Hn" in let HA := fresh "HA" in let HB := fresh "HB" in let Hd := fresh "Hd" in
  destruct HR as (E1 & E2 & E3 & E4 & Hn & HA & HB & Hd).

Lemma RB_getA : forall n D s u, RB n D s u -> sa n (get_side PA s) (get_side PA u).
Proof. intros n D s u HR. rb_destruct HR. exact HA. Qed.

Lemma RB_getB : forall n D s u, RB n D s u -> sb D (get_side PB s) (get_side PB u).
Proof. intros n D s u HR. rb_destruct HR. exact HB. Qed.

Lemma RB_set_pend : forall n D pd s u, no_a_shuffle pd -> RB n D s u -> RB n D (set_pend pd s) (set_pend pd u).
Proof.
  intros n D pd [act ft a b c pd0] [act' ft' a' b' c' pd'] Hpd HR. rb_destruct HR.
  rb_cbn. subst. unfold set_pend. apply RB_intro; assumption.
Qed.

Lemma RB_set_cmb : forall n D c s u, NoDup c.(atk) -> RB n D s u -> RB n D (set_cmb c s) (set_cmb c u).
Proof.
  intros n D c0 [act ft a b c pd] [act' ft' a' b' c' pd'] Hc HR. rb_destruct HR.
  rb_cbn. subst. unfold set_cmb. apply RB_intro; assumption.
Qed.

Lemma RB_setA : forall n n' D x y s u, sa n' x y -> RB n D s u -> RB n' D (set_side PA x s) (set_side PA y u).
Proof.
  intros n n' D x y [act ft a b c pd] [act' ft' a' b' c' pd'] Hxy HR. rb_destruct HR.
  rb_cbn. subst. unfold set_side. apply RB_intro; assumption.
Qed.

Lemma RB_setB : forall n D D' x y s u, sb D' x y -> RB n D s u -> RB n D' (set_side PB x s) (set_side PB y u).
Proof.
  intros n D D' x y [act ft a b c pd] [act' ft' a' b' c' pd'] Hxy HR. rb_destruct HR.
  rb_cbn. subst. unfold set_side. apply RB_intro; assumption.
Qed.

Lemma RB_mapA : forall n D f s u, (forall a a', sa n a a' -> sa n (f a) (f a')) ->
  RB n D s u -> RB n D (map_side PA f s) (map_side PA f u).
Proof. intros n D f s u Hf HR. unfold map_side. apply (RB_setA n); [apply Hf, (RB_getA n D) |]; exact HR. Qed.

Lemma RB_mapB : forall n D f s u, (forall b b', sb D b b' -> sb D (f b) (f b')) ->
  RB n D s u -> RB n D (map_side PB f s) (map_side PB f u).
Proof. intros n D f s u Hf HR. unfold map_side. apply (RB_setB n D); [apply Hf, (RB_getB n D) |]; exact HR. Qed.

Lemma RB_with_payment : forall n D x p k s u, (forall s u, RB n D s u -> RB n D (k s) (k u)) ->
  RB n D s u -> RB n D (with_payment x p s k) (with_payment x p u k).
Proof.
  intros n D x [] k s u Hk HR; unfold with_payment.
  - pose proof (sa_pay n x _ _ (RB_getA _ _ _ _ HR)) as Hp.
    destruct (pay x (get_side PA s)), (pay x (get_side PA u)); try contradiction;
      [apply Hk, (RB_setA n); assumption | exact HR].
  - pose proof (sb_pay D x _ _ (RB_getB _ _ _ _ HR)) as Hp.
    destruct (pay x (get_side PB s)), (pay x (get_side PB u)); try contradiction;
      [apply Hk, (RB_setB n D); assumption | exact HR].
Qed.

Lemma RB_end_step : forall n D st s u, RB n D s u -> RB n D (end_step st s) (end_step st u).
Proof.
  intros n D st s u HR. unfold end_step. cbv zeta.
  assert (HR' : RB n D (empty_pools s) (empty_pools u)).
  { unfold empty_pools. apply RB_mapA; [intros; apply sa_set_pool; assumption |].
    apply RB_mapB; [intros; apply sb_set_pool; assumption |]. exact HR. }
  generalize (empty_pools s) (empty_pools u) HR'. clear s u HR HR'. intros s u HR.
  pose proof HR as (E1 & E2 & E3 & _).
  rewrite <- E1, <- E2, <- E3.
  destruct st; try (apply RB_set_pend; [exact I | exact HR]).
  - destruct (first_turn s); (apply RB_set_pend; [exact I |]); [exact HR |].
    destruct (active s); [apply RB_mapA; [exact (sa_draw n) | exact HR] | apply RB_mapB; [exact (sb_draw D) | exact HR]].
  - destruct (atk (cmb s)), (atk_thop (cmb s)); apply RB_set_pend; try exact I; exact HR.
  - apply RB_set_pend; [exact I |]. apply RB_set_cmb; [constructor | exact HR].
  - unfold next_turn. cbv zeta. rewrite <- E1.
    assert (HR2 : RB n D (map_side (opp (active s)) untap_side s) (map_side (opp (active s)) untap_side u)).
    { destruct (opp (active s)); [apply RB_mapA; [exact (sa_untap n) | exact HR] | apply RB_mapB; [exact (sb_untap D) | exact HR]]. }
    destruct HR2 as (_ & _ & _ & _ & _ & HA & HB & _).
    apply RB_intro; [exact I | exact HA | exact HB | constructor].
Qed.

Lemma RB_block : forall n D wb tb tr s u, RB n D s u -> RB n D (do_block wb tb tr s) (do_block wb tb tr u).
Proof.
  intros n D wb tb tr [act ft a b c pd] [act' ft' a' b' c' pd'] HR. rb_destruct HR.
  rb_cbn. subst. unfold do_block, set_cmb, set_pend. cbn.
  match goal with |- context [if ?x then _ else _] => destruct x end;
    apply RB_intro; try exact I; assumption.
Qed.

Lemma RB_order : forall n D os s u, RB n D s u -> RB n D (do_order os s) (do_order os u).
Proof.
  intros n D os [act ft a b c pd] [act' ft' a' b' c' pd'] HR. rb_destruct HR.
  rb_cbn. subst. unfold do_order, set_cmb, set_pend. cbn. apply RB_intro; [exact I | assumption ..].
Qed.

(** ** Move lists *)

(** The parts of [RB] that the move lists read. *)
Definition RM (n : nat) (s u : state) : Prop :=
  s.(active) = u.(active) /\ s.(first_turn) = u.(first_turn) /\ s.(cmb) = u.(cmb) /\
  s.(pend) = u.(pend) /\ sa n s.(sideA) u.(sideA) /\ sideB_rel Hb s.(sideB) u.(sideB).

Lemma ready_big : forall n l l', Forall2 (big_rel n) l l' ->
  indices_where (fun _ w => can_pump w) l = indices_where (fun _ w => can_pump w) l'.
Proof.
  intros n l l' Hl. apply (Saturation.indices_where_rel _ _ _ _ _ Hl).
  intros _ [c tp sk] [c' tp' sk'] (Et & Es & _). cbn in *. unfold can_pump. cbn. congruence.
Qed.

Lemma wchoices_big : forall n k l l', Forall2 (big_rel n) l l' ->
  map (fun w => if w.(wtapped) then [None] else None :: map Some (seq 0 k)) l =
  map (fun w => if w.(wtapped) then [None] else None :: map Some (seq 0 k)) l'.
Proof.
  intros n k l l' Hl. induction Hl as [| x y l l' (Et & _) _ IH]; cbn; [reflexivity |].
  rewrite Et, IH. reflexivity.
Qed.

Lemma window_eq : forall n st p act ft a b a' b' c pd, sa n a a' -> sideB_rel Hb b b' ->
  window_moves st p (mkState act ft a b c pd) = window_moves st p (mkState act ft a' b' c pd).
Proof.
  intros n st p act ft a b a' b' c pd HA HB.
  destruct HA as (Hl & Hc & Hp & Hw & He & He' & Hx & Hx' & _ & _ & (Hbf & _) & _ & _).
  apply sbr_get in HB. destruct HB as (Hbw & Hc2 & Hp2 & Hw2 & He2 & Hx2 & _).
  unfold window_moves; destruct p; cbn [get_side Model.sideA Model.sideB Model.active].
  - rewrite (Saturation.can_pay_eq 1 a a'), (Saturation.can_pay_eq 2 a a'), (ready_big _ _ _ Hbf); auto.
    rewrite Hw, He, He', Hx, Hx'. reflexivity.
  - rewrite (Saturation.can_pay_eq 1 b b'), (Saturation.can_pay_eq 2 b b'), (Saturation.ready_rel Hb _ _ Hbw); auto.
    rewrite Hw2, He2, Hx2. reflexivity.
Qed.

(** *** Damage choices *)

Lemma big_wp : forall n a a' i, Forall2 (big_rel n) a.(bf) a'.(bf) ->
  (walker_power a i = K /\ walker_power a' i = K + n) \/
  (walker_power a i < K /\ walker_power a' i = walker_power a i).
Proof. intros n a a' i Hl. unfold walker_power. apply big_power. exact Hl. Qed.

(** A's blockers that are not BIG have their real toughness. *)
Lemma tough_A_eq : forall n a a' bs, Forall2 (big_rel n) a.(bf) a'.(bf) ->
  (forall j, In (BW j) bs -> walker_power a j <> K) ->
  map (blocker_toughness a) bs = map (blocker_toughness a') bs.
Proof.
  intros n a a' bs Hl Hj. apply map_ext_in. intros [j |] Hin; [| reflexivity]. cbn [blocker_toughness].
  destruct (big_wp n a a' j Hl) as [[E _] | [_ E]]; [exfalso; exact (Hj j Hin E) | symmetry; exact E].
Qed.

(** So do B's blockers that are not saturated. *)
Lemma tough_B_eq : forall b b' bs, Forall2 (walker_rel Hb) b.(bf) b'.(bf) ->
  (forall j, In (BW j) bs -> walker_power b j < Hb) ->
  map (blocker_toughness b) bs = map (blocker_toughness b') bs.
Proof.
  intros b b' bs Hl Hj. apply map_ext_in. intros [j |] Hin; [| reflexivity]. cbn [blocker_toughness].
  apply (Saturation.nonhuge_eq Hb); [exact Hl | exact (Hj j Hin)].
Qed.

Lemma big_A_false : forall a d l,
  existsb (fun '(i, bs) => Nat.eqb (walker_power a i) K &&
     match bs with [] => false | _ => K <=? list_sum (map (blocker_toughness d) bs) end) l = false ->
  forall i bs, In (i, bs) l -> walker_power a i = K -> bs <> [] ->
  list_sum (map (blocker_toughness d) bs) < K.
Proof.
  intros a d l Hx i bs Hin Hk Hne.
  destruct (Nat.ltb_spec (list_sum (map (blocker_toughness d) bs)) K) as [Hlt | Hge]; [exact Hlt | exfalso].
  assert (Ht : existsb (fun '(i, bs) => Nat.eqb (walker_power a i) K &&
     match bs with [] => false | _ => K <=? list_sum (map (blocker_toughness d) bs) end) l = true).
  { apply existsb_exists. exists (i, bs). split; [exact Hin |]. rewrite Hk, Nat.eqb_refl. cbn [andb].
    destruct bs; [congruence | apply Nat.leb_le; exact Hge]. }
  congruence.
Qed.

Lemma huge_exists : forall d bs j, In (BW j) bs -> Hb <= walker_power d j ->
  existsb (fun b => match b with BW j => is_huge Hb d j | BT => false end) bs = true.
Proof.
  intros d bs j Hj Hge. apply existsb_exists. exists (BW j). split; [exact Hj |].
  unfold is_huge. apply Nat.leb_le. exact Hge.
Qed.

Lemma in_tough_le : forall d bs j, In (BW j) bs -> walker_power d j <= list_sum (map (blocker_toughness d) bs).
Proof.
  intros d bs j Hj. exact (Saturation.in_le_sum (blocker_toughness d (BW j)) _ (in_map _ _ _ Hj)).
Qed.

(** When A attacks: an A attacker and its B blockers. *)
Lemma choices_A : forall n a a' b b' i bs, Forall2 (big_rel n) a.(bf) a'.(bf) ->
  Forall2 (walker_rel Hb) b.(bf) b'.(bf) ->
  (Hb <=? walker_power a i) && existsb (fun x => match x with BW j => is_huge Hb b j | BT => false end) bs = false ->
  (walker_power a i =? K) && match bs with [] => false | _ => K <=? list_sum (map (blocker_toughness b) bs) end = false ->
  kill_choices (walker_power a i) (map (blocker_toughness b) bs) =
  kill_choices (walker_power a' i) (map (blocker_toughness b') bs).
Proof.
  intros n a a' b b' i bs Hba Hbb Hi Gi.
  destruct (big_wp n a a' i Hba) as [[EK EK'] | [Hlt E]].
  - rewrite (tough_B_eq b b' bs Hbb).
    2: { intros j Hj. destruct (Nat.ltb_spec (walker_power b j) Hb) as [Hl | Hge]; [exact Hl | exfalso].
         rewrite (huge_exists b bs j Hj Hge), andb_true_r in Hi. apply Nat.leb_gt in Hi. lia. }
    destruct bs as [| x bs]; [reflexivity |].
    rewrite EK, Nat.eqb_refl in Gi. cbn [andb] in Gi. apply Nat.leb_gt in Gi.
    rewrite (tough_B_eq b b' (x :: bs) Hbb) in Gi.
    2: { intros j Hj. destruct (Nat.ltb_spec (walker_power b j) Hb) as [Hl | Hge]; [exact Hl | exfalso].
         rewrite (huge_exists b (x :: bs) j Hj Hge), andb_true_r in Hi. apply Nat.leb_gt in Hi. lia. }
    apply Saturation.kill_choices_big; [discriminate | lia | lia].
  - rewrite E. apply Saturation.kill_choices_rel. apply Saturation.Forall2_map_same.
    intros [j |] Hj; [| left; reflexivity]. cbn [blocker_toughness].
    destruct (Saturation.walker_power_rel Hb b b' j Hbb) as [Ej | (Hp & Hp')]; [left; exact Ej | right].
    destruct (Nat.ltb_spec (walker_power a i) Hb) as [Hl | Hge]; [lia | exfalso].
    rewrite (huge_exists b bs j Hj Hp), andb_true_r in Hi. apply Nat.leb_gt in Hi. lia.
Qed.

(** When B attacks: a B attacker and its A blockers. *)
Lemma choices_B : forall n a a' b b' i bs, Forall2 (big_rel n) a.(bf) a'.(bf) ->
  Forall2 (walker_rel Hb) b.(bf) b'.(bf) ->
  is_huge Hb b i && match bs with [] => true | _ => Hb <=? list_sum (map (blocker_toughness a) bs) end = false ->
  kill_choices (walker_power b i) (map (blocker_toughness a) bs) =
  kill_choices (walker_power b' i) (map (blocker_toughness a') bs).
Proof.
  intros n a a' b b' i bs Hba Hbb Hi. unfold is_huge in Hi.
  destruct (Saturation.walker_power_rel Hb b b' i Hbb) as [E | (Hp & Hp')].
  - rewrite <- E. apply Saturation.kill_choices_rel. apply Saturation.Forall2_map_same.
    intros [j |] Hj; [| left; reflexivity]. cbn [blocker_toughness].
    destruct (big_wp n a a' j Hba) as [[EK EK'] | [_ Ej]]; [right | left; symmetry; exact Ej].
    destruct (Nat.ltb_spec (walker_power b i) Hb) as [Hl | Hge]; [lia | exfalso].
    rewrite (proj2 (Nat.leb_le _ _) Hge) in Hi. cbn [andb] in Hi.
    destruct bs as [| x bs]; [destruct Hj |]. apply Nat.leb_gt in Hi.
    pose proof (in_tough_le a (x :: bs) j Hj). lia.
  - rewrite (proj2 (Nat.leb_le _ _) Hp) in Hi. cbn [andb] in Hi.
    destruct bs as [| x bs]; [discriminate |]. apply Nat.leb_gt in Hi.
    assert (Ht : forall j, In (BW j) (x :: bs) -> walker_power a j <> K).
    { intros j Hj E. pose proof (in_tough_le a (x :: bs) j Hj). lia. }
    rewrite <- (tough_A_eq n a a' (x :: bs) Hba Ht).
    apply Saturation.kill_choices_big; [discriminate | lia | lia].
Qed.

Lemma damage_eq : forall n act ft a b a' b' c, sa n a a' -> sideB_rel Hb b b' ->
  huge_event Hb (mkState act ft a b c ChooseDamage) = false ->
  big_event K (mkState act ft a b c ChooseDamage) = false ->
  damage_moves (mkState act ft a b c ChooseDamage) = damage_moves (mkState act ft a' b' c ChooseDamage).
Proof.
  intros n act ft a b a' b' c HA HB Hh Hg.
  pose proof (proj1 (sa_bf _ _ _ HA)) as Hba.
  pose proof (proj1 (sbr_get _ _ HB)) as Hbb.
  unfold damage_moves, CheckerA.huge_event, CheckerA.big_event, defender in *.
  destruct act; cbn [get_side opp Model.sideA Model.sideB Model.active Model.cmb Model.pend] in *;
    f_equal; f_equal; destruct c as [atk k blk tr]; cbn [Model.atk Model.blk] in *;
    clear k tr; revert blk Hh Hg; induction atk as [| i atk IH]; intros [| bs blk] Hh Hg;
    try reflexivity; cbn [combine map existsb] in *;
    apply orb_false_iff in Hh as (Hi & Hh); apply orb_false_iff in Hg as (Gi & Hg);
    f_equal; try (apply IH; assumption).
  - exact (choices_A n a a' b b' i bs Hba Hbb Hi Gi).
  - exact (choices_B n a a' b b' i bs Hba Hbb Hi).
Qed.

Lemma moves_eq : forall n s u, RM n s u -> huge_event Hb s = false -> big_event K s = false ->
  moves u = moves s.
Proof.
  intros n [act ft a b c pd] [act' ft' a' b' c' pd'] (E1 & E2 & E3 & E4 & HA & HB) Hh Hg.
  rb_cbn. subst act' ft' c' pd'.
  pose proof (proj1 (sa_bf _ _ _ HA)) as Hba.
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hu & _).
  pose proof (sbr_get _ _ HB) as (Hbb & _ & _ & _ & _ & _ & Hbu & _).
  unfold moves. destruct pd as [st p passed | | | | | st p cards | w].
  - symmetry. apply (window_eq n); assumption.
  - unfold attack_moves. destruct act; cbn [get_side Model.active Model.sideA Model.sideB].
    + rewrite (ready_big _ _ _ Hba), Hu. reflexivity.
    + rewrite (Saturation.ready_rel Hb _ _ Hbb), Hbu. reflexivity.
  - unfold block_moves, defender. destruct act; cbn [get_side opp Model.active Model.sideA Model.sideB Model.cmb].
    + rewrite (Saturation.wchoices_rel Hb _ _ _ Hbb), Hbu. reflexivity.
    + rewrite (wchoices_big _ _ _ _ Hba), Hu. reflexivity.
  - reflexivity.
  - symmetry. apply (damage_eq n); assumption.
  - reflexivity.
  - reflexivity.
Qed.

(** ** Combat damage *)

Lemma existsb_false_in : forall {X} (f : X -> bool) l x, existsb f l = false -> In x l -> f x = false.
Proof.
  intros X f l x E Hin. destruct (f x) eqn:Ex; [| reflexivity].
  rewrite <- E. symmetry. apply existsb_exists. eauto.
Qed.

(** A's blockers: exact, or one is BIG and both totals reach [K]. *)
Lemma tough_A_cases : forall n a a' bs, Forall2 (big_rel n) a.(bf) a'.(bf) ->
  map (blocker_toughness a) bs = map (blocker_toughness a') bs \/
  (exists j, In (BW j) bs /\ walker_power a j = K) /\
  K <= list_sum (map (blocker_toughness a) bs) /\ K <= list_sum (map (blocker_toughness a') bs).
Proof.
  intros n a a' bs Hl.
  destruct (existsb (fun x => match x with BW j => Nat.eqb (walker_power a j) K | BT => false end) bs) eqn:Ex.
  - right. apply existsb_exists in Ex as [[j |] [Hj Ej]]; [| discriminate]. apply Nat.eqb_eq in Ej.
    split; [exists j; auto |]. pose proof (in_tough_le a bs j Hj). pose proof (in_tough_le a' bs j Hj).
    destruct (big_wp n a a' j Hl) as [[_ E'] | [Hlt _]]; lia.
  - left. apply (tough_A_eq n); [exact Hl |]. intros j Hj E.
    pose proof (existsb_false_in _ bs (BW j) Ex Hj) as F. cbn beta iota in F. rewrite E, Nat.eqb_refl in F.
    discriminate.
Qed.

(** B's blockers: exact, or one is saturated and both totals reach [Hb]. *)
Lemma tough_B_cases : forall b b' bs, Forall2 (walker_rel Hb) b.(bf) b'.(bf) ->
  map (blocker_toughness b) bs = map (blocker_toughness b') bs \/
  (exists j, In (BW j) bs /\ Hb <= walker_power b j) /\
  Hb <= list_sum (map (blocker_toughness b) bs) /\ Hb <= list_sum (map (blocker_toughness b') bs).
Proof.
  intros b b' bs Hl.
  destruct (existsb (fun x => match x with BW j => is_huge Hb b j | BT => false end) bs) eqn:Ex.
  - right. apply existsb_exists in Ex as [[j |] [Hj Ej]]; [| discriminate].
    unfold is_huge in Ej. apply Nat.leb_le in Ej.
    split; [exists j; auto |]. pose proof (in_tough_le b bs j Hj). pose proof (in_tough_le b' bs j Hj).
    destruct (Saturation.walker_power_rel Hb b b' j Hl) as [E | (_ & H2)]; lia.
  - left. apply tough_B_eq; [exact Hl |]. intros j Hj.
    destruct (Nat.ltb_spec (walker_power b j) Hb) as [Hlt | Hge]; [exact Hlt | exfalso].
    rewrite (huge_exists b bs j Hj Hge) in Ex. discriminate.
Qed.

Lemma big_unique : forall l i i', bigs l <= 1 -> nth i (map counters l) 0 = K ->
  nth i' (map counters l) 0 = K -> i = i'.
Proof.
  induction l as [| x l IH]; intros [| i] [| i'] Hbg Hi Hi'; cbn in Hi, Hi'; try lia; rewrite bigs_cons in Hbg.
  - unfold kst in Hbg. rewrite Hi, Nat.eqb_refl in Hbg. pose proof (nth_K_bigs l i' Hi'). lia.
  - unfold kst in Hbg. rewrite Hi', Nat.eqb_refl in Hbg. pose proof (nth_K_bigs l i Hi). lia.
  - f_equal. apply IH; [lia | exact Hi | exact Hi'].
Qed.

(** The real unblocked damage: [n] more when the BIG Walker is unblocked.
    It attacks at most once, and it is the only BIG Walker. *)
Lemma sum_shift : forall n a a' (l : list (nat * list blocker)) (js : list nat),
  Forall2 (big_rel n) a.(bf) a'.(bf) -> bigs a.(bf) <= 1 ->
  length js = length l -> NoDup (map fst l) ->
  list_sum (map (fun '(i, bs, _) => match bs with [] => walker_power a' i | _ => 0 end) (combine l js)) =
  list_sum (map (fun '(i, bs, _) => match bs with [] => walker_power a i | _ => 0 end) (combine l js)) +
  (if existsb (fun '(i, bs) => match bs with [] => walker_power a i =? K | _ => false end) l then n else 0).
Proof.
  intros n a a' l js Hl Hbg. revert js.
  induction l as [| [i bs] l IH]; intros [| j js] Hlen Hnd; cbn in Hlen; try discriminate; [reflexivity |].
  cbn [map fst] in Hnd. apply NoDup_cons_iff in Hnd as [Hi Hnd]. cbn [combine map existsb].
  specialize (IH js ltac:(lia) Hnd). unfold list_sum in *. cbn [fold_right].
  destruct bs as [| x bs].
  - destruct (big_wp n a a' i Hl) as [[EK EK'] | [Hlt E]].
    + rewrite EK, EK', Nat.eqb_refl. cbn [orb].
      assert (Ex : existsb (fun '((i, bs) : nat * list blocker) => match bs with [] => walker_power a i =? K | _ => false end) l = false).
      { destruct (existsb (fun '((i, bs) : nat * list blocker) => match bs with [] => walker_power a i =? K | _ => false end) l) eqn:Ex;
          [exfalso | reflexivity].
        apply existsb_exists in Ex as [[i2 [| y bs2]] [Hin2 E2]]; [| discriminate]. apply Nat.eqb_eq in E2.
        apply Hi. replace i with i2 by (unfold walker_power in *; apply (big_unique a.(bf)); assumption).
        apply in_map_iff. exists (i2, []). auto. }
      rewrite Ex in IH. lia.
    + rewrite E. destruct (Nat.eqb_spec (walker_power a i) K); [lia |]. cbn [orb]. lia.
  - cbn [orb]. lia.
Qed.

Lemma unblocked_shift : forall n a a' c js, Forall2 (big_rel n) a.(bf) a'.(bf) -> bigs a.(bf) <= 1 ->
  NoDup c.(atk) -> length js = length (combine c.(atk) c.(blk)) ->
  Saturation.unblocked_of a' c (Saturation.fights_of c js) =
  Saturation.unblocked_of a c (Saturation.fights_of c js) +
  (if existsb (fun '(i, bs) => match bs with [] => walker_power a i =? K | _ => false end)
       (combine c.(atk) c.(blk)) then n else 0).
Proof.
  intros n a a' c js Hl Hbg Hnd Hlen. unfold Saturation.unblocked_of, Saturation.fights_of.
  rewrite (sum_shift n a a'); [lia | exact Hl | exact Hbg | exact Hlen | apply NoDup_fst_combine; exact Hnd].
Qed.

Lemma RB_damage : forall n D s u js, RB n D s u -> s.(pend) = ChooseDamage ->
  huge_event Hb s = false -> big_event K s = false -> In (Assign js) (damage_moves s) ->
  winner (do_damage js s) = None ->
  winner (do_damage js u) = Some PA \/
  RB n (if is_hit K s then (D - Z.of_nat n)%Z else D) (do_damage js s) (do_damage js u).
Proof.
  intros n D [act ft a b c pd] [act' ft' a' b' c' pd'] js HR Ep Hh Hg Hin Hw.
  rb_destruct HR. rb_cbn. subst act' ft' c' pd' pd.
  pose proof (sa_bf _ _ _ HA) as (Hba & _ & Hbig).
  pose proof (sb_bf _ _ _ HB) as Hbb.
  pose proof HA as (Hla & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hua & Hta).
  pose proof HB as (Hsr & _ & _). apply sbr_get in Hsr as (_ & _ & _ & _ & _ & _ & Hub & Htb & _).
  unfold damage_moves in Hin. apply in_map_iff in Hin as [js' [Ej Hin]]. injection Ej as ->.
  apply Saturation.in_product in Hin.
  pose proof (Forall2_length Hin) as Hlen. rewrite length_map, length_combine, length_map in Hlen.
  rewrite <- length_combine with (l' := blk c) in Hlen.
  change (do_damage js) with (Saturation.damage_alt js) in *.
  unfold CheckerA.huge_event, CheckerA.big_event, CheckerA.is_hit in *.
  destruct act; cbv beta iota zeta delta [Saturation.damage_alt defender get_side opp map_side set_side
    set_cmb set_pend Model.active Model.sideA Model.sideB Model.cmb Model.pend Model.first_turn] in *;
    set (fs := Saturation.fights_of c js) in *.
  - (* A attacks: its BIG attacker may hit, B's blockers may be saturated *)
    assert (Ed : Saturation.adead_of a' b' fs = Saturation.adead_of a b fs).
    { unfold Saturation.adead_of. f_equal. apply filter_ext_in. intros [[i bs] j] Hf.
      destruct bs as [| x bs]; [reflexivity |]. cbv beta iota.
      unfold fs, Saturation.fights_of in Hf. apply in_combine_l in Hf.
      destruct (big_wp n a a' i Hba) as [[EK EK'] | [Hlt Ei]].
      - assert (Et : map (blocker_toughness b) (x :: bs) = map (blocker_toughness b') (x :: bs)).
        { apply tough_B_eq; [exact Hbb |]. intros jj Hj.
          destruct (Nat.ltb_spec (walker_power b jj) Hb) as [Hl | Hge]; [exact Hl | exfalso].
          pose proof (Saturation.huge_B_false Hb a b _ Hh i _ jj Hf Hj Hge). lia. }
        pose proof (big_A_false a b _ Hg i (x :: bs) Hf EK ltac:(discriminate)) as Hs.
        rewrite <- Et, EK, EK'.
        destruct (Nat.leb_spec K (list_sum (map (blocker_toughness b) (x :: bs)))); [lia |].
        destruct (Nat.leb_spec (K + n) (list_sum (map (blocker_toughness b) (x :: bs)))); [lia | reflexivity].
      - rewrite Ei. destruct (tough_B_cases b b' (x :: bs) Hbb) as [Et | ((jj & Hj & Hge) & H1 & H2)].
        + rewrite Et. reflexivity.
        + pose proof (Saturation.huge_B_false Hb a b _ Hh i _ jj Hf Hj Hge).
          destruct (Nat.leb_spec (walker_power a i) (list_sum (map (blocker_toughness b) (x :: bs)))); [| lia].
          destruct (Nat.leb_spec (walker_power a i) (list_sum (map (blocker_toughness b') (x :: bs))));
            [reflexivity | lia]. }
    assert (Hdead : forall i, In i (Saturation.adead_of a b fs) -> walker_power a i <> K).
    { intros i Hi EK. unfold Saturation.adead_of in Hi. apply in_map_iff in Hi as [[[i' bs] j] [Ei Hi]].
      cbn in Ei. subst i'. apply filter_In in Hi as [Hf Hk]. destruct bs as [| x bs]; [discriminate |].
      cbv beta iota in Hk. apply Nat.leb_le in Hk.
      unfold fs, Saturation.fights_of in Hf. apply in_combine_l in Hf.
      pose proof (big_A_false a b _ Hg i (x :: bs) Hf EK ltac:(discriminate)). lia. }
    assert (Hkill : forall jj, In jj (flat_map (fun x => match x with BW i => [i] | BT => [] end)
                                 (Saturation.killed_of fs)) -> walker_power b jj = walker_power b' jj).
    { intros jj Hjj. apply in_flat_map in Hjj as [[jj' |] [Hk Hjj]]; [| destruct Hjj].
      destruct Hjj as [<- | []].
      unfold Saturation.killed_of in Hk. apply in_flat_map in Hk as [[[i bs] k] [Hf Hk]].
      apply (Saturation.nonhuge_eq Hb); [exact Hbb |].
      destruct (Nat.ltb_spec (walker_power b jj') Hb) as [Hl | Hge]; [exact Hl | exfalso].
      pose proof (Saturation.in_fight (fun p bs => kill_choices p (map (blocker_toughness b) bs))
                    (walker_power a) _ _ _ _ _ _ Hin Hf) as Hj.
      cbv beta in Hj. apply Saturation.kill_bound in Hj. rewrite firstn_map in Hj.
      pose proof (Saturation.in_le_sum _ _ (in_map (blocker_toughness b) _ _ Hk)) as Hle.
      cbn [blocker_toughness] in Hle.
      unfold fs, Saturation.fights_of in Hf. apply in_combine_l in Hf.
      pose proof (Saturation.huge_B_false Hb a b _ Hh i bs jj' Hf (Saturation.in_firstn _ _ _ Hk) Hge). lia. }
    pose proof (unblocked_shift n a a' c js Hba Hbig Hd Hlen) as Eu. fold fs in Eu.
    rewrite Ed.
    match type of Hw with context [if ?t then _ else _] => destruct t eqn:Ec end; [cbn in Hw; discriminate |].
    match goal with |- winner (if ?t then _ else _) = _ \/ _ => destruct t eqn:Er end; [left; reflexivity | right].
    apply Nat.leb_gt in Ec, Er. cbv beta iota.
    apply RB_intro; [exact I | | | constructor].
    + apply sa_bury; [| exact Hdead]. rewrite Hta. apply sa_set_thop_t. exact HA.
    + eapply sb_damage; [| exact Ec | exact Er |].
      * apply sb_bury; [| exact Hkill]. rewrite Hub. apply sb_set_thop_u. exact HB.
      * rewrite Eu. match goal with |- context [if ?e then _ else _] => destruct e end; lia.
  - (* B attacks: its attackers may be saturated, A's blockers may be BIG *)
    assert (Eu : Saturation.unblocked_of b' c fs = Saturation.unblocked_of b c fs).
    { unfold Saturation.unblocked_of. f_equal. f_equal. apply map_ext_in. intros [[i bs] j] Hf.
      destruct bs; [| reflexivity]. cbv beta iota.
      symmetry. apply (Saturation.nonhuge_eq Hb); [exact Hbb |].
      destruct (Nat.lt_ge_cases (walker_power b i) Hb) as [Hl | Hge]; [exact Hl | exfalso].
      unfold fs, Saturation.fights_of in Hf. apply in_combine_l in Hf.
      destruct (Saturation.huge_A_false Hb b a _ Hh i [] Hf Hge) as [N _]. congruence. }
    assert (Ed : Saturation.adead_of b' a' fs = Saturation.adead_of b a fs).
    { unfold Saturation.adead_of. f_equal. apply filter_ext_in. intros [[i bs] j] Hf.
      destruct bs as [| x bs]; [reflexivity |]. cbv beta iota.
      unfold fs, Saturation.fights_of in Hf. apply in_combine_l in Hf.
      destruct (Saturation.walker_power_rel Hb b b' i Hbb) as [Ei | (Hp & Hp')].
      - rewrite <- Ei. destruct (tough_A_cases n a a' (x :: bs) Hba) as [Et | ((jj & Hj & EK) & H1 & H2)].
        + rewrite Et. reflexivity.
        + assert (Hlt : walker_power b i < Hb).
          { destruct (Nat.lt_ge_cases (walker_power b i) Hb) as [Hl | Hge]; [exact Hl | exfalso].
            destruct (Saturation.huge_A_false Hb b a _ Hh i _ Hf Hge) as [_ Hs]. lia. }
          destruct (Nat.leb_spec (walker_power b i) (list_sum (map (blocker_toughness a) (x :: bs)))); [| lia].
          destruct (Nat.leb_spec (walker_power b i) (list_sum (map (blocker_toughness a') (x :: bs))));
            [reflexivity | lia].
      - destruct (Saturation.huge_A_false Hb b a _ Hh i _ Hf Hp) as [_ Hs].
        rewrite <- (tough_A_eq n a a' (x :: bs) Hba).
        2: { intros jj Hj E. pose proof (in_tough_le a (x :: bs) jj Hj). lia. }
        destruct (Nat.leb_spec (walker_power b i) (list_sum (map (blocker_toughness a) (x :: bs)))); [lia |].
        destruct (Nat.leb_spec (walker_power b' i) (list_sum (map (blocker_toughness a) (x :: bs))));
          [lia | reflexivity]. }
    assert (Hdead : forall i, In i (Saturation.adead_of b a fs) -> walker_power b i = walker_power b' i).
    { intros i Hi. unfold Saturation.adead_of in Hi. apply in_map_iff in Hi as [[[i' bs] j] [Ei Hi]].
      cbn in Ei. subst i'. apply filter_In in Hi as [Hf Hk]. destruct bs as [| x bs]; [discriminate |].
      cbv beta iota in Hk. apply Nat.leb_le in Hk.
      unfold fs, Saturation.fights_of in Hf. apply in_combine_l in Hf.
      apply (Saturation.nonhuge_eq Hb); [exact Hbb |].
      destruct (Nat.lt_ge_cases (walker_power b i) Hb) as [Hl | Hge]; [exact Hl | exfalso].
      destruct (Saturation.huge_A_false Hb b a _ Hh i _ Hf Hge) as [_ Hs]. lia. }
    assert (Hkill : forall jj, In jj (flat_map (fun x => match x with BW i => [i] | BT => [] end)
                                 (Saturation.killed_of fs)) -> walker_power a jj <> K).
    { intros jj Hjj EK. apply in_flat_map in Hjj as [[jj' |] [Hk Hjj]]; [| destruct Hjj].
      destruct Hjj as [<- | []].
      unfold Saturation.killed_of in Hk. apply in_flat_map in Hk as [[[i bs] k] [Hf Hk]].
      pose proof (Saturation.in_fight (fun p bs => kill_choices p (map (blocker_toughness a) bs))
                    (walker_power b) _ _ _ _ _ _ Hin Hf) as Hj.
      cbv beta in Hj. apply Saturation.kill_bound in Hj. rewrite firstn_map in Hj.
      pose proof (Saturation.in_le_sum _ _ (in_map (blocker_toughness a) _ _ Hk)) as Hle.
      cbn [blocker_toughness] in Hle.
      unfold fs, Saturation.fights_of in Hf. apply in_combine_l in Hf.
      destruct (Saturation.huge_A_false Hb b a _ Hh i bs Hf ltac:(lia)) as [_ Hs].
      pose proof (in_tough_le a bs jj' (Saturation.in_firstn _ _ _ Hk)). lia. }
    rewrite Eu, Ed.
    assert (El : forall l x sd, life (bury l (set_thop_u x sd)) = life sd) by reflexivity.
    rewrite !El in *. rewrite <- Hla in *.
    destruct (life a <=? Saturation.unblocked_of b c fs) eqn:Ec; [cbn in Hw; discriminate |].
    right. cbv beta iota.
    apply RB_intro; [exact I | | | constructor].
    + apply sa_set_life. apply sa_bury; [| exact Hkill]. rewrite Hua. apply sa_set_thop_u. exact HA.
    + apply sb_bury; [| exact Hdead]. rewrite Htb. apply sb_set_thop_t. exact HB.
Qed.

(** ** One step *)

Ltac in_split :=
  repeat match goal with
  | Hin : In _ (_ :: _) |- _ => destruct Hin as [Hin | Hin]; [try discriminate |]
  | Hin : In _ (_ ++ _) |- _ => apply in_app_iff in Hin as [Hin | Hin]
  | Hin : In _ (map _ _) |- _ => let x := fresh in apply in_map_iff in Hin as [x [Hin _]]; try discriminate
  | Hin : In _ [] |- _ => destruct Hin
  | Hin : In _ (if ?b then _ else _) |- _ => destruct b
  end.

Lemma window_pump : forall st p s i, In (Pump i) (window_moves st p s) -> can_pay 1 (get_side p s) = true.
Proof.
  intros st p s i Hin. destruct (can_pay 1 (get_side p s)) eqn:E; [reflexivity | exfalso].
  unfold window_moves in Hin. cbv zeta in Hin. rewrite E in Hin. in_split.
Qed.

Lemma window_cast : forall st p s x, In (CastWalker x) (window_moves st p s) -> x <= 1.
Proof.
  intros st p s x Hin. unfold window_moves in Hin. cbv zeta in Hin.
  repeat match goal with
  | H : In _ (_ :: _) |- _ => destruct H as [H | H]; [try (injection H as <-; lia); try discriminate |]
  | H : In _ (_ ++ _) |- _ => apply in_app_iff in H as [H | H]
  | H : In _ (map _ _) |- _ => let y := fresh in apply in_map_iff in H as [y [H _]]; discriminate
  | H : In _ [] |- _ => destruct H
  | H : In _ (if ?b then _ else _) |- _ => destruct b
  end.
Qed.

Lemma attack_in_nodup : forall s ws k, In (Attack ws k) (attack_moves s) -> NoDup ws.
Proof.
  intros s ws k Hin. unfold attack_moves in Hin. cbv zeta in Hin.
  apply in_flat_map in Hin as [ws' [Hws Hin]]. apply in_map_iff in Hin as [k' [Ek _]].
  injection Ek as E1 E2. subst ws'. exact (attack_nodup _ _ Hws).
Qed.

(** Every move but A's pumps keeps [n]; only combat damage moves [D]. *)
Lemma RB_step_plain : forall n D s u m, RB n D s u -> In m (moves s) ->
  huge_event Hb s = false -> big_event K s = false -> winner (step s m) = None ->
  (forall st bb i, s.(pend) = Window st PA bb -> m <> Pump i) ->
  winner (step u m) = Some PA \/
  RB n (if is_hit K s then (D - Z.of_nat n)%Z else D) (step s m) (step u m).
Proof.
  intros n D s u m HR Hin Hh Hg Hw Hnp.
  pose proof HR as (E1 & E2 & E3 & E4 & Hns & HA & HB & Hd).
  assert (Ehit : s.(pend) <> ChooseDamage -> is_hit K s = false).
  { intros N. unfold is_hit. destruct (pend s); try reflexivity. contradiction. }
  revert Hin Hw. unfold step, moves. rewrite <- E4.
  destruct (pend s) as [st p passed | | | | | st p cards | w] eqn:Ep, m; intros Hin Hw;
    try (exfalso; unfold damage_moves in Hin; apply in_map_iff in Hin as [? [? _]]; discriminate);
    try (rewrite Ehit by (try rewrite Ep; discriminate); right; exact HR).
  - (* Pass *)
    rewrite Ehit by (try rewrite Ep; discriminate). right.
    destruct passed; [apply RB_end_step; exact HR | apply RB_set_pend; [exact I | exact HR]].
  - (* Pump: only B's *)
    rewrite Ehit by (try rewrite Ep; discriminate). right.
    destruct p; [exfalso; exact (Hnp st passed i eq_refl eq_refl) |].
    unfold do_pump. apply RB_with_payment; [| exact HR]. intros s' u' HR'.
    apply RB_set_pend; [exact I |]. apply RB_mapB; [| exact HR'].
    intros x x' Hx. apply sb_pump. exact Hx.
  - (* ActElixir: only B has one *)
    rewrite Ehit by (try rewrite Ep; discriminate). right.
    destruct p.
    + exfalso. apply Saturation.window_elixir in Hin. cbn [get_side] in Hin.
      pose proof HA as (_ & _ & _ & _ & _ & _ & Hx & _). congruence.
    + unfold do_elixir. apply RB_with_payment; [| exact HR]. intros s' u' HR'. cbv beta zeta.
      pose proof (RB_getB _ _ _ _ HR') as HB'. pose proof HB' as (Hsr & _ & _).
      apply sbr_get in Hsr as (_ & _ & _ & _ & _ & _ & _ & _ & Elib & Egy).
      rewrite Elib, Egy. apply RB_set_pend; [exact I |]. apply (RB_setB n D); [| exact HR'].
      apply sb_elixir. exact HB'.
  - (* CastWalker *)
    rewrite Ehit by (try rewrite Ep; discriminate). right.
    pose proof (window_cast _ _ _ _ Hin) as Hx.
    unfold do_cast_walker. apply RB_with_payment; [| exact HR]. intros s' u' HR'. cbv beta zeta.
    apply RB_set_pend; [exact I |]. destruct p.
    + apply (RB_setA n); [| exact HR']. apply sa_cast_walker; [apply (RB_getA n D); exact HR' | lia].
    + apply (RB_setB n D); [| exact HR']. apply sb_cast_walker. apply (RB_getB n D). exact HR'.
  - (* CastElixir: only B has one *)
    rewrite Ehit by (try rewrite Ep; discriminate). right.
    destruct p.
    + exfalso. apply Saturation.window_cast_elixir in Hin. cbn [get_side] in Hin.
      pose proof HA as (_ & _ & _ & _ & He & _). congruence.
    + unfold do_cast_elixir. apply RB_with_payment; [| exact HR]. intros s' u' HR'.
      apply RB_set_pend; [exact I |]. apply RB_mapB; [| exact HR'].
      intros x x' Hx. apply sb_cast_elixir. exact Hx.
  - (* Attack *)
    rewrite Ehit by (try rewrite Ep; discriminate). right.
    pose proof (attack_in_nodup _ _ _ Hin) as Hnd.
    unfold do_attack. cbv zeta. rewrite <- E1. apply RB_set_pend; [exact I |].
    apply RB_set_cmb; [exact Hnd |].
    destruct (active s); [apply RB_mapA; [intros x x' Hx; apply sa_attack; exact Hx | exact HR] |
                          apply RB_mapB; [intros x x' Hx; apply sb_attack; exact Hx | exact HR]].
  - rewrite Ehit by (try rewrite Ep; discriminate). right. apply RB_block. exact HR.
  - rewrite Ehit by (try rewrite Ep; discriminate). right. apply RB_order. exact HR.
  - (* Assign *) apply RB_damage; assumption.
  - (* Arrange: only B shuffles *)
    rewrite Ehit by (try rewrite Ep; discriminate). right.
    destruct p; [exfalso; try rewrite Ep in Hns; exact Hns |].
    apply RB_set_pend; [exact I |]. apply RB_mapB; [| exact HR].
    intros x x' Hx. apply sb_set_library. exact Hx.
Qed.

(** *** A's pumps *)

Lemma pay_bf : forall k sd x, pay k sd = Some x -> x.(bf) = sd.(bf).
Proof.
  intros k sd x E. unfold pay in E. destruct (k <=? pool sd); [injection E as <-; reflexivity |].
  destruct (city sd && _); [injection E as <-; reflexivity | discriminate].
Qed.

Lemma set_bf_twice : forall l l' x, set_bf l (set_bf l' x) = set_bf l x.
Proof. intros l l' []. reflexivity. Qed.

Lemma nobig_existsb : forall l, existsb (fun w => Nat.eqb w.(counters) K) l = false -> bigs l = 0.
Proof.
  induction l as [| x l IH]; intros E; [reflexivity |]. cbn [existsb] in E. apply orb_false_iff in E as [E1 E2].
  rewrite bigs_cons. unfold kst. rewrite E1. exact (IH E2).
Qed.

Lemma sa_pump_big : forall n x y i, sa n x y -> nth i (map counters x.(bf)) 0 = K ->
  sa (S n) (set_bf (update_nth i (fun w => mkWalker K w.(wtapped) w.(sick))
                     (set_bf (update_nth i pump_walker x.(bf)) x).(bf))
                   (set_bf (update_nth i pump_walker x.(bf)) x))
           (set_bf (update_nth i pump_walker y.(bf)) y).
Proof.
  intros n x y i HA Hi. rewrite set_bf_twice.
  change (bf (set_bf (update_nth i pump_walker x.(bf)) x)) with (update_nth i pump_walker x.(bf)).
  apply (sa_set_bf n); [exact HA |]. apply bigA_pump_big; [exact (sa_bf _ _ _ HA) | exact Hi].
Qed.

Lemma sa_pump_create : forall n x y i, sa n x y -> bigs x.(bf) = 0 ->
  sa 0 (set_bf (update_nth i pump_walker x.(bf)) x) (set_bf (update_nth i pump_walker y.(bf)) y).
Proof.
  intros n x y i HA H0. apply (sa_set_bf n); [exact HA |].
  apply (bigA_pump_create n); [exact (sa_bf _ _ _ HA) | exact H0].
Qed.

Lemma sa_pump_small : forall n x y i, sa n x y ->
  nth i (map counters x.(bf)) 0 <> K -> S (nth i (map counters x.(bf)) 0) <> K ->
  sa n (set_bf (update_nth i pump_walker x.(bf)) x) (set_bf (update_nth i pump_walker y.(bf)) y).
Proof.
  intros n x y i HA H1 H2. apply (sa_set_bf n); [exact HA |].
  apply bigA_pump_small; [exact (sa_bf _ _ _ HA) | exact H1 | exact H2].
Qed.

Lemma RB_pumpA : forall n D s u st bb i, RB n D s u -> s.(pend) = Window st PA bb ->
  In (Pump i) (moves s) -> (is_create K s (Pump i) && has_big K s) = false ->
  RB (if is_pump_big K s (Pump i) then S n else if is_create K s (Pump i) then 0 else n) D
     (fix_big K s (Pump i) (step s (Pump i))) (step u (Pump i)).
Proof.
  intros n D [act ft a b c pd] [act' ft' a' b' c' pd'] st bb i HR Ep Hin Hc.
  rb_destruct HR. rb_cbn. subst act' ft' c' pd' pd.
  unfold moves in Hin. apply window_pump in Hin. cbn [get_side Model.sideA] in Hin.
  unfold fix_big, set_counters, step, do_pump, with_payment in *. unfold is_pump_big, is_create, has_big in *.
  cbn [Model.pend Model.sideA get_side] in *.
  pose proof (sa_pay n 1 a a' HA) as Hp. unfold can_pay in Hin.
  destruct (pay 1 a) as [x |] eqn:Px; [| discriminate].
  destruct (pay 1 a') as [y |] eqn:Py; [| contradiction].
  pose proof (pay_bf _ _ _ Px) as Ebf.
  cbv beta iota zeta delta [set_side map_side get_side set_pend Model.active Model.first_turn
    Model.sideA Model.sideB Model.cmb Model.pend].
  destruct (Nat.eqb_spec (walker_power a i) K) as [EK | NK].
  - apply RB_intro; auto. apply sa_pump_big; [exact Hp |]. rewrite Ebf. exact EK.
  - destruct (Nat.eqb_spec (S (walker_power a i)) K) as [EC | NC].
    + cbn [andb] in Hc. apply RB_intro; auto. apply (sa_pump_create n); [exact Hp |].
      rewrite Ebf. apply nobig_existsb. exact Hc.
    + apply RB_intro; auto. apply sa_pump_small; [exact Hp | rewrite Ebf; exact NK | rewrite Ebf; exact NC].
Qed.

Lemma not_pumpA : forall s m s', (forall st bb i, s.(pend) = Window st PA bb -> m <> Pump i) ->
  is_pump_big K s m = false /\ is_create K s m = false /\ fix_big K s m s' = s'.
Proof.
  intros s m s' Hnp. unfold fix_big, is_pump_big, is_create.
  destruct m as [| i | | | | | | | |]; try (repeat split; destruct (pend s) as [? [] ? | | | | | ? ? ? | ?]; reflexivity).
  destruct (pend s) as [st [] bb | | | | | ? ? ? | ?] eqn:Ep; try (repeat split; reflexivity).
  exfalso. exact (Hnp st bb i eq_refl eq_refl).
Qed.

Lemma RB_step : forall n D s u m, RB n D s u -> In m (moves s) ->
  huge_event Hb s = false -> big_event K s = false ->
  (is_create K s m && has_big K s) = false -> winner (step s m) = None ->
  winner (step u m) = Some PA \/
  RB (if is_pump_big K s m then S n else if is_create K s m then 0 else n)
     (if is_hit K s then (D - Z.of_nat n)%Z else D) (fix_big K s m (step s m)) (step u m).
Proof.
  intros n D s u m HR Hin Hh Hg Hc Hw.
  assert (Hcase : (exists st bb i, s.(pend) = Window st PA bb /\ m = Pump i) \/
                  (forall st bb i, s.(pend) = Window st PA bb -> m <> Pump i)).
  { destruct m as [| i | | | | | | | |]; try (right; intros; discriminate).
    destruct (pend s) as [st [] bb | | | | | ? ? ? | ?]; [left; eauto | right; intros; discriminate ..]. }
  destruct Hcase as [(st & bb & i & Ep & ->) | Hnp].
  - right. assert (Ehit : is_hit K s = false) by (unfold is_hit; rewrite Ep; reflexivity).
    rewrite Ehit. apply (RB_pumpA n D s u st bb i); assumption.
  - destruct (not_pumpA s m (step s m) Hnp) as (E1 & E2 & E3). rewrite E1, E2, E3.
    apply RB_step_plain; assumption.
Qed.

(** ** [RA] as [RB], then more A Thopters *)

(** The real state with A's Thopters cut back to the certificate's. *)
Definition thopA (s t : state) : state := more_thop PA s.(sideA).(thop_u) s.(sideA).(thop_t) t.

Lemma sideA_sa : forall n a a', sideA_rel K n a a' ->
  sa n a (set_thop_t a.(thop_t) (set_thop_u a.(thop_u) a')).
Proof.
  intros n a [] HA.
  destruct HA as (Hl & Hc & Hp & Hw & He & He' & Hx & Hx' & Hlib & Elib & Hbf & Hn & Hbg & Hu & Ht).
  unfold sa, set_thop_t, set_thop_u. cbn in *. repeat (split; [assumption |]).
  split; [exact (conj Hbf (conj Hn Hbg)) | split; reflexivity].
Qed.

Lemma RA_split : forall n s t, RA K Hb n s t ->
  RM n s (thopA s t) /\ thop_le PA (thopA s t) t /\
  (1 <= t.(sideB).(life) -> RB n (blife t - blife s)%Z s (thopA s t)).
Proof.
  intros n [act ft a b c pd] [act' ft' a' b' c' pd'] (E1 & E2 & E3 & E4 & Hn & HA & HB & Hd).
  rb_cbn. subst act' ft' c' pd'.
  pose proof (sideA_sa n a a' HA) as HSA.
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hu & Ht).
  unfold thopA, more_thop, map_side, get_side, set_side.
  cbn [Model.active Model.first_turn Model.sideA Model.sideB Model.cmb Model.pend].
  split; [| split].
  - exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj HSA HB))))).
  - exists (thop_u a'), (thop_t a'). destruct a'. cbn in *. auto.
  - intros Hl. refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj Hn (conj HSA (conj _ Hd))))))).
    split; [exact HB | split; [exact Hl |]]. unfold blife. cbn. lia.
Qed.

Lemma RA_join : forall n D x y z, RB n D x y -> thop_le PA y z ->
  RA K Hb n (norm Hb tt x) z /\ 1 <= z.(sideB).(life) /\ blife z = (blife x + D)%Z.
Proof.
  intros n D [act ft a b c pd] [act' ft' a' b' c' pd'] z HR [u [v [Hu [Hv ->]]]].
  rb_destruct HR. rb_cbn. subst act' ft' c' pd'.
  destruct HB as ((Hbw & Es) & Hl1 & HD).
  cbn [get_side Model.sideA] in Hu, Hv.
  unfold more_thop, map_side, get_side, set_side, norm.
  cbn [Model.active Model.first_turn Model.sideA Model.sideB Model.cmb Model.pend].
  split; [| split; [exact Hl1 | unfold blife; cbn; exact HD]].
  refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj Hn (conj _ (conj _ Hd))))))).
  - destruct a as [l1 c1 p1 h1 e1 bf1 x1 u1 t1 lib1 g1], a' as [l2 c2 p2 h2 e2 bf2 x2 u2 t2 lib2 g2].
    destruct HA as (Hl & Hc & Hp & Hw & He & He' & Hx & Hx' & Hlib & Elib & (Hbf & Hn0 & Hbg) & Hu' & Ht').
    cbn in *. unfold CheckerA.sideA_rel, cut_a, set_thop_u, set_thop_t. cbn.
    repeat (split; [first [assumption | lia] |]); first [assumption | lia].
  - destruct b. split; [| exact Es].
    exact (Checker.Forall2_walker_trans Hb _ _ _ (Checker.clamp_bf_rel Hb _) Hbw).
Qed.

Lemma stepA_winner : forall s m, winner (stepA K Hb tt s m) = winner (step s m).
Proof.
  intros s m. unfold stepA, fix_big. destruct m; try reflexivity.
  destruct (is_pump_big K s (Pump i)); reflexivity.
Qed.

Lemma stepA_blife : forall s m, blife (stepA K Hb tt s m) = blife (fix_big K s m (step s m)).
Proof. reflexivity. Qed.

(** ** The simulation facts *)

(** [CheckerA.cert_safe]'s first two hypotheses. *)
Theorem sim_mine : forall n s t m,
  RA K Hb n s t -> to_move s = PA -> winner s = None ->
  huge_event Hb s = false -> big_event K s = false ->
  In m (moves s) -> In m (moves t).
Proof.
  intros n s t m HR _ _ Hh Hg Hin. destruct (RA_split n s t HR) as (HM & Hle & _).
  apply (moves_thop_mine PA _ _ m Hle). rewrite (moves_eq n s _ HM Hh Hg). exact Hin.
Qed.

Theorem sim_theirs : forall n s t m,
  RA K Hb n s t -> to_move s = PB -> winner s = None ->
  huge_event Hb s = false -> big_event K s = false ->
  In m (moves t) -> In m (moves s).
Proof.
  intros n s t m HR Hm _ Hh Hg Hin. destruct (RA_split n s t HR) as (HM & Hle & _).
  rewrite <- (moves_eq n s _ HM Hh Hg). rewrite <- (moves_thop_opp PA _ _ Hle); [exact Hin |].
  rewrite <- (to_move_thop PA _ _ Hle) in *. rewrite (RA_to_move K Hb n s t HR). exact Hm.
Qed.

(** The third: a step either ends the real game in A's favour, or keeps
    [RA] and moves B's real life as [CheckerA] says. *)
Theorem sim_step : forall n s t m,
  RA K Hb n s t -> In m (moves s) -> huge_event Hb s = false -> big_event K s = false ->
  (is_create K s m && has_big K s)%bool = false ->
  winner (stepA K Hb tt s m) = None -> 1 <= t.(sideB).(life) ->
  winner (step t m) = Some PA \/
  (RA K Hb (if is_pump_big K s m then S n else if is_create K s m then O else n) (stepA K Hb tt s m) (step t m) /\
   1 <= (step t m).(sideB).(life) /\
   blife (step t m) = (blife t + (blife (stepA K Hb tt s m) - blife s) - (if is_hit K s then Z.of_nat n else 0))%Z).
Proof.
  intros n s t m HR Hin Hh Hg Hc Hw Hl.
  destruct (RA_split n s t HR) as (_ & Hle & HRB). specialize (HRB Hl).
  rewrite stepA_winner in Hw.
  pose proof (step_thop PA _ _ m Hle) as Hle'.
  destruct (RB_step n _ s (thopA s t) m HRB Hin Hh Hg Hc Hw) as [Hwin | HR'].
  - left. rewrite (winner_thop PA _ _ Hle'). exact Hwin.
  - right. destruct (RA_join _ _ _ _ _ HR' Hle') as (HRA & Hl' & Eb).
    split; [exact HRA |]. split; [exact Hl' |].
    rewrite Eb, stepA_blife. destruct (is_hit K s); lia.
Qed.

(** The key's facts. *)
Theorem RA_key : forall n M s t, RA K Hb n s t -> RA K Hb n (entry M (key Hb tt s)) t.
Proof.
  intros n M [act ft a b c pd] [act' ft' a' b' c' pd'] (E1 & E2 & E3 & E4 & Hn & HA & HB & Hd).
  rb_cbn. unfold entry, key, norm, map_side, get_side, set_side.
  cbn [Model.active Model.first_turn Model.sideA Model.sideB Model.cmb Model.pend].
  refine (conj E1 (conj E2 (conj E3 (conj E4 (conj Hn (conj _ (conj _ Hd))))))).
  - destruct a as [l1 c1 p1 h1 e1 bf1 x1 u1 t1 lib1 g1], a' as [l2 c2 p2 h2 e2 bf2 x2 u2 t2 lib2 g2].
    destruct HA as (Hl & Hc & Hp & Hw & He & He' & Hx & Hx' & Hlib & Elib & Hbf & Hn0 & Hbg & Hu & Ht).
    cbn in *. unfold CheckerA.sideA_rel, cut_a, set_gy_w, set_thop_u, set_thop_t. cbn.
    repeat (split; [first [assumption | lia] |]); first [assumption | lia].
  - destruct HB as (Hbw & Es). destruct b. split; [| exact Es].
    exact (Checker.Forall2_walker_trans Hb _ _ _ (Checker.clamp_bf_rel Hb _) Hbw).
Qed.

Theorem has_big_key : forall M s, has_big K (entry M (key Hb tt s)) = has_big K s.
Proof. intros M [act ft [] b c pd]. reflexivity. Qed.

End SaturationA.

(** ** The checker's guarantee, with no hypotheses left but the check itself

    The parameters only need [1 <= Hb < K]: B's saturated Walkers are
    below the BIG size, and a Walker A casts (with at most one counter) is
    not BIG. *)

Theorem certified_safe_a : forall K Hb ott tt lookup hint,
  Hb < K -> 1 <= Hb ->
  (forall s c b, lookup s = Some (c, b) ->
     exists d e M fuel, s = bump PA d e /\ check_node K Hb ott tt lookup hint fuel true (entry M e) c b O = true) ->
  forall n s t c b, RA K Hb n s t -> 1 <= t.(sideB).(life) -> is_turn_start s = true ->
  lookup (key Hb tt s) = Some (c, b) -> (blife t <= c + b * Z.of_nat n)%Z -> safe PA t.
Proof.
  intros K Hb ott tt lookup hint HbK Hb1 Hok.
  exact (cert_safe K Hb ott tt lookup hint Hok (sim_mine K Hb HbK Hb1) (sim_theirs K Hb HbK Hb1)
           (sim_step K Hb tt HbK Hb1) (RA_key K Hb tt HbK Hb1)).
Qed.

Lemma RA_init : forall K Hb p, RA K Hb 0 (init p) (init p).
Proof.
  intros K Hb []; unfold RA, init, CheckerA.sideA_rel, CheckerA.sideB_rel; cbn;
    repeat split; auto; constructor.
Qed.

(** If every certificate entry checks (each with its own life for B and
    fuel) and the A-first opening's entry has a line at least B's starting
    20 life, A is safe (does not lose) from the opening. *)
Theorem certified_opening_a : forall K Hb ott tt lookup hint c b,
  Hb < K -> 1 <= Hb ->
  (forall s c b, lookup s = Some (c, b) ->
     exists d e M fuel, s = bump PA d e /\ check_node K Hb ott tt lookup hint fuel true (entry M e) c b O = true) ->
  lookup (key Hb tt (init PA)) = Some (c, b) -> (20 <= c)%Z -> safe PA (init PA).
Proof.
  intros K Hb ott tt lookup hint c b HbK Hb1 Hok Hk Hc.
  apply (certified_safe_a K Hb ott tt lookup hint HbK Hb1 Hok 0 (init PA) (init PA) c b (RA_init K Hb PA)).
  - cbn. lia.
  - reflexivity.
  - exact Hk.
  - unfold blife. cbn. lia.
Qed.

Print Assumptions certified_safe_a.
Print Assumptions certified_opening_a.
