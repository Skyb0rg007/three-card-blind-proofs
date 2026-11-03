(** * The order of A's Walkers does not matter

    Swapping A's first two battlefield Walkers, and renaming everything that
    refers to them by index, preserves [wins p] and [safe p] for both
    players ([wins_sym], [safe_sym]). A owns two Walker cards, so this is
    every reordering of A's battlefield; the statements hold for every
    state, well formed or not.

    The relation is [Sym]: equality, or [SymX], where A's [bf] is
    [w1 :: w0 :: r] instead of [w0 :: w1 :: r] and the combat is renamed
    ([cmb_rel]):
    - When A attacks, the attacker indices [atk] are renamed by [swi]
      (0 <-> 1). But the attacking Walkers are listed in increasing order, so
      when both Walkers attack the lists stay [0 :: 1 :: r] and the
      per-attacker data ([blk], and the [Block], [Order] and [Assign] moves)
      are swapped instead ([crossed]).
    - When A defends, the blocker indices [BW i] in [blk] are renamed. Right
      after blocking, the blockers of an attacker are listed in increasing
      index order, so while the damage assignment order is still to be
      chosen ([ChooseOrder]) they are only a permutation of the renamed
      ones.

    [Sym] is symmetric ([Sym_sym]) and a bisimulation ([Sym_step]).

    For the certificate tables, [normA] puts A's two Walkers in increasing
    order of (counters, tapped, sick), false before true, as the solvers'
    [canon] sorts them. [Sym s (normA s)] holds for every [s]
    ([Sym_normA]). [swapA] commutes with [bump], [more_thop] and the
    checkers' [key], [entry] and [norm], and keeps their relations [R] and
    [RA]; [safe_set_up_sym] and [safe_set_down_sym] close safe sets under
    [Sym] as [Mono.safe_set_up] and [Mono.safe_set_down] do under life. *)

From Stdlib Require Import List Bool Arith Lia Permutation.
Import ListNotations.
From TCB.Spec Require Import Model Game Claims.
From TCB.Proofs Require Import GameFacts Mono Preservation.

(** ** Renaming indices 0 and 1 *)

Definition swi (i : nat) : nat := match i with 0 => 1 | 1 => 0 | _ => i end.

Definition swap01 {X} (l : list X) : list X :=
  match l with a :: b :: r => b :: a :: r | _ => l end.

Definition ren_b (b : blocker) : blocker :=
  match b with BW i => BW (swi i) | BT => BT end.

Lemma swi_swi : forall i, swi (swi i) = i.
Proof. intros [| [| i]]; reflexivity. Qed.

Lemma swi_eqb : forall i j, (swi i =? j) = (i =? swi j).
Proof. intros [| [| i]] [| [| j]]; reflexivity. Qed.

Lemma swi_big : forall i, 2 <= i -> swi i = i.
Proof. intros [| [| i]] H; [lia | lia | reflexivity]. Qed.

Lemma swi_lt : forall i n, 2 <= n -> i < n -> swi i < n.
Proof. intros [| [| i]] n H1 H2; cbn; lia. Qed.

Lemma ren_b_ren_b : forall b, ren_b (ren_b b) = b.
Proof. intros [i |]; cbn; [rewrite swi_swi |]; reflexivity. Qed.

Lemma map_ren_b_ren_b : forall bs, map ren_b (map ren_b bs) = bs.
Proof. intros bs. rewrite map_map. rewrite (map_ext _ id) by apply ren_b_ren_b. apply map_id. Qed.

Lemma map_swi_big : forall l, Forall (fun i => 2 <= i) l -> map swi l = l.
Proof.
  intros l H. induction H as [| x l Hx _ IH]; cbn; [reflexivity |].
  rewrite swi_big by exact Hx. f_equal. exact IH.
Qed.

Lemma map_swi_swi : forall l, map swi (map swi l) = l.
Proof. intros l. rewrite map_map. rewrite (map_ext _ id) by apply swi_swi. apply map_id. Qed.

Lemma mem_map_swi : forall i d, existsb (Nat.eqb i) (map swi d) = existsb (Nat.eqb (swi i)) d.
Proof.
  intros i d. induction d as [| j d IH]; cbn; [reflexivity |].
  rewrite IH, (swi_eqb i j). destruct j as [| [| j]]; reflexivity.
Qed.

(** ** Lists with their first two elements swapped *)

Lemma swap01_swap01 : forall {X} (l : list X), swap01 (swap01 l) = l.
Proof. intros X [| a [| b r]]; reflexivity. Qed.

Lemma length_swap01 : forall {X} (l : list X), length (swap01 l) = length l.
Proof. intros X [| a [| b r]]; reflexivity. Qed.

Lemma map_swap01 : forall {X Y} (f : X -> Y) l, map f (swap01 l) = swap01 (map f l).
Proof. intros X Y f [| a [| b r]]; reflexivity. Qed.

Lemma swap01_app : forall {X} (l m : list X), 2 <= length l -> swap01 (l ++ m) = swap01 l ++ m.
Proof. intros X [| a [| b r]] m H; cbn in H; [lia | lia | reflexivity]. Qed.

Lemma nth_error_swap01 : forall {X} (l : list X) i, 2 <= length l ->
  nth_error (swap01 l) i = nth_error l (swi i).
Proof. intros X [| a [| b r]] [| [| i]] H; cbn in H; try lia; reflexivity. Qed.

Lemma nth_swap01 : forall {X} (l : list X) i d, 2 <= length l ->
  nth i (swap01 l) d = nth (swi i) l d.
Proof. intros X [| a [| b r]] [| [| i]] d H; cbn in H; try lia; reflexivity. Qed.

Lemma perm_swap01 : forall {X} (l : list X), Permutation (swap01 l) l.
Proof. intros X [| a [| b r]]; [reflexivity | reflexivity | apply perm_swap]. Qed.

Lemma combine_swap01 : forall {X Y} (a : list X) (b : list Y), 2 <= length a -> 2 <= length b ->
  combine (swap01 a) (swap01 b) = swap01 (combine a b).
Proof.
  intros X Y [| x0 [| x1 a]] [| y0 [| y1 b]] Ha Hb; cbn in Ha, Hb; try lia; reflexivity.
Qed.

Lemma existsb_perm : forall {X} (f : X -> bool) l l', Permutation l l' -> existsb f l = existsb f l'.
Proof.
  intros X f l l' H. induction H; cbn; try congruence.
  - rewrite !orb_assoc, (orb_comm (f y)). reflexivity.
Qed.

Lemma filter_perm : forall {X} (f : X -> bool) l l', Permutation l l' -> Permutation (filter f l) (filter f l').
Proof.
  intros X f l l' H. induction H; cbn.
  - constructor.
  - destruct (f x); [constructor |]; assumption.
  - destruct (f x), (f y); try constructor; reflexivity.
  - eapply perm_trans; eassumption.
Qed.

Lemma list_sum_perm : forall l l', Permutation l l' -> list_sum l = list_sum l'.
Proof. intros l l' H. apply Permutation_list_sum. exact H. Qed.

Lemma perm_le1 : forall {X} (l l' : list X), Permutation l l' -> length l < 2 -> l' = l.
Proof.
  intros X [| a [| b r]] l' H Hl; cbn in Hl; try lia.
  - apply Permutation_nil. exact H.
  - apply Permutation_length_1_inv in H. exact H.
Qed.

(** ** Index functions *)

Lemma nth_error_combine_seq : forall {X} (l : list X) k i,
  nth_error (combine (seq k (length l)) l) i = option_map (fun x => (k + i, x)) (nth_error l i).
Proof.
  intros X l. induction l as [| x l IH]; intros k [| i]; cbn; try reflexivity.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH. destruct (nth_error l i); cbn; [do 2 f_equal; lia | reflexivity].
Qed.

Lemma nth_error_enum : forall {X} (l : list X) i,
  nth_error (enum l) i = option_map (fun x => (i, x)) (nth_error l i).
Proof. intros. unfold enum. apply nth_error_combine_seq. Qed.

Lemma nth_error_update_nth : forall {X} n (f : X -> X) l i,
  nth_error (update_nth n f l) i = if i =? n then option_map f (nth_error l i) else nth_error l i.
Proof.
  intros X n f l i. unfold update_nth. rewrite nth_error_map, nth_error_enum.
  destruct (nth_error l i); cbn; destruct (i =? n); reflexivity.
Qed.

Lemma update_nth_swap : forall {X} n (f : X -> X) l, 2 <= length l ->
  update_nth (swi n) f (swap01 l) = swap01 (update_nth n f l).
Proof.
  intros X n f l H. apply nth_error_ext. intros i.
  rewrite nth_error_swap01 by (rewrite length_update_nth; exact H).
  rewrite !nth_error_update_nth, nth_error_swap01 by exact H.
  rewrite swi_eqb. reflexivity.
Qed.

Lemma nth_error_taps : forall ws (l : list walker) j,
  nth_error (fold_right (fun i l => update_nth i tap_walker l) l ws) j =
  if existsb (Nat.eqb j) ws then option_map tap_walker (nth_error l j) else nth_error l j.
Proof.
  induction ws as [| i ws IH]; intros l j; cbn [fold_right existsb]; [reflexivity |].
  rewrite nth_error_update_nth, IH.
  destruct (j =? i); cbn [orb]; [| reflexivity].
  destruct (existsb (Nat.eqb j) ws); [| reflexivity].
  destruct (nth_error l j); reflexivity.
Qed.

Lemma taps_swap : forall ws ws' (l : list walker), 2 <= length l ->
  (forall j, existsb (Nat.eqb j) ws' = existsb (Nat.eqb (swi j)) ws) ->
  fold_right (fun i l => update_nth i tap_walker l) (swap01 l) ws' =
  swap01 (fold_right (fun i l => update_nth i tap_walker l) l ws).
Proof.
  intros ws ws' l H Hm. apply nth_error_ext. intros j.
  rewrite nth_error_swap01 by (rewrite length_tap_all; exact H).
  rewrite !nth_error_taps, Hm, nth_error_swap01 by exact H. reflexivity.
Qed.

(** [indices_where] and [remove_indices] from an offset. *)
Definition ind_from {X} (k : nat) (f : nat -> X -> bool) (l : list X) : list nat :=
  map fst (filter (fun '(i, x) => f i x) (combine (seq k (length l)) l)).

Lemma ind_from_cons : forall {X} k f (x : X) l,
  ind_from k f (x :: l) = if f k x then k :: ind_from (S k) f l else ind_from (S k) f l.
Proof. intros. unfold ind_from. cbn. destruct (f k x); reflexivity. Qed.

Lemma ind_from_ge : forall {X} k f (l : list X), Forall (fun i => k <= i) (ind_from k f l).
Proof.
  intros X k f l. revert k. induction l as [| x l IH]; intros k; [constructor |].
  rewrite ind_from_cons. specialize (IH (S k)).
  destruct (f k x); [constructor; [lia |] |];
    (eapply Forall_impl; [| exact IH]; intros i Hi; cbv beta in *; lia).
Qed.

Lemma ind_from_map : forall {X Y} k f (g : Y -> X) l,
  ind_from k f (map g l) = ind_from k (fun i y => f i (g y)) l.
Proof.
  intros X Y k f g l. revert k. induction l as [| y l IH]; intros k; [reflexivity |].
  cbn [map]. rewrite !ind_from_cons, IH. reflexivity.
Qed.

Lemma ind_from_ext : forall {X} k f f' (l : list X), (forall i x, f i x = f' i x) ->
  ind_from k f l = ind_from k f' l.
Proof.
  intros X k f f' l H. revert k. induction l as [| x l IH]; intros k; [reflexivity |].
  rewrite !ind_from_cons, H, IH. reflexivity.
Qed.

Lemma indices_where_from : forall {X} f (l : list X), indices_where f l = ind_from 0 f l.
Proof. reflexivity. Qed.

Lemma in_indices_where_iff : forall {X} f (l : list X) i,
  In i (indices_where f l) <-> exists x, nth_error l i = Some x /\ f i x = true.
Proof.
  intros X f l i. unfold indices_where. rewrite in_map_iff. split.
  - intros ([i' x] & <- & Hin). apply filter_In in Hin as [Hin Hf].
    apply In_nth_error in Hin as [j Hj]. rewrite nth_error_enum in Hj.
    destruct (nth_error l j) eqn:E; [| discriminate]. injection Hj as -> ->.
    exists x. auto.
  - intros (x & Hx & Hf). exists (i, x). split; [reflexivity |].
    apply filter_In. split; [| exact Hf].
    apply nth_error_In with i. rewrite nth_error_enum, Hx. reflexivity.
Qed.

(** With a test that ignores the index, the indices in the swapped list are
    the renamed ones, possibly in another order. *)
Lemma indices_swap_perm : forall {X} (g : X -> bool) l, 2 <= length l ->
  Permutation (indices_where (fun _ x => g x) (swap01 l)) (map swi (indices_where (fun _ x => g x) l)).
Proof.
  intros X g [| x0 [| x1 r]] H; cbn in H; try lia. cbn [swap01].
  rewrite !indices_where_from, !ind_from_cons.
  pose proof (map_swi_big _ (ind_from_ge 2 (fun _ x => g x) r)) as E.
  destruct (g x0), (g x1); cbn [map swi]; rewrite E; try reflexivity. apply perm_swap.
Qed.

Lemma in_indices_swap : forall {X} (g : X -> bool) l i, 2 <= length l ->
  In i (indices_where (fun _ x => g x) l) -> In (swi i) (indices_where (fun _ x => g x) (swap01 l)).
Proof.
  intros X g l i H Hin. apply in_indices_where_iff in Hin as (x & Hx & Hg).
  apply in_indices_where_iff. exists x. rewrite nth_error_swap01, swi_swi by exact H. auto.
Qed.

Definition rem_from {X} (k : nat) (dead : list nat) (l : list X) : list X :=
  map snd (filter (fun '(i, _) => negb (existsb (Nat.eqb i) dead)) (combine (seq k (length l)) l)).

Lemma rem_from_cons : forall {X} k dead (x : X) l,
  rem_from k dead (x :: l) =
  if existsb (Nat.eqb k) dead then rem_from (S k) dead l else x :: rem_from (S k) dead l.
Proof. intros. unfold rem_from. cbn. destruct (existsb (Nat.eqb k) dead); reflexivity. Qed.

Lemma rem_from_ext : forall {X} k d d' (l : list X),
  (forall i, k <= i -> existsb (Nat.eqb i) d = existsb (Nat.eqb i) d') ->
  rem_from k d l = rem_from k d' l.
Proof.
  intros X k d d' l. revert k. induction l as [| x l IH]; intros k H; [reflexivity |].
  rewrite !rem_from_cons, H by lia. rewrite IH by (intros; apply H; lia). reflexivity.
Qed.

Lemma remove_from : forall {X} dead (l : list X), remove_indices dead l = rem_from 0 dead l.
Proof. reflexivity. Qed.

Lemma remove_mem : forall {X} d d' (l : list X),
  (forall i, existsb (Nat.eqb i) d = existsb (Nat.eqb i) d') -> remove_indices d l = remove_indices d' l.
Proof. intros. rewrite !remove_from. apply rem_from_ext. auto. Qed.

Lemma remove_perm : forall {X} d d' (l : list X), Permutation d d' -> remove_indices d l = remove_indices d' l.
Proof. intros. apply remove_mem. intros i. apply existsb_perm. assumption. Qed.

(** Removing renamed indices from the swapped list: the survivors in the
    same order if one of the two Walkers dies, swapped if neither does. *)
Definition dies01 (dead : list nat) : bool := existsb (Nat.eqb 0) dead || existsb (Nat.eqb 1) dead.

Lemma remove_swap : forall {X} dead (l : list X), 2 <= length l ->
  (dies01 dead = true -> remove_indices (map swi dead) (swap01 l) = remove_indices dead l) /\
  (dies01 dead = false -> remove_indices (map swi dead) (swap01 l) = swap01 (remove_indices dead l) /\
                          2 <= length (remove_indices dead l)).
Proof.
  intros X dead [| x0 [| x1 r]] H; cbn in H; try lia. cbn [swap01]. unfold dies01.
  rewrite !remove_from, !rem_from_cons, !mem_map_swi. cbn [swi].
  rewrite (rem_from_ext 2 (map swi dead) dead)
    by (intros i Hi; rewrite mem_map_swi, swi_big by exact Hi; reflexivity).
  destruct (existsb (Nat.eqb 0) dead), (existsb (Nat.eqb 1) dead); cbn; split; intros E;
    try discriminate; auto.
  split; [reflexivity | lia].
Qed.

(** ** The relation *)

Definition sw_side (a : side) : side := set_bf (swap01 a.(bf)) a.

(** Blockers of the attackers when A defends: renamed, and only up to order
    until the damage assignment order is chosen. *)
Definition blk_rel (pd : pending) (bl bl' : list (list blocker)) : Prop :=
  match pd with
  | ChooseOrder => Forall2 (fun bs bs' => Permutation bs' (map ren_b bs)) bl bl'
  | _ => bl' = map (map ren_b) bl
  end.

(** Both of A's Walkers attack: the attacker lists stay [0 :: 1 :: r], the
    per-attacker blockers are swapped. *)
Definition crossed (c c' : combat) : Prop :=
  exists r, c.(atk) = 0 :: 1 :: r /\ Forall (fun i => 2 <= i) r /\ c'.(atk) = c.(atk) /\
    2 <= length c.(blk) /\ c'.(blk) = swap01 c.(blk).

Definition cmb_rel (act : player) (pd : pending) (c c' : combat) : Prop :=
  c'.(atk_thop) = c.(atk_thop) /\ c'.(trades) = c.(trades) /\
  match act with
  | PA => (c'.(atk) = map swi c.(atk) /\ c'.(blk) = c.(blk)) \/ crossed c c'
  | PB => c'.(atk) = c.(atk) /\ blk_rel pd c.(blk) c'.(blk)
  end.

Definition SymX (s t : state) : Prop :=
  2 <= length s.(sideA).(bf) /\
  exists c', cmb_rel s.(active) s.(pend) s.(cmb) c' /\
    t = mkState s.(active) s.(first_turn) (sw_side s.(sideA)) s.(sideB) c' s.(pend).

Definition Sym (s t : state) : Prop := t = s \/ SymX s t.

Lemma sw_side_sw_side : forall a, sw_side (sw_side a) = a.
Proof. intros []. unfold sw_side, set_bf. cbn. rewrite swap01_swap01. reflexivity. Qed.

Lemma length_sw_side : forall a, length (sw_side a).(bf) = length a.(bf).
Proof. intros []. apply length_swap01. Qed.

Lemma cmb_rel_sym : forall act pd c c', cmb_rel act pd c c' -> cmb_rel act pd c' c.
Proof.
  intros act pd c c' (E1 & E2 & Hc). split; [congruence |]. split; [congruence |].
  destruct act.
  - destruct Hc as [(Ea & Eb) | (r & Ea & Hr & Ea' & Hl & Eb)].
    + left. rewrite Ea, map_swi_swi. auto.
    + right. exists r. rewrite Ea', Ea. repeat split; auto.
      * rewrite Eb, length_swap01. exact Hl.
      * rewrite Eb, swap01_swap01. reflexivity.
  - destruct Hc as (Ea & Hb). split; [congruence |].
    destruct pd; unfold blk_rel in *;
      try (rewrite Hb, map_map; rewrite (map_ext _ id) by apply map_ren_b_ren_b; symmetry; apply map_id).
    clear - Hb. induction Hb as [| bs bs' l l' Hp _ IH]; constructor; [| exact IH].
    apply (Permutation_map ren_b) in Hp. rewrite map_ren_b_ren_b in Hp. symmetry. exact Hp.
Qed.

Lemma Sym_sym : forall s t, Sym s t -> Sym t s.
Proof.
  intros s t [-> | (Hl & c' & Hc & ->)]; [left; reflexivity | right].
  destruct s as [act ft a b c pd]. unfold SymX.
  cbn [Model.sideA Model.active Model.pend Model.cmb Model.first_turn Model.sideB] in *.
  split; [rewrite length_sw_side; exact Hl |].
  exists c. split; [apply cmb_rel_sym; exact Hc |]. rewrite sw_side_sw_side. reflexivity.
Qed.

Lemma Sym_winner : forall s t, Sym s t -> winner t = winner s.
Proof. intros s t [-> | (_ & c' & _ & ->)]; reflexivity. Qed.

Lemma Sym_to_move : forall s t, Sym s t -> to_move t = to_move s.
Proof. intros s t [-> | (_ & c' & _ & ->)]; reflexivity. Qed.

Lemma cmb_rel_pend : forall act pd pd' c c', cmb_rel act pd c c' ->
  pd <> ChooseOrder -> pd' <> ChooseOrder -> cmb_rel act pd' c c'.
Proof.
  intros [] pd pd' c c' (E1 & E2 & Hc) H1 H2; (split; [exact E1 | split; [exact E2 |]]); [exact Hc |].
  destruct Hc as (Ea & Hb). split; [exact Ea |].
  destruct pd, pd'; cbn in *; congruence.
Qed.

Lemma cmb_rel_none : forall act pd, cmb_rel act pd no_combat no_combat.
Proof.
  intros [] pd; (split; [reflexivity | split; [reflexivity |]]); [left; split; reflexivity |].
  split; [reflexivity |]. destruct pd; cbn; try reflexivity. constructor.
Qed.

Lemma SymX_mk : forall act ft a a' b c c' pd, 2 <= length a.(bf) -> a' = sw_side a ->
  cmb_rel act pd c c' -> Sym (mkState act ft a b c pd) (mkState act ft a' b c' pd).
Proof. intros. subst. right. split; [assumption |]. exists c'. auto. Qed.

Lemma can_pay_sw : forall n a, can_pay n (sw_side a) = can_pay n a.
Proof.
  intros n []. unfold can_pay, pay. cbn.
  destruct (n <=? _); [reflexivity |]. destruct (_ && _); reflexivity.
Qed.

(** ** Steps *)

Ltac sw_cbn :=
  unfold sw_side, set_bf in *;
  cbn [Model.life Model.city Model.pool Model.hand_w Model.hand_e Model.bf
    Model.elixir_bf Model.thop_u Model.thop_t Model.library Model.gy_w] in *.

(** Finish [Sym] of two states built field by field. *)
Ltac fin_sym :=
  first
  [ left; reflexivity
  | apply SymX_mk;
    [ cbn; rewrite ?length_map, ?length_update_nth, ?length_app, ?length_tap_all; cbn; lia
    | unfold sw_side, set_bf; cbn; f_equal;
      rewrite ?map_swap01, ?swap01_app by lia; try reflexivity
    | first [ eapply cmb_rel_pend; [eassumption | first [discriminate | assumption] | discriminate]
            | apply cmb_rel_none
            | assumption ] ] ].

Lemma sym_end_step : forall st act ft a b c c' pd, 2 <= length a.(bf) -> cmb_rel act pd c c' ->
  pd <> ChooseOrder ->
  Sym (end_step st (mkState act ft a b c pd)) (end_step st (mkState act ft (sw_side a) b c' pd)).
Proof.
  intros st act ft a b [atk k blk tr] [atk' k' blk' tr'] pd Hlen Hc Hpd.
  destruct a as [la ca pa hwa hea bfa ea tua tta liba gya], b. sw_cbn.
  pose proof Hc as (Ek & Etr & Hc'). unfold crossed in Hc'.
  cbn [Model.atk_thop Model.trades Model.atk Model.blk] in Ek, Etr, Hc'.
  subst k' tr'.
  assert (Hatk : (atk = [] <-> atk' = [])).
  { destruct act.
    - destruct Hc' as [(-> & _) | (r & -> & _ & -> & _)]; [destruct atk | ]; split; easy.
    - destruct Hc' as (-> & _). tauto. }
  destruct st, act, ft; simpl_step; split_tests; try fin_sym.
  all: exfalso; destruct Hatk as [H1 H2];
    first [specialize (H1 eq_refl) | specialize (H2 eq_refl)]; discriminate.
Qed.

Ltac in_split' :=
  repeat match goal with
  | Hin : In _ (_ :: _) |- _ => destruct Hin as [Hin | Hin]; [try discriminate |]
  | Hin : In _ (_ ++ _) |- _ => apply in_app_iff in Hin as [Hin | Hin]
  | Hin : In _ (map _ _) |- _ => let x := fresh in apply in_map_iff in Hin as [x [Hin _]]; try discriminate
  | Hin : In _ [] |- _ => destruct Hin
  | Hin : In _ (if ?b then _ else _) |- _ => destruct b
  end.

(** *** Priority windows *)

Definition mv_window (m : move) : move := match m with Pump i => Pump (swi i) | _ => m end.

Definition mv_win (p : player) (m : move) : move := match p with PA => mv_window m | PB => m end.

Lemma sym_window_moves : forall act ft a b c c' st p passed m, 2 <= length a.(bf) ->
  In m (window_moves st p (mkState act ft a b c (Window st p passed))) ->
  In (mv_win p m) (window_moves st p (mkState act ft (sw_side a) b c' (Window st p passed))).
Proof.
  intros act ft a b c c' st [] passed m Hlen Hin; unfold window_moves in *;
    cbn [get_side Model.sideA Model.sideB Model.active mv_win] in *; [| exact Hin].
  rewrite !can_pay_sw. destruct a as [la ca pa hwa hea bfa ea tua tta liba gya]. sw_cbn.
  destruct Hin as [<- | Hin]; [left; reflexivity |]. right.
  apply in_app_iff in Hin as [Hin | Hin].
  - destruct (can_pay 1 _); [| destruct Hin]. apply in_map_iff in Hin as (i & <- & Hi).
    cbn [mv_window]. apply in_app_iff. left. apply in_map. apply in_indices_swap; assumption.
  - assert (E : mv_window m = m) by (destruct m; try reflexivity; exfalso; in_split').
    rewrite E. apply in_app_iff. right. exact Hin.
Qed.

Lemma sym_window_step : forall act ft a b c c' st p passed m, 2 <= length a.(bf) ->
  cmb_rel act (Window st p passed) c c' ->
  Sym (step (mkState act ft a b c (Window st p passed)) m)
      (step (mkState act ft (sw_side a) b c' (Window st p passed)) (mv_win p m)).
Proof.
  intros act ft a b c c' st p passed m Hlen Hc.
  assert (Hm : forall m, match m with Pass | Pump _ | ActElixir | CastWalker _ | CastElixir => False | _ => True end ->
     Sym (step (mkState act ft a b c (Window st p passed)) m)
         (step (mkState act ft (sw_side a) b c' (Window st p passed)) m)).
  { intros [] Hn; try destruct Hn; apply SymX_mk; auto. }
  destruct p, m; cbn [mv_win mv_window]; try (apply Hm; exact I).
  all: try (destruct passed; [apply sym_end_step; [exact Hlen | exact Hc | discriminate] |]).
  all: destruct a as [la ca pa hwa hea bfa ea tua tta liba gya], b; sw_cbn.
  all: simpl_step; split_tests; fin_sym.
  all: try (apply update_nth_swap; lia).
Qed.

(** *** Declaring attackers *)

Lemma sublist_subsets : forall ws l, sublist ws l -> In ws (subsets l).
Proof.
  intros ws l H. unfold subsets. induction H as [| x l l' _ IH | x l l' _ IH]; cbn [fold_right].
  - left. reflexivity.
  - apply in_app_iff. left. exact IH.
  - apply in_app_iff. right. apply in_map. exact IH.
Qed.

Lemma sublist_ge : forall ws T, sublist ws T -> Forall (fun i => 2 <= i) T -> Forall (fun i => 2 <= i) ws.
Proof.
  intros ws T Hs HT. rewrite Forall_forall in *. intros x Hx. apply HT, (sublist_incl _ _ Hs), Hx.
Qed.

(** The attackers in the swapped state: the renamed ones, sorted. *)
Lemma attack_ws : forall l ws, 2 <= length l ->
  sublist ws (indices_where (fun _ w => can_pump w) l) ->
  exists ws', sublist ws' (indices_where (fun _ w => can_pump w) (swap01 l)) /\
    (ws' = map swi ws \/ exists r, ws = 0 :: 1 :: r /\ Forall (fun i => 2 <= i) r /\ ws' = ws).
Proof.
  intros [| x0 [| x1 r]] ws H Hs; cbn in H; try lia. cbn [swap01] in *.
  rewrite !indices_where_from, !ind_from_cons in *.
  pose proof (ind_from_ge 2 (fun _ w => can_pump w) r) as HT.
  set (T := ind_from 2 (fun _ w => can_pump w) r) in *.
  assert (Hpl : forall w, sublist w T -> map swi w = w)
    by (intros w Hw; apply map_swi_big; eapply sublist_ge; eassumption).
  destruct (can_pump x0), (can_pump x1).
  - inversion Hs as [| ? ? ? Hs1 | ? w ? Hs1]; subst.
    + inversion Hs1 as [| ? ? ? Hs2 | ? w ? Hs2]; subst.
      * exists ws. split; [apply sl_skip, sl_skip, Hs2 | left; symmetry; apply Hpl, Hs2].
      * exists (0 :: w). split; [apply sl_keep, sl_skip, Hs2 | left; cbn; rewrite Hpl; auto].
    + inversion Hs1 as [| ? ? ? Hs2 | ? w' ? Hs2]; subst.
      * exists (1 :: w). split; [apply sl_skip, sl_keep, Hs2 | left; cbn; rewrite Hpl; auto].
      * exists (0 :: 1 :: w'). split; [apply sl_keep, sl_keep, Hs2 |].
        right. exists w'. split; [reflexivity |]. split; [eapply sublist_ge; eassumption | reflexivity].
  - inversion Hs as [| ? ? ? Hs1 | ? w ? Hs1]; subst.
    + exists ws. split; [apply sl_skip, Hs1 | left; symmetry; apply Hpl, Hs1].
    + exists (1 :: w). split; [apply sl_keep, Hs1 | left; cbn; rewrite Hpl; auto].
  - inversion Hs as [| ? ? ? Hs1 | ? w ? Hs1]; subst.
    + exists ws. split; [apply sl_skip, Hs1 | left; symmetry; apply Hpl, Hs1].
    + exists (0 :: w). split; [apply sl_keep, Hs1 | left; cbn; rewrite Hpl; auto].
  - exists ws. split; [exact Hs | left; symmetry; apply Hpl, Hs].
Qed.

Lemma mem_ws : forall ws ws',
  (ws' = map swi ws \/ exists r, ws = 0 :: 1 :: r /\ Forall (fun i => 2 <= i) r /\ ws' = ws) ->
  forall j, existsb (Nat.eqb j) ws' = existsb (Nat.eqb (swi j)) ws.
Proof.
  intros ws ws' [-> | (r & -> & Hr & ->)] j; [apply mem_map_swi |].
  cbn [existsb]. rewrite <- (mem_map_swi j r), (map_swi_big r Hr).
  destruct j as [| [| j]]; cbn; reflexivity.
Qed.

Lemma sym_attack : forall act ft a b c c' ws k, 2 <= length a.(bf) ->
  In (Attack ws k) (moves (mkState act ft a b c ChooseAttack)) ->
  exists m', In m' (moves (mkState act ft (sw_side a) b c' ChooseAttack)) /\
    Sym (do_attack ws k (mkState act ft a b c ChooseAttack)) (step (mkState act ft (sw_side a) b c' ChooseAttack) m').
Proof.
  intros act ft a b c c' ws k Hlen Hin.
  unfold moves, attack_moves in *. cbn [get_side Model.active Model.sideA Model.sideB Model.pend] in *.
  apply in_flat_map in Hin as (ws0 & Hws & Hin). apply in_map_iff in Hin as (k0 & E & Hk). injection E as -> ->.
  destruct act.
  - destruct (attack_ws a.(bf) ws Hlen (subsets_sublist _ _ Hws)) as (ws' & Hws' & Hrel).
    exists (Attack ws' k). split.
    + apply in_flat_map. exists ws'. split; [apply sublist_subsets; destruct a; exact Hws' |].
      apply in_map. destruct a; exact Hk.
    + destruct a as [la ca pa hwa hea bfa ea tua tta liba gya], b; sw_cbn.
      simpl_step. apply SymX_mk.
      * cbn. rewrite length_tap_all. exact Hlen.
      * unfold sw_side, set_bf; cbn. f_equal. apply taps_swap; [exact Hlen | apply mem_ws; exact Hrel].
      * split; [reflexivity | split; [reflexivity |]]. cbn [Model.atk Model.blk].
        destruct Hrel as [-> | (r & -> & Hr & ->)].
        -- left. rewrite map_map. auto.
        -- right. exists r. cbn. repeat split; auto. lia.
  - exists (Attack ws k). split.
    + apply in_flat_map. exists ws. split; [exact Hws | apply in_map; exact Hk].
    + destruct a as [la ca pa hwa hea bfa ea tua tta liba gya], b; sw_cbn.
      simpl_step. apply SymX_mk.
      * exact Hlen.
      * reflexivity.
      * split; [reflexivity | split; [reflexivity |]]. split; [reflexivity |]. cbn.
        rewrite map_map. reflexivity.
Qed.

(** *** Declaring blockers *)

Lemma length_product : forall {X} (cs : list (list X)) x, In x (product cs) -> length x = length cs.
Proof. intros X cs x H. apply in_product in H. eapply Forall2_length. exact H. Qed.

Lemma product_map : forall {X} (g : X -> X) cs x, In x (product cs) ->
  (forall c y, In c cs -> In y c -> In (g y) c) -> In (map g x) (product cs).
Proof.
  intros X g cs. induction cs as [| c cs IH]; intros x Hx Hg; cbn [product fold_right] in *.
  - destruct Hx as [<- | []]. left. reflexivity.
  - apply in_flat_map in Hx as (y & Hy & Hx). apply in_map_iff in Hx as (x' & <- & Hx').
    apply in_flat_map. exists (g y). split; [apply Hg; [left; reflexivity | exact Hy] |].
    cbn [map]. apply in_map. apply IH; [exact Hx' |]. intros c' y' Hc'. apply Hg. right. exact Hc'.
Qed.

Lemma product_swap01 : forall {X} (cs : list (list X)) x, In x (product cs) ->
  In (swap01 x) (product (swap01 cs)).
Proof.
  intros X [| c0 [| c1 cs]] x Hx.
  - destruct Hx as [<- | []]. left. reflexivity.
  - pose proof (length_product _ _ Hx) as Hl. destruct x as [| y [| y' x]]; cbn in Hl; try lia. exact Hx.
  - cbn [product fold_right swap01] in *.
    apply in_flat_map in Hx as (y0 & Hy0 & Hx). apply in_map_iff in Hx as (x1 & <- & Hx1).
    apply in_flat_map in Hx1 as (y1 & Hy1 & Hx1). apply in_map_iff in Hx1 as (x' & <- & Hx').
    cbn [swap01]. apply in_flat_map. exists y1. split; [exact Hy1 |]. apply in_map.
    apply in_flat_map. exists y0. split; [exact Hy0 |]. apply in_map. exact Hx'.
Qed.


Lemma bv_swap01 : forall n t v, In v (bounded_vectors n t) -> In (swap01 v) (bounded_vectors n t).
Proof.
  intros [| [| n]] t v Hv.
  - destruct Hv as [<- | []]. left. reflexivity.
  - cbn [bounded_vectors] in Hv. apply in_flat_map in Hv as (k & Hk & Hv).
    apply in_map_iff in Hv as (v' & <- & Hv'). destruct Hv' as [<- | []]. cbn [swap01].
    cbn [bounded_vectors]. apply in_flat_map. exists k. split; [exact Hk |]. apply in_map. left. reflexivity.
  - cbn [bounded_vectors] in Hv |- *.
    apply in_flat_map in Hv as (k0 & Hk0 & Hv). apply in_map_iff in Hv as (v1 & <- & Hv1).
    apply in_flat_map in Hv1 as (k1 & Hk1 & Hv1). apply in_map_iff in Hv1 as (v' & <- & Hv').
    apply in_seq in Hk0, Hk1. cbn [swap01].
    apply in_flat_map. exists k1. split; [apply in_seq; lia |]. apply in_map.
    apply in_flat_map. exists k0. split; [apply in_seq; lia |]. apply in_map.
    replace (t - k1 - k0) with (t - k0 - k1) by lia. exact Hv'.
Qed.

Lemma list_sum_swap01 : forall l, list_sum (swap01 l) = list_sum l.
Proof. intros l. apply list_sum_perm, perm_swap01. Qed.

Definition blk_of (wb : list (option nat)) (tb : list nat) : list (list blocker) :=
  map (fun '(a, k) =>
         map BW (indices_where (fun _ o => match o with Some b => b =? a | None => false end) wb)
         ++ repeat BT k)
      (enum tb).

Lemma do_block_eq : forall wb tb tr s, do_block wb tb tr s =
  let c := mkCombat s.(cmb).(atk) s.(cmb).(atk_thop) (blk_of wb tb) tr in
  if has_multiblock c then set_pend ChooseOrder (set_cmb c s)
  else set_pend (Window DeclBlk s.(active) false) (set_cmb c s).
Proof. reflexivity. Qed.

Lemma nth_error_map_enum : forall {X Y} (h : nat * X -> Y) l i,
  nth_error (map h (enum l)) i = option_map (fun x => h (i, x)) (nth_error l i).
Proof. intros. rewrite nth_error_map, nth_error_enum. destruct (nth_error l i); reflexivity. Qed.

Lemma length_blk_of : forall wb tb, length (blk_of wb tb) = length tb.
Proof. intros. unfold blk_of. rewrite length_map. apply length_enum. Qed.

(** B blocks both of A's attacking Walkers' swapped positions. *)
Lemma blk_of_cross : forall wb tb, 2 <= length tb ->
  blk_of (map (option_map swi) wb) (swap01 tb) = swap01 (blk_of wb tb).
Proof.
  intros wb tb H. apply nth_error_ext. intros i.
  rewrite nth_error_swap01 by (rewrite length_blk_of; exact H).
  unfold blk_of. rewrite !nth_error_map_enum, nth_error_swap01 by exact H.
  destruct (nth_error tb (swi i)) as [k |]; [| reflexivity]. cbn [option_map]. do 2 f_equal.
  rewrite !indices_where_from, ind_from_map. f_equal. apply ind_from_ext.
  intros _ [o |]; cbn; [apply swi_eqb | reflexivity].
Qed.

(** A blocks with its Walkers in the other order. *)
Lemma blk_of_perm : forall wb tb, 2 <= length wb ->
  Forall2 (fun bs bs' => Permutation bs' (map ren_b bs)) (blk_of wb tb) (blk_of (swap01 wb) tb).
Proof.
  intros wb tb H. unfold blk_of. generalize (enum tb). intros l.
  induction l as [| [a k] l IH]; cbn [map]; constructor; [| exact IH].
  rewrite map_app, map_map, map_repeat. cbn [ren_b].
  apply Permutation_app_tail. rewrite <- (map_map swi BW). apply Permutation_map.
  apply (indices_swap_perm (fun o => match o with Some b => b =? a | None => false end)). exact H.
Qed.

Lemma multiblock_perm : forall l l', Forall2 (fun bs bs' => Permutation bs' (map ren_b bs)) l l' ->
  existsb (fun bs => 2 <=? length bs) l' = existsb (fun bs => 2 <=? length bs) l.
Proof.
  intros l l' H. induction H as [| bs bs' l l' Hp _ IH]; cbn [existsb]; [reflexivity |].
  rewrite IH, (Permutation_length Hp), length_map. reflexivity.
Qed.

Lemma perm_exact : forall l l', Forall2 (fun bs bs' => Permutation bs' (map ren_b bs)) l l' ->
  existsb (fun bs => 2 <=? length bs) l = false -> l' = map (map ren_b) l.
Proof.
  intros l l' H. induction H as [| bs bs' l l' Hp _ IH]; cbn [existsb map]; intros Hx; [reflexivity |].
  apply orb_false_iff in Hx as [H1 H2]. apply Nat.leb_gt in H1. f_equal; [| apply IH, H2].
  apply perm_le1; [symmetry; exact Hp | rewrite length_map; exact H1].
Qed.


Lemma sym_block : forall act ft a b c c' wb tb tr, 2 <= length a.(bf) ->
  cmb_rel act ChooseBlock c c' ->
  In (Block wb tb tr) (moves (mkState act ft a b c ChooseBlock)) ->
  exists m', In m' (moves (mkState act ft (sw_side a) b c' ChooseBlock)) /\
    Sym (do_block wb tb tr (mkState act ft a b c ChooseBlock)) (step (mkState act ft (sw_side a) b c' ChooseBlock) m').
Proof.
  intros act ft a b [atk k blk tr0] [atk' k' blk' tr0'] wb tb tr Hlen Hc Hin.
  destruct Hc as (Ek & Etr & Hc). cbn [Model.atk_thop Model.trades Model.atk Model.blk] in Ek, Etr, Hc.
  subst k' tr0'. unfold crossed in Hc. cbn [Model.atk_thop Model.trades Model.atk Model.blk] in Hc.
  unfold moves, block_moves, defender in *.
  cbn [get_side opp Model.active Model.sideA Model.sideB Model.pend Model.cmb Model.atk Model.atk_thop] in *.
  apply in_flat_map in Hin as (wb0 & Hwb & Hin). apply in_flat_map in Hin as (tb0 & Htb & Hin).
  apply in_map_iff in Hin as (tr1 & E & Htr). injection E as -> -> ->.
  destruct act; cbn [get_side opp Model.active Model.sideA Model.sideB Model.pend Model.cmb Model.atk Model.atk_thop] in *.
  - destruct Hc as [(-> & ->) | (r & -> & Hr & -> & Hl & ->)].
    + (* the same blocks *)
      exists (Block wb tb tr). rewrite length_map. split.
      * apply in_flat_map. exists wb. split; [exact Hwb |].
        apply in_flat_map. exists tb. split; [exact Htb |]. apply in_map. exact Htr.
      * cbn [step Model.pend]. rewrite !do_block_eq. cbv zeta.
        cbn [Model.cmb Model.atk Model.atk_thop Model.active].
        unfold has_multiblock. cbn [Model.blk].
        destruct (existsb _ (blk_of wb tb)); unfold set_pend, set_cmb; cbn;
          (apply SymX_mk; [exact Hlen | reflexivity |]);
          (split; [reflexivity | split; [reflexivity |]]); left; split; reflexivity.
    + (* both of A's Walkers attack: B's blocks on them swap *)
      pose proof (in_bounded_vectors _ _ _ Htb) as (Htl & Hts). cbn [length] in Htl.
      exists (Block (map (option_map swi) wb) (swap01 tb) tr). split.
      * apply in_flat_map. exists (map (option_map swi) wb). split.
        { apply product_map; [exact Hwb |]. intros cx y Hcx Hy.
          apply in_map_iff in Hcx as (w & <- & _). destruct (wtapped w); [destruct Hy as [<- | []]; left; reflexivity |].
          destruct Hy as [<- | Hy]; [left; reflexivity | right].
          apply in_map_iff in Hy as (i & <- & Hi). cbn [option_map]. apply in_map. apply in_seq in Hi. apply in_seq.
          cbn [length] in *. pose proof (swi_lt i (S (S (length r))) ltac:(lia) ltac:(lia)). lia. }
        apply in_flat_map. exists (swap01 tb). split; [apply bv_swap01; exact Htb |].
        apply in_map. rewrite list_sum_swap01. exact Htr.
      * cbn [step Model.pend]. rewrite !do_block_eq. cbv zeta.
        cbn [Model.cmb Model.atk Model.atk_thop Model.active].
        rewrite blk_of_cross by lia.
        unfold has_multiblock. cbn [Model.blk]. rewrite (existsb_perm _ _ _ (perm_swap01 _)).
        destruct (existsb _ (blk_of wb tb)); unfold set_pend, set_cmb; cbn;
          (apply SymX_mk; [exact Hlen | reflexivity |]);
          (split; [reflexivity | split; [reflexivity |]]); right; exists r; cbn;
          (repeat split; auto); rewrite length_blk_of; lia.
  - (* A blocks: its Walkers swap places in the block *)
    destruct Hc as (-> & Hb).
    assert (Hwl : 2 <= length wb) by (rewrite (length_product _ _ Hwb), length_map; exact Hlen).
    exists (Block (swap01 wb) tb tr). split.
    + apply in_flat_map. exists (swap01 wb). split.
      { destruct a; cbn [sw_side set_bf Model.bf] in *. unfold sw_side, set_bf. cbn [Model.bf].
        rewrite map_swap01. apply product_swap01. exact Hwb. }
      apply in_flat_map. exists tb. split; [destruct a; exact Htb |]. apply in_map. destruct a; exact Htr.
    + cbn [step Model.pend]. rewrite !do_block_eq. cbv zeta.
      cbn [Model.cmb Model.atk Model.atk_thop Model.active].
      pose proof (blk_of_perm wb tb Hwl) as Hp.
      unfold has_multiblock. cbn [Model.blk]. rewrite (multiblock_perm _ _ Hp).
      destruct (existsb _ (blk_of wb tb)) eqn:Em; unfold set_pend, set_cmb; cbn;
        (apply SymX_mk; [exact Hlen | reflexivity |]);
        (split; [reflexivity | split; [reflexivity |]]); (split; [reflexivity |]); cbn [blk_rel].
      * exact Hp.
      * apply perm_exact; assumption.
Qed.
