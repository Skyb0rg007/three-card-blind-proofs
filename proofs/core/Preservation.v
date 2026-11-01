(** * Preservation: legal moves keep a state well formed

    [well_formed] (in [Claims.v]) holds of the openings and is kept by every
    legal move. Card counts are kept because no move creates or destroys a
    card; combat indices stay in range because only combat damage removes
    Walkers from the battlefield, and it also ends the combat. *)
From Stdlib Require Import List Bool Arith Lia Permutation.
Import ListNotations.
From TCB.Spec Require Import Model Claims.

(** ** Lists *)

Inductive sublist {A} : list A -> list A -> Prop :=
| sl_nil : sublist [] []
| sl_skip x l l' : sublist l l' -> sublist l (x :: l')
| sl_keep x l l' : sublist l l' -> sublist (x :: l) (x :: l').

Lemma sublist_nil_l {A} (l : list A) : sublist [] l.
Proof. induction l; constructor; auto. Qed.

Lemma sublist_refl {A} (l : list A) : sublist l l.
Proof. induction l; [constructor | apply sl_keep; assumption]. Qed.

Lemma sublist_incl {A} (l l' : list A) : sublist l l' -> incl l l'.
Proof.
  induction 1 as [| x l l' _ IH | x l l' _ IH]; intros y Hy.
  - exact Hy.
  - right. apply IH, Hy.
  - destruct Hy as [<- | Hy]; [left; reflexivity | right; apply IH, Hy].
Qed.

Lemma sublist_NoDup {A} (l l' : list A) : sublist l l' -> NoDup l' -> NoDup l.
Proof.
  induction 1 as [| x l l' _ IH | x l l' Hs IH]; intros Hn.
  - constructor.
  - apply NoDup_cons_iff in Hn as [_ Hn]. auto.
  - apply NoDup_cons_iff in Hn as [Hx Hn]. constructor; auto.
    intros Hin. apply Hx, (sublist_incl _ _ Hs), Hin.
Qed.

Lemma sublist_trans {A} (l1 l2 l3 : list A) : sublist l1 l2 -> sublist l2 l3 -> sublist l1 l3.
Proof.
  intros H12 H23. revert l1 H12.
  induction H23 as [| x l l' _ IH | x l l' _ IH]; intros l1 H12.
  - exact H12.
  - apply sl_skip, IH, H12.
  - inversion H12; subst; [apply sl_skip | apply sl_keep]; auto.
Qed.

Lemma sublist_app {A} (a a' b b' : list A) :
  sublist a a' -> sublist b b' -> sublist (a ++ b) (a' ++ b').
Proof.
  induction 1 as [| x l l' _ IH | x l l' _ IH]; intros Hb; cbn.
  - exact Hb.
  - apply sl_skip, IH, Hb.
  - apply sl_keep, IH, Hb.
Qed.

Lemma sublist_map {A B} (f : A -> B) l l' : sublist l l' -> sublist (map f l) (map f l').
Proof.
  induction 1; cbn; [constructor | apply sl_skip | apply sl_keep]; assumption.
Qed.

Lemma sublist_flat_map {A B} (f : A -> list B) l l' :
  sublist l l' -> sublist (flat_map f l) (flat_map f l').
Proof.
  induction 1 as [| x l l' _ IH | x l l' _ IH]; cbn.
  - constructor.
  - rewrite <- (app_nil_l (flat_map f l)). apply sublist_app; [apply sublist_nil_l | exact IH].
  - apply sublist_app; [apply sublist_refl | exact IH].
Qed.

Lemma sublist_filter {A} (f : A -> bool) l : sublist (filter f l) l.
Proof.
  induction l as [| x l IH]; cbn; [constructor |].
  destruct (f x); [apply sl_keep | apply sl_skip]; exact IH.
Qed.

Lemma sublist_firstn {A} n (l : list A) : sublist (firstn n l) l.
Proof.
  revert l; induction n as [| n IH]; intros [| x l]; cbn.
  - constructor.
  - apply sublist_nil_l.
  - constructor.
  - apply sl_keep, IH.
Qed.

(** A sublist of a list without duplicates whose elements are below [n]. *)
Definition indices_below (n : nat) (l : list nat) : Prop :=
  NoDup l /\ Forall (fun i => i < n) l.

Lemma indices_below_sublist n l l' : sublist l l' -> indices_below n l' -> indices_below n l.
Proof.
  intros Hs [Hn Hf]. split; [eapply sublist_NoDup; eauto |].
  rewrite Forall_forall in *. intros x Hx. apply Hf, (sublist_incl _ _ Hs), Hx.
Qed.

Lemma indices_below_perm n l l' : Permutation l l' -> indices_below n l -> indices_below n l'.
Proof.
  intros Hp [Hn Hf]. split; [eapply Permutation_NoDup; eauto |].
  rewrite Forall_forall in *. intros x Hx. apply Hf. eapply Permutation_in; [symmetry |]; eauto.
Qed.

Lemma map_fst_combine {A B} (xs : list A) (ys : list B) :
  length xs = length ys -> map fst (combine xs ys) = xs.
Proof.
  revert ys; induction xs as [| x xs IH]; intros [| y ys] H; try discriminate; [reflexivity |].
  cbn. f_equal. apply IH. cbn in H. congruence.
Qed.

Lemma map_snd_combine {A B} (xs : list A) (ys : list B) :
  length xs = length ys -> map snd (combine xs ys) = ys.
Proof.
  revert ys; induction xs as [| x xs IH]; intros [| y ys] H; try discriminate; [reflexivity |].
  cbn. f_equal. apply IH. cbn in H. congruence.
Qed.

Lemma length_enum {A} (l : list A) : length (enum l) = length l.
Proof. unfold enum. rewrite length_combine, length_seq. lia. Qed.

Lemma map_fst_enum {A} (l : list A) : map fst (enum l) = seq 0 (length l).
Proof. apply map_fst_combine. apply length_seq. Qed.

Lemma map_snd_enum {A} (l : list A) : map snd (enum l) = l.
Proof. apply map_snd_combine. apply length_seq. Qed.

Lemma NoDup_enum {A} (l : list A) : NoDup (enum l).
Proof. apply (NoDup_map_inv fst). rewrite map_fst_enum. apply seq_NoDup. Qed.

Lemma in_combine_seq {A} (l : list A) k i x :
  In (i, x) (combine (seq k (length l)) l) -> nth_error l (i - k) = Some x.
Proof.
  revert k; induction l as [| y l IH]; intros k Hin; [destruct Hin |].
  cbn in Hin. destruct Hin as [E | Hin].
  - injection E as <- <-. rewrite Nat.sub_diag. reflexivity.
  - pose proof (in_combine_l _ _ _ _ Hin) as Hk. apply in_seq in Hk.
    replace (i - k) with (S (i - S k)) by lia. apply IH, Hin.
Qed.

(** Each index appears once in [enum l]. *)
Lemma enum_functional {A} (l : list A) i x y :
  In (i, x) (enum l) -> In (i, y) (enum l) -> x = y.
Proof.
  unfold enum. intros Hx Hy.
  apply in_combine_seq in Hx, Hy. congruence.
Qed.

Lemma indices_where_below {A} f (l : list A) : indices_below (length l) (indices_where f l).
Proof.
  apply indices_below_sublist with (seq 0 (length l)).
  - unfold indices_where. rewrite <- map_fst_enum. apply sublist_map, sublist_filter.
  - split; [apply seq_NoDup |]. apply Forall_forall. intros i Hi. apply in_seq in Hi. lia.
Qed.

Lemma in_indices_where {A} f (l : list A) i :
  In i (indices_where f l) -> exists x, In (i, x) (enum l) /\ f i x = true.
Proof.
  unfold indices_where. intros Hi. apply in_map_iff in Hi as ([i' x] & <- & Hi).
  apply filter_In in Hi as [Hin Hf]. exists x. auto.
Qed.

Lemma NoDup_flat_map {A B} (f : A -> list B) l :
  NoDup l -> (forall x, In x l -> NoDup (f x)) ->
  (forall x y b, In x l -> In y l -> In b (f x) -> In b (f y) -> x = y) ->
  NoDup (flat_map f l).
Proof.
  induction l as [| x l IH]; intros Hl Hf Hd; cbn; [constructor |].
  apply NoDup_cons_iff in Hl as [Hx Hl].
  apply NoDup_app.
  - apply Hf. left. reflexivity.
  - apply IH; [exact Hl | intros y Hy; apply Hf; right; exact Hy |].
    intros y z b Hy Hz. apply Hd; right; assumption.
  - intros b Hb1 Hb2. apply in_flat_map in Hb2 as (y & Hy & Hb2).
    assert (x = y) as <- by (apply (Hd x y b); auto with datatypes). contradiction.
Qed.

Lemma Permutation_flat_map {A B} (f : A -> list B) l l' :
  Permutation l l' -> Permutation (flat_map f l) (flat_map f l').
Proof.
  induction 1; cbn.
  - constructor.
  - apply Permutation_app_head. assumption.
  - rewrite !app_assoc. apply Permutation_app_tail, Permutation_app_comm.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma Permutation_concat {A} (ls ls' : list (list A)) :
  Forall2 (@Permutation A) ls ls' -> Permutation (concat ls) (concat ls').
Proof. induction 1; cbn; [constructor | apply Permutation_app; assumption]. Qed.

Lemma Forall2_map_r {A B C} (R : A -> C -> Prop) (f : B -> C) xs ys :
  Forall2 R xs (map f ys) -> Forall2 (fun x y => R x (f y)) xs ys.
Proof.
  revert xs; induction ys as [| y ys IH]; intros xs H; inversion H; subst; constructor; auto.
Qed.

Lemma Forall2_impl' {A B} (R R' : A -> B -> Prop) xs ys :
  (forall x y, R x y -> R' x y) -> Forall2 R xs ys -> Forall2 R' xs ys.
Proof. intros HR. induction 1; constructor; auto. Qed.

(** ** The generators of [Model.moves] *)

Lemma subsets_sublist l ws : In ws (subsets l) -> sublist ws l.
Proof.
  unfold subsets. revert ws. induction l as [| x l IH]; intros ws Hin; cbn [fold_right] in Hin.
  - destruct Hin as [<- | []]. constructor.
  - apply in_app_iff in Hin as [Hin | Hin].
    + apply sl_skip, IH, Hin.
    + apply in_map_iff in Hin as (ws' & <- & Hin). apply sl_keep, IH, Hin.
Qed.

Lemma in_product {A} (cs : list (list A)) x :
  In x (product cs) -> Forall2 (fun y c => In y c) x cs.
Proof.
  unfold product. revert x. induction cs as [| c cs IH]; intros x Hin; cbn [fold_right] in Hin.
  - destruct Hin as [<- | []]. constructor.
  - apply in_flat_map in Hin as (y & Hy & Hin). apply in_map_iff in Hin as (x' & <- & Hin).
    constructor; auto.
Qed.

Lemma in_bounded_vectors n t v :
  In v (bounded_vectors n t) -> length v = n /\ list_sum v <= t.
Proof.
  revert t v; induction n as [| n IH]; intros t v Hin.
  - destruct Hin as [<- | []]. cbn. lia.
  - cbn [bounded_vectors] in Hin. apply in_flat_map in Hin as (k & Hk & Hin). apply in_map_iff in Hin as (v' & <- & Hin).
    apply in_seq in Hk. apply IH in Hin as [Hl Hs].
    unfold list_sum in *. cbn [length fold_right]. lia.
Qed.

Lemma remove_first_perm {A} dec (x : A) l :
  In x l -> Permutation l (x :: remove_first dec x l).
Proof.
  induction l as [| y l IH]; intros Hin; [destruct Hin |]. cbn.
  destruct (dec x y) as [-> | Hne]; [reflexivity |].
  destruct Hin as [-> | Hin]; [congruence |].
  eapply perm_trans; [apply perm_skip, IH, Hin | apply perm_swap].
Qed.

Lemma orders_fuel_perm {A} dec n (l o : list A) :
  length l = n -> In o (orders_fuel dec n l) -> Permutation o l.
Proof.
  revert l o. induction n as [| n IH]; intros l o Hlen Hin.
  - destruct l; [| discriminate]. destruct Hin as [<- | []]. constructor.
  - destruct l as [| y r]; [discriminate |].
    cbn [orders_fuel] in Hin. apply in_flat_map in Hin as (x & Hx & Hin).
    apply in_map_iff in Hin as (o' & <- & Hin). apply nodup_In in Hx.
    pose proof (remove_first_perm dec x (y :: r) Hx) as Hp.
    eapply perm_trans; [| symmetry; exact Hp]. apply perm_skip. apply (IH _ _); [| exact Hin].
    apply Permutation_length in Hp. cbn [length] in Hp, Hlen. lia.
Qed.

Lemma orders_perm {A} dec (l o : list A) : In o (orders dec l) -> Permutation o l.
Proof. apply orders_fuel_perm. reflexivity. Qed.

(** ** Removing dead Walkers *)

Lemma length_filter_fst {A B} (q : A -> bool) (xs : list A) (ys : list B) :
  length xs = length ys ->
  length (filter (fun '(i, _) => q i) (combine xs ys)) = length (filter q xs).
Proof.
  revert ys; induction xs as [| x xs IH]; intros [| y ys] H; try discriminate; [reflexivity |].
  cbn in H |- *. destruct (q x); cbn; [f_equal |]; apply IH; congruence.
Qed.

Lemma remove_indices_length {A} (dead : list nat) (l : list A) :
  indices_below (length l) dead ->
  length (remove_indices dead l) + length dead = length l.
Proof.
  intros [Hnd Hlt]. unfold remove_indices, enum. rewrite length_map.
  rewrite (length_filter_fst (fun i => negb (existsb (Nat.eqb i) dead))) by apply length_seq.
  pose proof (filter_length (fun i => existsb (Nat.eqb i) dead) (seq 0 (length l))) as Hf.
  rewrite length_seq in Hf.
  assert (length (filter (fun i => existsb (Nat.eqb i) dead) (seq 0 (length l))) = length dead)
    as Hd.
  { apply Nat.le_antisymm; apply NoDup_incl_length.
    - apply NoDup_filter, seq_NoDup.
    - intros i Hi. apply filter_In in Hi as [_ Hi].
      apply existsb_exists in Hi as (j & Hj & E). apply Nat.eqb_eq in E. subst. exact Hj.
    - exact Hnd.
    - intros i Hi. apply filter_In. split.
      + apply in_seq. rewrite Forall_forall in Hlt. specialize (Hlt i Hi). lia.
      + apply existsb_exists. exists i. split; [exact Hi | apply Nat.eqb_refl]. }
  lia.
Qed.

(** ** Counting a side's cards *)

Definition side_walkers (sd : side) : nat :=
  sd.(hand_w) + length sd.(bf) + sd.(gy_w) + count_occ card_eq_dec sd.(library) CWalker.

Definition side_elixirs (sd : side) : nat :=
  Nat.b2n sd.(hand_e) + Nat.b2n sd.(elixir_bf) + count_occ card_eq_dec sd.(library) CElixir.

(** [sd'] has the cards and Thopters of [sd], and no fewer Walkers on the battlefield. *)
Definition same_counts (sd sd' : side) : Prop :=
  side_walkers sd' = side_walkers sd /\ side_elixirs sd' = side_elixirs sd /\
  length sd.(bf) <= length sd'.(bf) /\ sd'.(thop_u) = sd.(thop_u) /\ sd'.(thop_t) = sd.(thop_t).

Ltac solve_counts :=
  unfold same_counts, side_walkers, side_elixirs; cbn;
  rewrite ?length_app; cbn; repeat split; lia.

Lemma same_counts_refl sd : same_counts sd sd.
Proof. solve_counts. Qed.

Lemma length_update_nth {A} n (f : A -> A) l : length (update_nth n f l) = length l.
Proof. unfold update_nth. rewrite length_map. apply length_enum. Qed.

Lemma length_tap_all ws (l : list walker) :
  length (fold_right (fun i l => update_nth i tap_walker l) l ws) = length l.
Proof. induction ws; cbn; [reflexivity | rewrite length_update_nth; assumption]. Qed.

Lemma pay_shape n sd sd' :
  pay n sd = Some sd' -> exists pl ct, sd' = set_pool pl (set_city ct sd).
Proof.
  unfold pay. destruct (n <=? pool sd).
  - intros [= <-]. exists (pool sd - n), (city sd). destruct sd. reflexivity.
  - destruct (city sd && (n <=? pool sd + 2)); [| discriminate].
    intros [= <-]. exists (pool sd + 2 - n), false. reflexivity.
Qed.

(** ** States *)

Definition quiet (pd : pending) : Prop :=
  match pd with ChooseShuffle _ _ _ => False | _ => True end.

Lemma shuffling_quiet p s : quiet s.(pend) -> shuffling p s = [].
Proof. unfold shuffling. destruct (pend s); easy. Qed.

Lemma walker_count_quiet p s : quiet s.(pend) -> walker_count p s = side_walkers (get_side p s).
Proof.
  intros Hq. unfold walker_count. rewrite shuffling_quiet, app_nil_r by exact Hq. reflexivity.
Qed.

Lemma elixir_count_quiet p s : quiet s.(pend) -> elixir_count p s = side_elixirs (get_side p s).
Proof.
  intros Hq. unfold elixir_count. rewrite shuffling_quiet, app_nil_r by exact Hq. reflexivity.
Qed.

Lemma elixirs_le_1 p s : well_formed s -> quiet s.(pend) -> side_elixirs (get_side p s) <= 1.
Proof.
  intros [(_ & HA & _ & HB) _] Hq. rewrite <- elixir_count_quiet by exact Hq.
  destruct p; lia.
Qed.

(** The card part of [well_formed] only depends on the card counts, between quiet states. *)
Lemma cards_same s s' :
  cards_conserved s -> quiet s.(pend) -> quiet s'.(pend) ->
  (forall p, side_walkers (get_side p s') = side_walkers (get_side p s) /\
             side_elixirs (get_side p s') = side_elixirs (get_side p s)) ->
  cards_conserved s' /\ shuffled_library_empty s'.
Proof.
  intros Hc Hq Hq' Hs. split.
  - unfold cards_conserved in *.
    rewrite !walker_count_quiet, !elixir_count_quiet in * by assumption.
    destruct (Hs PA) as [-> ->], (Hs PB) as [-> ->]. exact Hc.
  - intros st p cards E. rewrite E in Hq'. destruct Hq'.
Qed.

Lemma combat_none s : s.(cmb) = no_combat -> attackers_exist s /\ blockers_exist s /\ thopters_exist s.
Proof.
  unfold attackers_exist, blockers_exist, thopters_exist, blocking_walkers, blocking_thopters.
  intros ->. cbn. repeat split; try constructor; lia.
Qed.

(** The combat part of [well_formed] survives growing battlefields. *)
Lemma combat_same s s' :
  well_formed s -> s'.(active) = s.(active) -> s'.(cmb) = s.(cmb) ->
  (forall p, length (get_side p s).(bf) <= length (get_side p s').(bf) /\
             (get_side p s').(thop_u) = (get_side p s).(thop_u) /\
             (get_side p s').(thop_t) = (get_side p s).(thop_t)) ->
  attackers_exist s' /\ blockers_exist s' /\ thopters_exist s'.
Proof.
  intros Hwf Ha Hc Hs.
  destruct Hwf as (_ & _ & (Hnd & Hat & Hlb) & (Hbn & Hbf) & Ht).
  unfold attackers_exist, blockers_exist, thopters_exist, defender in *.
  rewrite Ha, Hc.
  destruct (Hs (active s)) as (Hla & Hua & Hta).
  destruct (Hs (opp (active s))) as (Hld & Hud & Htd).
  repeat split; try assumption; try lia.
  - eapply Forall_impl; [| exact Hat]. cbn. lia.
  - eapply Forall_impl; [| exact Hbf]. cbn. lia.
Qed.

Lemma wf_same s s' :
  well_formed s -> quiet s.(pend) -> quiet s'.(pend) ->
  s'.(active) = s.(active) -> s'.(cmb) = s.(cmb) ->
  (forall p, same_counts (get_side p s) (get_side p s')) ->
  well_formed s'.
Proof.
  intros Hwf Hq Hq' Ha Hc Hs.
  destruct (cards_same s s') as [Hcc Hsh];
    [exact (proj1 Hwf) | assumption .. | intros p; destruct (Hs p) as (? & ? & _); auto |].
  split; [exact Hcc | split; [exact Hsh |]].
  apply (combat_same s); [assumption .. |].
  intros p. destruct (Hs p) as (_ & _ & ? & ? & ?). auto.
Qed.

Lemma wf_fresh s s' :
  well_formed s -> quiet s.(pend) -> quiet s'.(pend) -> s'.(cmb) = no_combat ->
  (forall p, side_walkers (get_side p s') = side_walkers (get_side p s) /\
             side_elixirs (get_side p s') = side_elixirs (get_side p s)) ->
  well_formed s'.
Proof.
  intros Hwf Hq Hq' Hc Hs.
  destruct (cards_same s s') as [Hcc Hsh]; [exact (proj1 Hwf) | assumption .. |].
  split; [| split]; auto using combat_none.
Qed.

Lemma get_set_side p sd s : get_side p (set_side p sd s) = sd.
Proof. destruct p; reflexivity. Qed.

Lemma set_set_side p sd sd' s : set_side p sd (set_side p sd' s) = set_side p sd s.
Proof. destruct p; reflexivity. Qed.

Lemma wf_side p sd s :
  well_formed s -> quiet s.(pend) -> same_counts (get_side p s) sd ->
  well_formed (set_side p sd s).
Proof.
  intros Hwf Hq Hs. apply (wf_same s); [assumption | assumption | | | |].
  - destruct p; exact Hq.
  - destruct p; reflexivity.
  - destruct p; reflexivity.
  - intros q. destruct p, q; cbn in *; auto using same_counts_refl.
Qed.

Lemma wf_pend pd s : well_formed s -> quiet s.(pend) -> quiet pd -> well_formed (set_pend pd s).
Proof.
  intros Hwf Hq Hq'. apply (wf_same s); auto.
  intros [|]; apply same_counts_refl.
Qed.

Lemma quiet_set_side p sd s : quiet s.(pend) -> quiet (set_side p sd s).(pend).
Proof. destruct p; auto. Qed.

(** A side update paid for with [with_payment]. *)
Lemma wf_with_payment n p s st f :
  well_formed s -> quiet s.(pend) ->
  (forall pl ct, same_counts (get_side p s) (f (set_pool pl (set_city ct (get_side p s))))) ->
  well_formed (with_payment n p s (fun s => set_pend (Window st p false) (map_side p f s))).
Proof.
  intros Hwf Hq Hf. unfold with_payment.
  destruct (pay n (get_side p s)) as [sd |] eqn:Hp; [| exact Hwf].
  unfold map_side. rewrite get_set_side, set_set_side.
  apply wf_pend; [| apply quiet_set_side; exact Hq | exact I].
  apply wf_side; [assumption .. |]. apply pay_shape in Hp as (pl & ct & ->). apply Hf.
Qed.

Lemma count_walkers_repeat n : count_occ card_eq_dec (repeat CWalker n) CWalker = n.
Proof. apply count_occ_repeat_eq. reflexivity. Qed.

Lemma count_elixirs_repeat n : count_occ card_eq_dec (repeat CWalker n) CElixir = 0.
Proof. apply count_occ_repeat_neq. discriminate. Qed.

(** ** Shuffles *)

Lemma wf_elixir st p s :
  well_formed s -> quiet s.(pend) -> elixir_bf (get_side p s) = true ->
  well_formed (do_elixir st p s).
Proof.
  intros Hwf Hq He. unfold do_elixir, with_payment.
  destruct (pay 2 (get_side p s)) as [sd |] eqn:Hpay; [| exact Hwf].
  apply pay_shape in Hpay as (pl & ct & ->). cbv zeta. rewrite get_set_side, set_set_side.
  split; [| split].
  - destruct Hwf as [Hc _]. unfold cards_conserved in *.
    rewrite !walker_count_quiet, !elixir_count_quiet in Hc by exact Hq.
    destruct s as [act ft A B c pd].
    unfold walker_count, elixir_count, shuffling, side_walkers, side_elixirs in *.
    destruct p; cbn in He, Hc |- *; rewrite He in Hc; cbn in Hc;
      rewrite ?count_occ_app, ?count_walkers_repeat, ?count_elixirs_repeat, ?He; cbn;
      rewrite ?count_occ_app, ?count_walkers_repeat, ?count_elixirs_repeat in *; cbn in *; lia.
  - intros st' q cards E. destruct p; cbn in E |- *; injection E as <- <- <-; reflexivity.
  - apply (combat_same s); [exact Hwf | destruct p; reflexivity | destruct p; reflexivity |].
    intros q. destruct p, q; cbn; repeat split; lia.
Qed.

Lemma wf_arrange st p cards lib s :
  well_formed s -> s.(pend) = ChooseShuffle st p cards -> In lib (orders card_eq_dec cards) ->
  well_formed (set_pend (Window st p false) (map_side p (set_library lib) s)).
Proof.
  intros Hwf Hp Hin.
  apply orders_perm in Hin. rewrite (Permutation_count_occ card_eq_dec) in Hin.
  split; [| split].
  - destruct Hwf as [Hc [Hsh _]]. specialize (Hsh st p cards Hp).
    destruct s as [act ft A B c pd]; cbn in Hp; subst pd.
    unfold cards_conserved, walker_count, elixir_count, shuffling in *.
    destruct p; cbn in Hc, Hsh |- *; rewrite Hsh in Hc; cbn in Hc;
      pose proof (Hin CWalker); pose proof (Hin CElixir); rewrite ?app_nil_r in *; lia.
  - intros st' q cards' E. destruct p; discriminate E.
  - apply (combat_same s); [exact Hwf | destruct p; reflexivity | destruct p; reflexivity |].
    intros q. destruct p, q; cbn; repeat split; lia.
Qed.

(** ** Priority windows *)

Lemma same_counts_draw sd : side_elixirs sd <= 1 -> same_counts sd (draw sd).
Proof.
  unfold draw, same_counts, side_walkers, side_elixirs. intros Hle.
  destruct (library sd) as [| [|] r] eqn:El; cbn in Hle |- *; rewrite ?El; cbn;
    repeat split; lia.
Qed.

Lemma same_counts_untap sd :
  side_walkers (untap_side sd) = side_walkers sd /\ side_elixirs (untap_side sd) = side_elixirs sd.
Proof.
  unfold side_walkers, side_elixirs. cbn. rewrite length_map. split; reflexivity.
Qed.

Lemma wf_empty_pools s : well_formed s -> quiet s.(pend) ->
  well_formed (empty_pools s) /\ quiet (empty_pools s).(pend) /\
  (empty_pools s).(active) = s.(active) /\ (empty_pools s).(first_turn) = s.(first_turn) /\
  (empty_pools s).(cmb) = s.(cmb).
Proof.
  intros Hwf Hq. unfold empty_pools, map_side.
  assert (well_formed (set_side PB (set_pool 0 (get_side PB s)) s)) as H1
    by (apply wf_side; [assumption .. | solve_counts]).
  split; [| split; [exact Hq | repeat split]].
  apply wf_side; [exact H1 | exact Hq | solve_counts].
Qed.

Lemma wf_end_step st s : well_formed s -> quiet s.(pend) -> well_formed (end_step st s).
Proof.
  intros Hwf Hq. unfold end_step.
  destruct (wf_empty_pools s Hwf Hq) as (Hwf0 & Hq0 & Ha0 & Hf0 & Hc0).
  generalize dependent (empty_pools s). intros s0 Hwf0 Hq0 Ha0 Hf0 Hc0.
  destruct st; cbn zeta.
  - apply wf_pend; [| | exact I].
    + destruct (first_turn s0); [exact Hwf0 |]. unfold map_side.
      apply wf_side; [assumption .. |]. apply same_counts_draw, elixirs_le_1; assumption.
    + destruct (first_turn s0); [exact Hq0 |]. apply quiet_set_side, Hq0.
  - apply wf_pend; easy.
  - apply wf_pend; easy.
  - apply wf_pend; easy.
  - destruct (atk (cmb s0)), (atk_thop (cmb s0)); apply wf_pend; easy.
  - apply wf_pend; easy.
  - apply wf_pend; easy.
  - apply (wf_fresh s0); [assumption .. | exact I | reflexivity |].
    intros p. split; reflexivity.
  - apply wf_pend; easy.
  - unfold next_turn. apply (wf_fresh s0); [assumption .. | exact I | reflexivity |].
    intros p. cbn. unfold map_side.
    destruct (opp (active s0)), p; cbn; first [apply same_counts_untap | split; reflexivity].
Qed.

Lemma wf_window st p passed s m :
  well_formed s -> s.(pend) = Window st p passed -> In m (window_moves st p s) ->
  well_formed (match m with
               | Pass => if passed then end_step st s else set_pend (Window st (opp p) true) s
               | Pump i => do_pump st p i s
               | ActElixir => do_elixir st p s
               | CastWalker x => do_cast_walker st p x s
               | CastElixir => do_cast_elixir st p s
               | _ => s
               end).
Proof.
  intros Hwf Hp Hin.
  assert (Hq : quiet s.(pend)) by (rewrite Hp; exact I).
  unfold window_moves in Hin. destruct Hin as [<- | Hin].
  { destruct passed; [apply wf_end_step | apply wf_pend]; easy. }
  apply in_app_iff in Hin as [Hin | Hin].
  { destruct (can_pay 1 _); [| destruct Hin].
    apply in_map_iff in Hin as (i & <- & _).
    apply wf_with_payment; [assumption .. |]. intros pl ct.
    unfold same_counts, side_walkers, side_elixirs; cbn -[update_nth].
    rewrite length_update_nth. repeat split; lia. }
  apply in_app_iff in Hin as [Hin | Hin].
  { destruct (elixir_bf (get_side p s) && can_pay 2 _) eqn:E; [| destruct Hin].
    destruct Hin as [<- | []]. apply andb_prop in E as [Ee _].
    apply wf_elixir; assumption. }
  destruct (player_eqb p (active s) && is_main st); [| destruct Hin].
  apply in_app_iff in Hin as [Hin | Hin].
  - destruct (0 <? hand_w (get_side p s)) eqn:Eh; [| destruct Hin]. apply Nat.ltb_lt in Eh.
    assert (forall x, well_formed (do_cast_walker st p x s)) as Hcast.
    { intros x. unfold do_cast_walker, with_payment.
      destruct (pay (2 * x) (get_side p s)) as [sd |] eqn:Hpay; [| exact Hwf].
      cbv zeta. rewrite get_set_side, set_set_side.
      apply wf_pend; [| apply quiet_set_side, Hq | exact I].
      apply wf_side; [assumption .. |].
      apply pay_shape in Hpay as (pl & ct & ->).
      destruct x; solve_counts. }
    destruct Hin as [<- | Hin]; [apply Hcast |].
    destruct (can_pay 2 _); [destruct Hin as [<- | []]; apply Hcast | destruct Hin].
  - destruct (hand_e (get_side p s) && can_pay 1 _) eqn:E; [| destruct Hin].
    destruct Hin as [<- | []]. apply andb_prop in E as [Eh _].
    pose proof (elixirs_le_1 p s Hwf Hq) as Hle.
    apply wf_with_payment; [assumption .. |]. intros pl ct. revert Hle.
    unfold same_counts, side_walkers, side_elixirs. cbn. rewrite Eh. cbn.
    intros. repeat split; lia.
Qed.

(** ** Combat *)

Lemma get_side_set_cmb p c s : get_side p (set_cmb c s) = get_side p s.
Proof. destruct p; reflexivity. Qed.

Lemma walker_count_set_cmb p c s : walker_count p (set_cmb c s) = walker_count p s.
Proof. destruct p; reflexivity. Qed.

Lemma elixir_count_set_cmb p c s : elixir_count p (set_cmb c s) = elixir_count p s.
Proof. destruct p; reflexivity. Qed.

(** A new combat that refers to existing Walkers and Thopters. *)
Lemma wf_set_cmb s c :
  cards_conserved s -> quiet s.(pend) ->
  indices_below (length (get_side s.(active) s).(bf)) c.(atk) ->
  length c.(blk) = length c.(atk) ->
  indices_below (length (get_side (opp s.(active)) s).(bf)) (blocking_walkers c) ->
  c.(trades) <= c.(atk_thop) <= (get_side s.(active) s).(thop_t) ->
  blocking_thopters c + c.(trades) <= (get_side (opp s.(active)) s).(thop_u) ->
  well_formed (set_cmb c s).
Proof.
  intros Hc Hq [Han Hal] Hlb [Hbn Hbl] Ht Hu.
  split; [| split; [| split; [| split]]].
  - unfold cards_conserved in *.
    rewrite !walker_count_set_cmb, !elixir_count_set_cmb. exact Hc.
  - intros st p cards E. cbn in E. rewrite E in Hq. destruct Hq.
  - unfold attackers_exist. cbn [cmb active set_cmb]. rewrite get_side_set_cmb. auto.
  - unfold blockers_exist, defender. cbn [cmb active set_cmb]. rewrite get_side_set_cmb. auto.
  - unfold thopters_exist, defender. cbn [cmb active set_cmb]. rewrite !get_side_set_cmb. auto.
Qed.

Lemma concat_nils {A B} (l : list A) : concat (map (fun _ => @nil B) l) = [].
Proof. induction l; cbn; auto. Qed.

Lemma wf_attack s ws k :
  well_formed s -> s.(pend) = ChooseAttack ->
  In ws (subsets (indices_where (fun _ w => can_pump w) (get_side s.(active) s).(bf))) ->
  well_formed (do_attack ws k s).
Proof.
  intros Hwf Hp Hws. apply subsets_sublist in Hws.
  pose proof (indices_below_sublist _ _ _ Hws (indices_where_below _ _)) as Hb.
  destruct Hwf as (Hc & _ & _ & _ & _).
  destruct s as [act ft A B c pd]; cbn in Hp, Hb; subst pd.
  unfold do_attack. destruct act; apply wf_pend; try exact I.
  all: apply wf_set_cmb; [eapply proj1, (cards_same _ _ Hc); [exact I | exact I |] | exact I | ..].
  all: try (intros q; destruct q; unfold side_walkers, side_elixirs; cbn -[update_nth];
            rewrite ?length_tap_all; split; reflexivity).
  all: cbn -[update_nth]; rewrite ?length_tap_all, ?length_map; try lia; try exact Hb.
  all: unfold blocking_walkers, blocking_thopters; cbn; rewrite concat_nils; cbn;
    try split; try constructor; lia.
Qed.

Lemma bw_blocks (g : nat -> list nat) (l : list (nat * nat)) :
  flat_map (fun b => match b with BW i => [i] | BT => [] end)
    (concat (map (fun '(a, k) => map BW (g a) ++ repeat BT k) l))
  = flat_map (fun '(a, _) => g a) l.
Proof.
  assert (H1 : forall xs, flat_map (fun b => match b with BW i => [i] | BT => [] end)
                            (map BW xs) = xs) by (induction xs; cbn; congruence).
  assert (H2 : forall k, flat_map (fun b => match b with BW i => [i] | BT => [] end)
                           (repeat BT k) = []) by (induction k; cbn; auto).
  induction l as [| [a k] l IH]; cbn; [reflexivity |].
  rewrite !flat_map_app, H1, H2, IH, app_nil_r. reflexivity.
Qed.

Lemma count_blocks (g : nat -> list nat) (l : list (nat * nat)) :
  count_occ blocker_eq_dec (concat (map (fun '(a, k) => map BW (g a) ++ repeat BT k) l)) BT
  = list_sum (map snd l).
Proof.
  assert (H1 : forall xs, count_occ blocker_eq_dec (map BW xs) BT = 0) by (induction xs; cbn; auto).
  induction l as [| [a k] l IH]; cbn; [reflexivity |].
  rewrite !count_occ_app, H1, IH, count_occ_repeat_eq by reflexivity. reflexivity.
Qed.

Lemma wf_block s wb tb tr :
  well_formed s -> s.(pend) = ChooseBlock ->
  In wb (product (map (fun w => if w.(wtapped) then [None]
                                else None :: map Some (seq 0 (length s.(cmb).(atk))))
                      (get_side (defender s) s).(bf))) ->
  In tb (bounded_vectors (length s.(cmb).(atk)) (get_side (defender s) s).(thop_u)) ->
  tr <= Nat.min ((get_side (defender s) s).(thop_u) - list_sum tb) s.(cmb).(atk_thop) ->
  well_formed (do_block wb tb tr s).
Proof.
  unfold defender. intros Hwf Hp Hwb Htb Htr.
  apply in_product, Forall2_length in Hwb. rewrite length_map in Hwb.
  apply in_bounded_vectors in Htb as [Hlt Hst].
  destruct Hwf as (Hc & _ & (Han & Hal & Hlb) & _ & (Ht1 & Ht2)).
  assert (Hq : quiet (pend s)) by (rewrite Hp; exact I).
  unfold do_block. cbv zeta.
  set (ix := fun a => indices_where (fun _ o => match o with Some b => b =? a | None => false end) wb).
  match goal with |- context [set_cmb ?c s] => set (c' := c) end.
  assert (Hwf' : well_formed (set_cmb c' s)).
  { apply wf_set_cmb; [exact Hc | exact Hq | unfold c'; cbn [atk blk trades atk_thop] ..].
    - split; assumption.
    - rewrite length_map, length_enum. lia.
    - unfold blocking_walkers. cbn [blk]. rewrite (bw_blocks ix). split.
      + apply NoDup_flat_map; [apply NoDup_enum | intros [a k] _; apply indices_where_below |].
        intros [a k] [a' k'] i Hx Hy Hi Hi'. cbn in Hi, Hi'.
        apply in_indices_where in Hi as (o & Ho & Eo), Hi' as (o' & Ho' & Eo').
        rewrite (enum_functional _ _ _ _ Ho Ho') in Eo.
        destruct o' as [b |]; [| discriminate].
        apply Nat.eqb_eq in Eo, Eo'. subst a a'.
        f_equal. eapply enum_functional; eassumption.
      + apply Forall_forall. intros i Hi. apply in_flat_map in Hi as ([a k] & _ & Hi).
        cbn in Hi. destruct (indices_where_below
          (fun _ o => match o with Some b => b =? a | None => false end) wb) as [_ Hf].
        rewrite Forall_forall in Hf. specialize (Hf i Hi). lia.
    - lia.
    - unfold blocking_thopters. cbn [blk]. rewrite (count_blocks ix), map_snd_enum. lia. }
  destruct (has_multiblock c'); apply wf_pend; first [exact Hwf' | exact Hq | exact I].
Qed.

Lemma wf_order s os :
  well_formed s -> s.(pend) = ChooseOrder ->
  In os (product (map (orders blocker_eq_dec) s.(cmb).(blk))) ->
  well_formed (do_order os s).
Proof.
  intros Hwf Hp Hos.
  apply in_product, Forall2_map_r in Hos.
  assert (Hperm : Forall2 (@Permutation blocker) os s.(cmb).(blk))
    by (eapply Forall2_impl'; [| exact Hos]; intros x y; apply orders_perm).
  apply Forall2_length in Hos.
  apply Permutation_concat in Hperm.
  destruct Hwf as (Hc & _ & (Han & Hal & Hlb) & (Hbn & Hbf) & (Ht1 & Ht2)).
  assert (Hq : quiet (pend s)) by (rewrite Hp; exact I).
  unfold do_order. apply wf_pend; [| exact Hq | exact I].
  apply wf_set_cmb; [exact Hc | exact Hq | cbn [atk blk trades atk_thop] ..].
  - split; assumption.
  - lia.
  - apply (indices_below_perm _ (blocking_walkers (cmb s))); [| split; assumption].
    unfold blocking_walkers. apply Permutation_flat_map. symmetry. exact Hperm.
  - lia.
  - unfold blocking_thopters in *.
    rewrite (proj1 (Permutation_count_occ blocker_eq_dec _ _) Hperm). exact Ht2.
Qed.

(** ** Combat damage *)

Lemma sublist_fights_atk {A B C} (xs : list A) (ys : list B) (zs : list C) :
  sublist (map (fun '(i, _, _) => i) (combine (combine xs ys) zs)) xs.
Proof.
  revert ys zs; induction xs as [| x xs IH]; intros [| y ys] [| z zs]; cbn;
    try apply sublist_nil_l.
  apply sl_keep, IH.
Qed.

Lemma sublist_killed {A B} (xs : list A) (bss : list (list B)) (js : list nat) :
  sublist (flat_map (fun '(_, bs, j) => firstn j bs) (combine (combine xs bss) js)) (concat bss).
Proof.
  revert xs js; induction bss as [| bs bss IH]; intros [| x xs] [| j js]; cbn;
    try apply sublist_nil_l.
  apply sublist_app; [apply sublist_firstn | apply IH].
Qed.

Lemma side_counts_bury dead sd :
  indices_below (length sd.(bf)) dead ->
  side_walkers (bury dead sd) = side_walkers sd /\ side_elixirs (bury dead sd) = side_elixirs sd.
Proof.
  intros H. unfold bury, side_walkers, side_elixirs. cbn -[remove_indices].
  pose proof (remove_indices_length dead (bf sd) H). split; lia.
Qed.

Lemma wf_damage s js : well_formed s -> s.(pend) = ChooseDamage -> well_formed (do_damage js s).
Proof.
  intros Hwf Hp.
  pose proof Hwf as (_ & _ & (Han & Hal & _) & (Hbn & Hbf) & _).
  destruct s as [act ft A B c pd]; cbn in Hp; subst pd.
  unfold do_damage. cbv zeta.
  destruct act; cbn [get_side active cmb defender opp sideA sideB] in *.
  all: match goal with |- context [bury ?x (set_thop_t _ ?sd)] =>
         set (a_dead := x);
         assert (Ha : indices_below (length (bf sd)) a_dead)
           by (apply indices_below_sublist with (atk c); [| split; assumption];
               eapply sublist_trans; [apply sublist_map, sublist_filter | apply sublist_fights_atk]);
         clearbody a_dead
       end.
  all: match goal with |- context [bury ?x (set_thop_u _ ?sd)] =>
         set (d_dead := x);
         assert (Hd : indices_below (length (bf sd)) d_dead)
           by (apply indices_below_sublist with (blocking_walkers c); [| split; assumption];
               unfold blocking_walkers; apply sublist_flat_map, sublist_killed);
         clearbody d_dead
       end.
  all: destruct (_ <=? _);
    (eapply wf_fresh; [exact Hwf | exact I | exact I | reflexivity |]);
    intros q; destruct q; cbn [get_side set_pend set_cmb set_side map_side sideA sideB];
    first [exact (side_counts_bury _ _ Ha) | exact (side_counts_bury _ _ Hd)].
Qed.

(** ** The theorems *)

Theorem init_wf : init_well_formed.
Proof.
  intros p. destruct p; repeat split; cbn; try constructor; try lia; discriminate.
Qed.

Theorem preservation_wf : preservation.
Proof.
  intros s m Hwf Hin. unfold step. unfold moves in Hin.
  destruct (pend s) as [st p passed | | | | | st p cards | w] eqn:Hp.
  - eapply wf_window; eassumption.
  - unfold attack_moves in Hin. apply in_flat_map in Hin as (ws & Hws & Hin).
    apply in_map_iff in Hin as (k & <- & _). apply wf_attack; assumption.
  - unfold block_moves in Hin. apply in_flat_map in Hin as (wb & Hwb & Hin).
    apply in_flat_map in Hin as (tb & Htb & Hin). apply in_map_iff in Hin as (tr & <- & Htr).
    apply in_seq in Htr. apply wf_block; try assumption. lia.
  - unfold order_moves in Hin. apply in_map_iff in Hin as (os & <- & Hos).
    apply wf_order; assumption.
  - unfold damage_moves in Hin. apply in_map_iff in Hin as (js & <- & _).
    apply wf_damage; assumption.
  - apply in_map_iff in Hin as (lib & <- & Hlib). eapply wf_arrange; eassumption.
  - destruct Hin.
Qed.
