(** * The simulation facts behind [Checker.cert_safe] (REDUCTION.md R4)

    [Checker.R s t] says the certificate-side state [s] abstracts the real
    state [t]: A's huge Walkers (at least [H] counters) may differ in size,
    A's graveyard may differ, and B may have more life and Thopters in [t].
    This file proves what [cert_safe] assumes about it, starting with the
    move lists. *)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.
From TCB.Spec Require Import Model Game.
From TCB.Proofs Require Import Mono Checker.

Section Saturation.

Variables H ott tt : nat.

Notation R := (R H).
Notation walker_rel := (walker_rel H).
Notation huge_event := (huge_event H).

(** ** Lists that only read related parts *)

Lemma indices_where_rel : forall {A B} (P : A -> B -> Prop) (f : nat -> A -> bool) (g : nat -> B -> bool) l l',
  Forall2 P l l' -> (forall i x y, P x y -> f i x = g i y) ->
  indices_where f l = indices_where g l'.
Proof.
  intros A B P f g l l' HP Hfg. unfold indices_where, enum.
  rewrite <- (Forall2_length HP). generalize 0.
  induction HP as [| x y l l' Hxy HP IH]; intros i; [reflexivity |].
  cbn [length seq combine filter]. rewrite (Hfg i x y Hxy).
  destruct (g i y); cbn [map]; [f_equal |]; apply IH.
Qed.

Lemma ready_rel : forall l l', Forall2 walker_rel l l' ->
  indices_where (fun _ w => can_pump w) l = indices_where (fun _ w => can_pump w) l'.
Proof.
  intros l l' Hl. apply (indices_where_rel _ _ _ _ _ Hl).
  intros _ [c tp sk] [c' tp' sk'] (Et & Es & _). cbn in *. unfold can_pump. cbn. congruence.
Qed.

Lemma map_tapped_rel : forall {X} (h : bool -> X) l l', Forall2 walker_rel l l' ->
  map (fun w => h w.(wtapped)) l = map (fun w => h w.(wtapped)) l'.
Proof.
  intros X h l l' Hl. induction Hl as [| x y l l' (Et & _) _ IH]; cbn; [reflexivity |].
  rewrite Et, IH. reflexivity.
Qed.

(** ** Damage choices *)

Lemma max_prefix_all : forall ts p, list_sum ts <= p -> max_prefix p ts = length ts.
Proof.
  induction ts as [| t ts IH]; intros p Hs; [reflexivity |].
  cbn [max_prefix length]. unfold list_sum in *; cbn [fold_right] in Hs.
  destruct (Nat.leb_spec t p); [| lia]. f_equal. apply IH. lia.
Qed.

(** An attacker's choices don't depend on its power once it can kill all
    its blockers. *)
Lemma kill_choices_big : forall p p' ts, ts <> [] -> list_sum ts < p -> list_sum ts < p' ->
  kill_choices p ts = kill_choices p' ts.
Proof.
  intros p p' [| t ts] Hne Hp Hp'; [congruence |]. unfold kill_choices.
  unfold list_sum in *; cbn [fold_right] in *.
  destruct (Nat.ltb_spec p t), (Nat.ltb_spec p' t); try lia.
  rewrite !max_prefix_all; unfold list_sum; cbn [fold_right]; [reflexivity | lia | lia].
Qed.

(** Nor on the exact toughness of blockers too big for it to kill. *)
Lemma max_prefix_rel : forall ts ts' p,
  Forall2 (fun x y => x = y \/ (p < x /\ p < y)) ts ts' -> max_prefix p ts = max_prefix p ts'.
Proof.
  induction ts as [| t ts IH]; intros ts' p Hr;
    destruct ts' as [| y ts']; inversion Hr as [| ? ? ? ? Hxy Hl]; subst; [reflexivity |].
  cbn [max_prefix]. destruct Hxy as [<- | (H1 & H2)].
  - destruct (Nat.leb_spec t p); [| reflexivity]. f_equal. apply IH.
    eapply Forall2_impl; [| exact Hl]. intros a b [E | (Ha & Hb)]; [left; exact E | right; lia].
  - destruct (Nat.leb_spec t p), (Nat.leb_spec y p); try lia; reflexivity.
Qed.

Lemma kill_choices_rel : forall p ts ts',
  Forall2 (fun x y => x = y \/ (p < x /\ p < y)) ts ts' -> kill_choices p ts = kill_choices p ts'.
Proof.
  intros p ts ts' Hr. unfold kill_choices.
  destruct Hr as [| x y l l' Hxy Hl]; [reflexivity |].
  rewrite (max_prefix_rel (x :: l) (y :: l') p); [| constructor; assumption].
  destruct Hxy as [<- | (H1 & H2)]; [reflexivity |].
  destruct (Nat.ltb_spec p x), (Nat.ltb_spec p y); try lia; reflexivity.
Qed.

(** ** Sides *)

Lemma strip_b_fields : forall b b', strip_b b = strip_b b' ->
  b.(city) = b'.(city) /\ b.(pool) = b'.(pool) /\ b.(hand_w) = b'.(hand_w) /\
  b.(hand_e) = b'.(hand_e) /\ b.(bf) = b'.(bf) /\ b.(elixir_bf) = b'.(elixir_bf) /\
  b.(library) = b'.(library) /\ b.(gy_w) = b'.(gy_w).
Proof.
  intros [] [] E. unfold strip_b in E. cbn in E. injection E. intros. subst. auto 10.
Qed.

Lemma can_pay_eq : forall n sd sd', sd.(pool) = sd'.(pool) -> sd.(city) = sd'.(city) ->
  can_pay n sd = can_pay n sd'.
Proof.
  intros n sd sd' Ep Ec. unfold can_pay, pay. rewrite Ep, Ec.
  destruct (n <=? pool sd'); [reflexivity |]. destruct (city sd' && _); reflexivity.
Qed.

Lemma power_rel : forall l l' i, Forall2 walker_rel l l' ->
  nth i (map counters l) 0 = nth i (map counters l') 0 \/
  (H <= nth i (map counters l) 0 /\ H <= nth i (map counters l') 0).
Proof.
  intros l l' i Hl. revert i.
  induction Hl as [| x y l l' (_ & _ & Hc) _ IH]; intros [| i]; cbn; auto.
Qed.

Lemma walker_power_rel : forall a a' i, Forall2 walker_rel a.(bf) a'.(bf) ->
  walker_power a i = walker_power a' i \/ (H <= walker_power a i /\ H <= walker_power a' i).
Proof. intros a a' i Hl. unfold walker_power. apply power_rel. exact Hl. Qed.

(** ** Move lists *)

Lemma window_eq : forall st p act ft a b a' b' c pd,
  sideA_rel H a a' -> sideB_rel b b' ->
  window_moves st p (mkState act ft a b c pd) = window_moves st p (mkState act ft a' b' c pd).
Proof.
  intros st p act ft a b a' b' c pd HA HB.
  destruct HA as (Hl & Hc & Hp & Hw & He & He' & Hx & Hx' & _ & _ & Hbf & _ & _).
  destruct HB as (_ & _ & _ & Hs). apply strip_b_fields in Hs.
  destruct Hs as (Hc2 & Hp2 & Hw2 & He2 & Hbf2 & Hx2 & _ & _).
  unfold window_moves; destruct p; cbn [get_side Model.sideA Model.sideB Model.active].
  - rewrite (can_pay_eq 1 a a'), (can_pay_eq 2 a a'), (ready_rel _ _ Hbf); auto.
    rewrite Hw, He, He', Hx, Hx'. reflexivity.
  - rewrite (can_pay_eq 1 b b'), (can_pay_eq 2 b b'); auto.
    rewrite Hw2, He2, Hbf2, Hx2. reflexivity.
Qed.

Lemma Forall2_map_same : forall {X Y} (P : Y -> Y -> Prop) (f g : X -> Y) l,
  (forall x, In x l -> P (f x) (g x)) -> Forall2 P (map f l) (map g l).
Proof.
  intros X Y P f g l Hfg. induction l as [| x l IH]; cbn; constructor.
  - apply Hfg. left. reflexivity.
  - apply IH. intros y Hy. apply Hfg. right. exact Hy.
Qed.

Lemma walker_power_bf : forall d d' i, d.(bf) = d'.(bf) -> walker_power d i = walker_power d' i.
Proof. intros d d' i E. unfold walker_power. rewrite E. reflexivity. Qed.

Lemma toughness_bf : forall d d' x, d.(bf) = d'.(bf) -> blocker_toughness d x = blocker_toughness d' x.
Proof. intros d d' [i |] E; cbn; [apply walker_power_bf; exact E | reflexivity]. Qed.

Lemma damage_eq : forall act ft a b a' b' c,
  sideA_rel H a a' -> sideB_rel b b' ->
  huge_event (mkState act ft a b c ChooseDamage) = false ->
  damage_moves (mkState act ft a b c ChooseDamage) =
  damage_moves (mkState act ft a' b' c ChooseDamage).
Proof.
  intros act ft a b a' b' c HA HB Hh.
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbf & _ & _).
  pose proof HB as (_ & _ & _ & Hs). apply strip_b_fields in Hs.
  destruct Hs as (_ & _ & _ & _ & Hbf2 & _ & _ & _).
  unfold damage_moves, Checker.huge_event, defender in *.
  destruct act; cbn [get_side opp Model.sideA Model.sideB Model.active Model.cmb Model.pend] in *;
    f_equal; f_equal; destruct c as [atk k blk tr]; cbn [Model.atk Model.blk] in *;
    clear k tr; revert blk Hh; induction atk as [| i atk IH]; intros [| bs blk] Hh;
    try reflexivity; cbn [combine map existsb] in *;
    apply orb_false_iff in Hh as (Hi & Hh); f_equal; try (apply IH; exact Hh).
  - (* A attacks *)
    rewrite (map_ext (blocker_toughness b) (blocker_toughness b')) by (intros; apply toughness_bf; exact Hbf2).
    destruct (walker_power_rel a a' i Hbf) as [E | (Hp & Hp')]; [rewrite E; reflexivity |].
    unfold is_huge in Hi. destruct (Nat.leb_spec H (walker_power a i)); [| lia].
    cbn [andb] in Hi. destruct bs as [| x bs]; [discriminate |].
    apply Nat.leb_gt in Hi.
    apply kill_choices_big; [discriminate | |]; rewrite <- (map_ext (blocker_toughness b)) by (intros; apply toughness_bf; exact Hbf2); lia.
  - (* B attacks *)
    rewrite (walker_power_bf b b' i Hbf2). apply kill_choices_rel. apply Forall2_map_same.
    intros [j |] Hj; [| left; reflexivity]. cbn [blocker_toughness].
    destruct (walker_power_rel a a' j Hbf) as [E | (Hp & Hp')]; [left; exact E | right].
    assert (Hq : walker_power b' i < H).
    { rewrite <- (walker_power_bf b b' i Hbf2).
      destruct (Nat.leb_spec H (walker_power b i)) as [Hle |]; [| lia].
      exfalso. cbn [andb] in Hi.
      assert (Hex : existsb (fun x => match x with BW j => is_huge H a j | BT => false end) bs = true).
      { apply existsb_exists. exists (BW j). split; [exact Hj |]. unfold is_huge. apply Nat.leb_le. exact Hp. }
      rewrite Hex in Hi. discriminate. }
    lia.
Qed.

Lemma wchoices_rel : forall n l l', Forall2 walker_rel l l' ->
  map (fun w => if w.(wtapped) then [None] else None :: map Some (seq 0 n)) l =
  map (fun w => if w.(wtapped) then [None] else None :: map Some (seq 0 n)) l'.
Proof.
  intros n l l' Hl. induction Hl as [| x y l l' (Et & _) _ IH]; cbn; [reflexivity |].
  rewrite Et, IH. reflexivity.
Qed.

(** The move lists agree, except where B's extra Thopters give B more
    attacks or blocks. *)
Lemma moves_eq : forall s t, R s t -> huge_event s = false ->
  ~ (s.(pend) = ChooseAttack /\ s.(active) = PB) ->
  ~ (s.(pend) = ChooseBlock /\ s.(active) = PA) ->
  moves t = moves s.
Proof.
  intros [act ft a b c pd] [act' ft' a' b' c' pd'] (E1 & E2 & E3 & E4 & _ & HA & HB) Hh N1 N2.
  cbn [Model.active Model.first_turn Model.cmb Model.pend Model.sideA Model.sideB] in *.
  subst act' ft' c' pd'.
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbf & Hu & _).
  unfold moves.
  destruct pd as [st p passed | | | | | st p cards | w].
  - symmetry. apply window_eq; assumption.
  - destruct act; [| exfalso; apply N1; split; reflexivity].
    unfold attack_moves. cbn [get_side Model.active Model.sideA].
    rewrite (ready_rel _ _ Hbf), Hu. reflexivity.
  - destruct act; [exfalso; apply N2; split; reflexivity |].
    unfold block_moves, defender. cbn [get_side opp Model.active Model.sideA Model.cmb].
    rewrite (wchoices_rel _ _ _ Hbf), Hu. reflexivity.
  - reflexivity.
  - symmetry. apply damage_eq; assumption.
  - reflexivity.
  - reflexivity.
Qed.

Lemma moves_incl : forall s t m, R s t ->
  (s.(pend) = ChooseAttack /\ s.(active) = PB \/ s.(pend) = ChooseBlock /\ s.(active) = PA) ->
  In m (moves s) -> In m (moves t).
Proof.
  intros [act ft a b c pd] [act' ft' a' b' c' pd'] m (E1 & E2 & E3 & E4 & _ & HA & HB) Hc Hin.
  cbn [Model.active Model.first_turn Model.cmb Model.pend Model.sideA Model.sideB] in *.
  subst act' ft' c' pd'.
  destruct HB as (_ & Hu & _ & Hs). apply strip_b_fields in Hs.
  destruct Hs as (_ & _ & _ & _ & Hbf & _ & _ & _).
  unfold moves in *.
  destruct Hc as [(-> & ->) | (-> & ->)].
  - unfold attack_moves in *. cbn [get_side Model.active Model.sideB] in *. rewrite <- Hbf.
    apply in_flat_map in Hin as [ws [Hws Hin]]. apply in_map_iff in Hin as [k [<- Hk]].
    apply in_seq in Hk. apply in_flat_map. exists ws. split; [exact Hws |].
    apply in_map. apply in_seq. lia.
  - unfold block_moves, defender in *. cbn [get_side opp Model.active Model.sideB Model.cmb] in *.
    rewrite <- Hbf.
    apply in_flat_map in Hin as [wb [Hwb Hin]]. apply in_flat_map in Hin as [tb [Htb Hin]].
    apply in_map_iff in Hin as [k [<- Hk]]. apply in_seq in Hk.
    apply in_flat_map. exists wb. split; [exact Hwb |].
    apply in_flat_map. exists tb. split; [eapply bounded_vectors_mono; [| exact Htb]; lia |].
    apply in_map. apply in_seq. lia.
Qed.

(** [Checker.cert_safe]'s first two hypotheses. *)
Theorem sim_theirs : forall s t m,
  R s t -> to_move s = PA -> winner s = None -> huge_event s = false ->
  In m (moves t) -> In m (moves s).
Proof.
  intros s t m HR Hm _ Hh Hin. rewrite (moves_eq s t HR Hh) in Hin; [exact Hin | |];
    intros [E1 E2]; unfold to_move in Hm; rewrite E1, E2 in Hm; discriminate.
Qed.

Theorem sim_mine : forall s t m,
  R s t -> to_move s = PB -> winner s = None -> huge_event s = false ->
  In m (moves s) -> In m (moves t).
Proof.
  intros s t m HR Hm _ Hh Hin.
  destruct (pend s) eqn:Ep; try (rewrite (moves_eq s t HR Hh); [exact Hin | rewrite Ep; intros [E _]; discriminate | rewrite Ep; intros [E _]; discriminate]).
  - destruct (active s) eqn:Ea.
    + rewrite (moves_eq s t HR Hh); [exact Hin | rewrite Ep, Ea; intros [_ E]; discriminate | rewrite Ep; intros [E _]; discriminate].
    + apply (moves_incl s t m HR); [left; split; assumption | exact Hin].
  - destruct (active s) eqn:Ea.
    + apply (moves_incl s t m HR); [right; split; assumption | exact Hin].
    + rewrite (moves_eq s t HR Hh); [exact Hin | rewrite Ep; intros [E _]; discriminate | rewrite Ep, Ea; intros [_ E]; discriminate].
Qed.

(** ** Steps on A's side

    [RA s u]: as [R], but with B's sides equal. [R] factors through it and
    the two relations of [Mono.v] for B's life and Thopters. *)

Definition RA (s u : state) : Prop :=
  s.(active) = u.(active) /\ s.(first_turn) = u.(first_turn) /\
  s.(cmb) = u.(cmb) /\ s.(pend) = u.(pend) /\ no_a_shuffle s.(pend) /\
  sideA_rel H s.(sideA) u.(sideA) /\ s.(sideB) = u.(sideB).

Lemma walker_rel_pump : forall w w', walker_rel w w' -> walker_rel (pump_walker w) (pump_walker w').
Proof. intros [] [] (E1 & E2 & E3). unfold walker_rel, pump_walker in *; cbn in *. repeat split; auto. lia. Qed.

Lemma walker_rel_tap : forall w w', walker_rel w w' -> walker_rel (tap_walker w) (tap_walker w').
Proof. intros [] [] (E1 & E2 & E3). unfold walker_rel, tap_walker in *; cbn in *. repeat split; auto. Qed.

Lemma walker_rel_untap : forall w w', walker_rel w w' ->
  walker_rel (mkWalker w.(counters) false false) (mkWalker w'.(counters) false false).
Proof. intros [] [] (E1 & E2 & E3). unfold walker_rel in *; cbn in *. repeat split; auto. Qed.

Lemma F2_update : forall f i l l', Forall2 walker_rel l l' ->
  (forall w w', walker_rel w w' -> walker_rel (f w) (f w')) ->
  Forall2 walker_rel (update_nth i f l) (update_nth i f l').
Proof.
  intros f i l l' Hl Hf. unfold update_nth, enum.
  rewrite <- (Forall2_length Hl). generalize 0.
  induction Hl as [| x y l l' Hxy Hl IH]; intros k; cbn [length seq combine map]; constructor; auto.
  destruct (k =? i); auto.
Qed.

Lemma F2_taps : forall ws l l', Forall2 walker_rel l l' ->
  Forall2 walker_rel (fold_right (fun i l => update_nth i tap_walker l) l ws)
                     (fold_right (fun i l => update_nth i tap_walker l) l' ws).
Proof.
  intros ws l l' Hl. induction ws as [| i ws IH]; cbn; [exact Hl |].
  apply F2_update; [exact IH | apply walker_rel_tap].
Qed.

Lemma F2_untap : forall l l', Forall2 walker_rel l l' ->
  Forall2 walker_rel (map (fun w => mkWalker w.(counters) false false) l)
                     (map (fun w => mkWalker w.(counters) false false) l').
Proof.
  intros l l' Hl. induction Hl; cbn; constructor; auto. apply walker_rel_untap. assumption.
Qed.

Lemma F2_remove : forall dead l l', Forall2 walker_rel l l' ->
  Forall2 walker_rel (remove_indices dead l) (remove_indices dead l').
Proof.
  intros dead l l' Hl. unfold remove_indices, enum.
  rewrite <- (Forall2_length Hl). generalize 0.
  induction Hl as [| x y l l' Hxy Hl IH]; intros i; cbn [length seq combine filter map]; [constructor |].
  destruct (existsb (Nat.eqb i) dead); cbn [negb map]; [apply IH | constructor; [exact Hxy | apply IH]].
Qed.

Lemma F2_snoc : forall l l' w, Forall2 walker_rel l l' -> Forall2 walker_rel (l ++ [w]) (l' ++ [w]).
Proof.
  intros l l' w Hl. apply Forall2_app; [exact Hl |]. constructor; [| constructor].
  repeat split; auto.
Qed.

(** Rebuild [sideA_rel] for two sides given field by field. *)
Ltac sa_destruct HA :=
  let Hl := fresh "Hl" in let Hc := fresh "Hc" in let Hp := fresh "Hp" in
  let Hw := fresh "Hw" in let He := fresh "He" in let He' := fresh "He'" in
  let Hx := fresh "Hx" in let Hx' := fresh "Hx'" in let Hlib := fresh "Hlib" in
  let Elib := fresh "Elib" in let Hbf := fresh "Hbf" in let Hu := fresh "Hu" in
  let Ht := fresh "Ht" in
  destruct HA as (Hl & Hc & Hp & Hw & He & He' & Hx & Hx' & Hlib & Elib & Hbf & Hu & Ht).

Lemma sa_fields : forall l c p hw he bf e tu tt lib g l' c' p' hw' he' bf' e' tu' tt' lib' g',
  l = l' -> c = c' -> p = p' -> hw = hw' -> he = false -> he' = false -> e = false -> e' = false ->
  Forall (eq CWalker) lib -> lib = lib' -> Forall2 walker_rel bf bf' -> tu = tu' -> tt = tt' ->
  sideA_rel H (mkSide l c p hw he bf e tu tt lib g) (mkSide l' c' p' hw' he' bf' e' tu' tt' lib' g').
Proof. intros. unfold sideA_rel; cbn. repeat split; assumption. Qed.

Ltac sa_solve HA :=
  sa_destruct HA; cbn in *; apply sa_fields; try assumption; try congruence.

Lemma sa_set_pool : forall n a a', sideA_rel H a a' -> sideA_rel H (set_pool n a) (set_pool n a').
Proof. intros n [] [] HA. unfold set_pool. sa_solve HA. Qed.

Lemma sa_set_city : forall x a a', sideA_rel H a a' -> sideA_rel H (set_city x a) (set_city x a').
Proof. intros x [] [] HA. unfold set_city. sa_solve HA. Qed.

Lemma sa_pay : forall n a a', sideA_rel H a a' ->
  match pay n a, pay n a' with
  | Some x, Some y => sideA_rel H x y
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros n a a' HA. pose proof HA as HA'. sa_destruct HA'. unfold pay. rewrite Hp, Hc.
  destruct (n <=? pool a'); [apply sa_set_pool; exact HA |].
  destruct (city a' && (n <=? pool a' + 2)); [| exact I].
  apply sa_set_pool, sa_set_city. exact HA.
Qed.

Lemma sa_set_bf : forall l l' a a', sideA_rel H a a' -> Forall2 walker_rel l l' ->
  sideA_rel H (set_bf l a) (set_bf l' a').
Proof. intros l l' [] [] HA Hl. unfold set_bf. sa_solve HA. Qed.

Lemma sa_bf : forall a a', sideA_rel H a a' -> Forall2 walker_rel a.(bf) a'.(bf).
Proof. intros a a' HA. sa_destruct HA. exact Hbf. Qed.

Lemma sa_thops : forall u v a a', sideA_rel H a a' ->
  sideA_rel H (set_thop_t v (set_thop_u u a)) (set_thop_t v (set_thop_u u a')).
Proof. intros u v [] [] HA. unfold set_thop_t, set_thop_u. sa_solve HA. Qed.

Lemma sa_untap : forall a a', sideA_rel H a a' -> sideA_rel H (untap_side a) (untap_side a').
Proof.
  intros [] [] HA. pose proof (sa_bf _ _ HA) as Hb. unfold untap_side, set_thop_t, set_thop_u, set_bf, set_city.
  sa_solve HA. apply F2_untap; exact Hb.
Qed.

Lemma sa_draw : forall a a', sideA_rel H a a' -> sideA_rel H (draw a) (draw a').
Proof.
  intros [] [] HA. pose proof HA as HA'. sa_destruct HA'. cbn in *. subst library0.
  unfold draw; cbn. destruct library as [| [] r].
  - sa_solve HA.
  - unfold set_library, set_hand_w. sa_solve HA. inversion Hlib; assumption.
  - inversion Hlib. discriminate.
Qed.

Lemma sa_cast_walker : forall a a' x, sideA_rel H a a' ->
  sideA_rel H (match x with
               | 0 => set_gy_w (S (set_hand_w (pred a.(hand_w)) a).(gy_w)) (set_hand_w (pred a.(hand_w)) a)
               | _ => set_bf ((set_hand_w (pred a.(hand_w)) a).(bf) ++ [mkWalker x false true]) (set_hand_w (pred a.(hand_w)) a)
               end)
              (match x with
               | 0 => set_gy_w (S (set_hand_w (pred a'.(hand_w)) a').(gy_w)) (set_hand_w (pred a'.(hand_w)) a')
               | _ => set_bf ((set_hand_w (pred a'.(hand_w)) a').(bf) ++ [mkWalker x false true]) (set_hand_w (pred a'.(hand_w)) a')
               end).
Proof.
  intros [] [] [| x] HA; pose proof (sa_bf _ _ HA) as Hb; unfold set_gy_w, set_hand_w, set_bf; sa_solve HA.
  apply F2_snoc. exact Hb.
Qed.

(** Burying Walkers whose sizes agree. *)
Lemma sa_bury : forall dead a a', sideA_rel H a a' ->
  (forall i, In i dead -> walker_power a i = walker_power a' i) ->
  sideA_rel H (bury dead a) (bury dead a').
Proof.
  intros dead a a' HA Hd. pose proof (sa_bf _ _ HA) as Hb.
  assert (Es : list_sum (map (walker_power a) dead) = list_sum (map (walker_power a') dead))
    by (f_equal; apply map_ext_in; exact Hd).
  unfold bury. rewrite Es. clear Es Hd.
  destruct a, a'. unfold set_gy_w, set_thop_u, set_bf. sa_solve HA. apply F2_remove. exact Hb.
Qed.

Lemma sa_set_life : forall n a a', sideA_rel H a a' -> sideA_rel H (set_life n a) (set_life n a').
Proof. intros n [] [] HA. unfold set_life. sa_solve HA. Qed.

Lemma sa_set_thop_t : forall n a a', sideA_rel H a a' -> sideA_rel H (set_thop_t n a) (set_thop_t n a').
Proof. intros n [] [] HA. unfold set_thop_t. sa_solve HA. Qed.

Lemma sa_set_thop_u : forall n a a', sideA_rel H a a' -> sideA_rel H (set_thop_u n a) (set_thop_u n a').
Proof. intros n [] [] HA. unfold set_thop_u. sa_solve HA. Qed.

Lemma sa_attack : forall ws k a a', sideA_rel H a a' ->
  sideA_rel H
    (set_thop_t (a.(thop_t) + k) (set_thop_u (a.(thop_u) - k)
      (set_bf (fold_right (fun i l => update_nth i tap_walker l) a.(bf) ws) a)))
    (set_thop_t (a'.(thop_t) + k) (set_thop_u (a'.(thop_u) - k)
      (set_bf (fold_right (fun i l => update_nth i tap_walker l) a'.(bf) ws) a'))).
Proof.
  intros ws k [] [] HA. pose proof (sa_bf _ _ HA) as Hb.
  unfold set_thop_t, set_thop_u, set_bf. sa_solve HA. apply F2_taps. exact Hb.
Qed.

(** *** [RA] through the state operations *)

Lemma RA_intro : forall act ft a a' b c pd, no_a_shuffle pd -> sideA_rel H a a' ->
  RA (mkState act ft a b c pd) (mkState act ft a' b c pd).
Proof.
  intros. unfold RA; cbn [Model.active Model.first_turn Model.cmb Model.pend Model.sideA Model.sideB].
  repeat (split; [reflexivity |]). split; [assumption |]. split; [assumption | reflexivity].
Qed.

Ltac ra_cbn := cbn [Model.active Model.first_turn Model.cmb Model.pend Model.sideA Model.sideB] in *.

Lemma RA_getA : forall s u, RA s u -> sideA_rel H (get_side PA s) (get_side PA u).
Proof. intros s u (_ & _ & _ & _ & _ & HA & _). exact HA. Qed.

Lemma RA_getB : forall s u, RA s u -> get_side PB s = get_side PB u.
Proof. intros s u (_ & _ & _ & _ & _ & _ & EB). exact EB. Qed.

Lemma RA_set_pend : forall pd s u, no_a_shuffle pd -> RA s u -> RA (set_pend pd s) (set_pend pd u).
Proof.
  intros pd [act ft a b c pd0] [act' ft' a' b' c' pd'] Hpd (E1 & E2 & E3 & E4 & Hn & HA & EB).
  ra_cbn. subst. unfold set_pend. apply RA_intro; assumption.
Qed.

Lemma RA_set_cmb : forall c s u, RA s u -> RA (set_cmb c s) (set_cmb c u).
Proof.
  intros c0 [act ft a b c pd] [act' ft' a' b' c' pd'] (E1 & E2 & E3 & E4 & Hn & HA & EB).
  ra_cbn. subst. unfold set_cmb. apply RA_intro; assumption.
Qed.

Lemma RA_setA : forall x y s u, sideA_rel H x y -> RA s u -> RA (set_side PA x s) (set_side PA y u).
Proof.
  intros x y [act ft a b c pd] [act' ft' a' b' c' pd'] Hxy (E1 & E2 & E3 & E4 & Hn & HA & EB).
  ra_cbn. subst. unfold set_side. apply RA_intro; assumption.
Qed.

Lemma RA_setB : forall x s u, RA s u -> RA (set_side PB x s) (set_side PB x u).
Proof.
  intros x [act ft a b c pd] [act' ft' a' b' c' pd'] (E1 & E2 & E3 & E4 & Hn & HA & EB).
  ra_cbn. subst. unfold set_side. apply RA_intro; assumption.
Qed.

Lemma RA_mapA : forall f s u, (forall a a', sideA_rel H a a' -> sideA_rel H (f a) (f a')) ->
  RA s u -> RA (map_side PA f s) (map_side PA f u).
Proof.
  intros f s u Hf HR. unfold map_side. apply RA_setA; [apply Hf, RA_getA |]; exact HR.
Qed.

Lemma RA_mapB : forall f s u, RA s u -> RA (map_side PB f s) (map_side PB f u).
Proof. intros f s u HR. unfold map_side. rewrite (RA_getB _ _ HR). apply RA_setB. exact HR. Qed.

Lemma RA_rebuild : forall act ft c pd s u, no_a_shuffle pd -> RA s u ->
  RA (mkState act ft s.(sideA) s.(sideB) c pd) (mkState act ft u.(sideA) u.(sideB) c pd).
Proof.
  intros act0 ft0 c0 pd0 [act ft a b c pd] [act' ft' a' b' c' pd'] Hpd (E1 & E2 & E3 & E4 & Hn & HA & EB).
  ra_cbn. subst. cbn. apply RA_intro; assumption.
Qed.

Lemma RA_with_payment : forall n p k s u, (forall s u, RA s u -> RA (k s) (k u)) ->
  RA s u -> RA (with_payment n p s k) (with_payment n p u k).
Proof.
  intros n [] k s u Hk HR; unfold with_payment.
  - pose proof (sa_pay n _ _ (RA_getA _ _ HR)) as Hp.
    destruct (pay n (get_side PA s)), (pay n (get_side PA u)); try contradiction;
      [apply Hk, RA_setA; assumption | exact HR].
  - rewrite (RA_getB _ _ HR). destruct (pay n (get_side PB u)); [apply Hk, RA_setB |]; exact HR.
Qed.

Lemma RA_end_step : forall st s u, RA s u -> RA (end_step st s) (end_step st u).
Proof.
  intros st s u HR. unfold end_step. cbv zeta.
  assert (HR' : RA (empty_pools s) (empty_pools u)).
  { unfold empty_pools. apply RA_mapA; [intros; apply sa_set_pool; assumption |].
    apply RA_mapB. exact HR. }
  generalize (empty_pools s) (empty_pools u) HR'. clear s u HR HR'. intros s u HR.
  pose proof HR as (E1 & E2 & E3 & _).
  rewrite <- E1, <- E2, <- E3.
  destruct st; try (apply RA_set_pend; [exact I | exact HR]).
  - destruct (first_turn s); (apply RA_set_pend; [exact I |]); [exact HR |].
    destruct (active s); [apply RA_mapA; [exact sa_draw | exact HR] | apply RA_mapB; exact HR].
  - destruct (atk (cmb s)), (atk_thop (cmb s)); apply RA_set_pend; try exact I; exact HR.
  - apply RA_set_pend; [exact I |]. apply RA_set_cmb. exact HR.
  - unfold next_turn. cbv zeta. rewrite <- E1. apply RA_rebuild; [exact I |].
    destruct (opp (active s)); [apply RA_mapA; [exact sa_untap | exact HR] | apply RA_mapB; exact HR].
Qed.

Lemma RA_block : forall wb tb tr s u, RA s u -> RA (do_block wb tb tr s) (do_block wb tb tr u).
Proof.
  intros wb tb tr [act ft a b c pd] [act' ft' a' b' c' pd'] (E1 & E2 & E3 & E4 & Hn & HA & EB).
  ra_cbn. subst. unfold do_block, set_cmb, set_pend. cbn.
  match goal with |- context [if ?x then _ else _] => destruct x end;
    apply RA_intro; try exact I; assumption.
Qed.

Lemma RA_order : forall os s u, RA s u -> RA (do_order os s) (do_order os u).
Proof.
  intros os [act ft a b c pd] [act' ft' a' b' c' pd'] (E1 & E2 & E3 & E4 & Hn & HA & EB).
  ra_cbn. subst. unfold do_order, set_cmb, set_pend. cbn. apply RA_intro; [exact I | assumption].
Qed.

(** *** A's moves that A cannot make *)

Ltac in_split :=
  repeat match goal with
  | Hin : In _ (_ :: _) |- _ => destruct Hin as [Hin | Hin]; [try discriminate |]
  | Hin : In _ (_ ++ _) |- _ => apply in_app_iff in Hin as [Hin | Hin]
  | Hin : In _ (map _ _) |- _ => let x := fresh in apply in_map_iff in Hin as [x [Hin _]]; try discriminate
  | Hin : In _ [] |- _ => destruct Hin
  | Hin : In _ (if ?b then _ else _) |- _ => destruct b
  end.

Lemma window_elixir : forall st p s, In ActElixir (window_moves st p s) -> (get_side p s).(elixir_bf) = true.
Proof.
  intros st p s Hin. destruct (elixir_bf (get_side p s)) eqn:E; [reflexivity | exfalso].
  unfold window_moves in Hin. rewrite E in Hin. cbn [andb] in Hin. in_split.
Qed.

Lemma window_cast_elixir : forall st p s, In CastElixir (window_moves st p s) -> (get_side p s).(hand_e) = true.
Proof.
  intros st p s Hin. destruct (hand_e (get_side p s)) eqn:E; [reflexivity | exfalso].
  unfold window_moves in Hin. rewrite E in Hin. cbn [andb] in Hin. in_split.
Qed.

(** *** Combat damage *)

Definition fights_of (c : combat) (js : list nat) := combine (combine c.(atk) c.(blk)) js.

Definition unblocked_of (a : side) (c : combat) (fs : list (nat * list blocker * nat)) : nat :=
  list_sum (map (fun '(i, bs, _) => match bs with [] => walker_power a i | _ => 0 end) fs)
  + (c.(atk_thop) - c.(trades)).

Definition adead_of (a d : side) (fs : list (nat * list blocker * nat)) : list nat :=
  map (fun '(i, _, _) => i)
    (filter (fun '(i, bs, _) =>
               match bs with
               | [] => false
               | _ => walker_power a i <=? list_sum (map (blocker_toughness d) bs)
               end) fs).

Definition killed_of (fs : list (nat * list blocker * nat)) : list blocker :=
  flat_map (fun '(_, bs, j) => firstn j bs) fs.

Definition damage_alt (js : list nat) (s : state) : state :=
  let ap := s.(active) in
  let dp := defender s in
  let a := get_side ap s in
  let d := get_side dp s in
  let c := s.(cmb) in
  let fs := fights_of c js in
  let unblocked := unblocked_of a c fs in
  let killed := killed_of fs in
  let d_dead := flat_map (fun b => match b with BW i => [i] | BT => [] end) killed in
  let d_thop_dead := count_occ blocker_eq_dec killed BT + c.(trades) in
  let a := bury (adead_of a d fs) (set_thop_t (a.(thop_t) - c.(trades)) a) in
  let d := bury d_dead (set_thop_u (d.(thop_u) - d_thop_dead) d) in
  let s := set_cmb no_combat (set_side dp d (set_side ap a s)) in
  if d.(life) <=? unblocked then set_pend (Over ap) s
  else set_pend (Window DamageStep ap false)
         (map_side dp (fun d => set_life (d.(life) - unblocked) d) s).

Lemma damage_alt_eq : forall js s, do_damage js s = damage_alt js s.
Proof. reflexivity. Qed.

Lemma nonhuge_eq : forall a a' i, Forall2 walker_rel a.(bf) a'.(bf) -> walker_power a i < H ->
  walker_power a i = walker_power a' i.
Proof. intros a a' i Hb Hl. destruct (walker_power_rel a a' i Hb) as [E | (Hp & _)]; [exact E | lia]. Qed.

Lemma huge_A_false : forall a d l,
  existsb (fun '(i, bs) => is_huge H a i &&
             match bs with [] => true | _ => H <=? list_sum (map (blocker_toughness d) bs) end) l = false ->
  forall i bs, In (i, bs) l -> H <= walker_power a i ->
  bs <> [] /\ list_sum (map (blocker_toughness d) bs) < H.
Proof.
  intros a d l Hx i bs Hin Hge.
  destruct (is_huge H a i && match bs with [] => true | _ => H <=? list_sum (map (blocker_toughness d) bs) end) eqn:Ev.
  - exfalso. assert (Ht : existsb (fun '(i, bs) => is_huge H a i &&
             match bs with [] => true | _ => H <=? list_sum (map (blocker_toughness d) bs) end) l = true).
    { apply existsb_exists. exists (i, bs). split; assumption. }
    congruence.
  - unfold is_huge in Ev. rewrite (proj2 (Nat.leb_le _ _) Hge) in Ev. cbn [andb] in Ev.
    destruct bs; [discriminate | split; [discriminate | apply Nat.leb_gt; exact Ev]].
Qed.

Lemma huge_B_false : forall a d l,
  existsb (fun '(i, bs) => (H <=? walker_power a i) &&
             existsb (fun b => match b with BW j => is_huge H d j | BT => false end) bs) l = false ->
  forall i bs j, In (i, bs) l -> In (BW j) bs -> H <= walker_power d j -> walker_power a i < H.
Proof.
  intros a d l Hx i bs j Hin Hj Hge.
  destruct (Nat.leb_spec H (walker_power a i)) as [Hle | Hlt]; [exfalso | exact Hlt].
  assert (Ht : existsb (fun '(i, bs) => (H <=? walker_power a i) &&
             existsb (fun b => match b with BW j => is_huge H d j | BT => false end) bs) l = true).
  { apply existsb_exists. exists (i, bs). split; [exact Hin |].
    apply andb_true_intro. split; [apply Nat.leb_le; exact Hle |].
    apply existsb_exists. exists (BW j). split; [exact Hj | apply Nat.leb_le; exact Hge]. }
  congruence.
Qed.

Lemma in_le_sum : forall x l, In x l -> x <= list_sum l.
Proof.
  intros x l. induction l as [| y l IH]; intros Hin; [destruct Hin |].
  unfold list_sum in *; cbn [fold_right]. destruct Hin as [<- | Hin]; [lia | specialize (IH Hin); lia].
Qed.

Lemma in_firstn : forall {X} n (x : X) l, In x (firstn n l) -> In x l.
Proof.
  intros X n x l Hin. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact Hin.
Qed.

Lemma max_prefix_bound : forall ts p j, j <= max_prefix p ts -> list_sum (firstn j ts) <= p.
Proof.
  induction ts as [| t ts IH]; intros p [| j] Hj; cbn [firstn]; unfold list_sum in *; cbn [fold_right]; try lia.
  cbn [max_prefix] in Hj. destruct (Nat.leb_spec t p); [| lia].
  specialize (IH (p - t) j ltac:(lia)). unfold list_sum in IH. lia.
Qed.

Lemma kill_bound : forall p ts j, In j (kill_choices p ts) -> list_sum (firstn j ts) <= p.
Proof.
  intros p [| t ts] j Hin; unfold kill_choices in Hin.
  - destruct Hin as [<- | []]. cbn. lia.
  - destruct (Nat.ltb_spec p t).
    + destruct Hin as [<- | []]. cbn. lia.
    + apply in_seq in Hin. apply max_prefix_bound. lia.
Qed.

Lemma in_product : forall {X} (cs : list (list X)) xs, In xs (product cs) -> Forall2 (@In X) xs cs.
Proof.
  intros X cs. induction cs as [| c cs IH]; intros xs Hin; cbn [product] in Hin.
  - destruct Hin as [<- | []]. constructor.
  - apply in_flat_map in Hin as [x [Hx Hin]]. apply in_map_iff in Hin as [r [<- Hr]].
    constructor; [exact Hx | apply IH; exact Hr].
Qed.

Lemma in_fight : forall (F : nat -> list blocker -> list nat) (g : nat -> nat) atk blk js i bs j,
  Forall2 (@In nat) js (map (fun '(p, bs) => F p bs) (combine (map g atk) blk)) ->
  In (i, bs, j) (combine (combine atk blk) js) -> In j (F (g i) bs).
Proof.
  intros F g atk. induction atk as [| x atk IH]; intros [| y blk] [| k js] i bs j Hf Hin;
    cbn [combine map] in *; try destruct Hin; inversion Hf as [| ? ? ? ? Hk Hr]; subst.
  - injection H0 as <- <- <-. exact Hk.
  - eapply IH; eassumption.
Qed.

Lemma RA_damage : forall s u js, RA s u -> s.(pend) = ChooseDamage -> huge_event s = false ->
  In (Assign js) (damage_moves s) -> RA (do_damage js s) (do_damage js u).
Proof.
  intros [act ft a b c pd] [act' ft' a' b' c' pd'] js (E1 & E2 & E3 & E4 & Hn & HA & EB) Ep Hh Hin.
  ra_cbn. subst act' ft' c' pd' b' pd.
  change (RA (damage_alt js (mkState act ft a b c ChooseDamage)) (damage_alt js (mkState act ft a' b c ChooseDamage))).
  pose proof (sa_bf _ _ HA) as Hbf.
  unfold damage_moves in Hin. apply in_map_iff in Hin as [js' [Ej Hin]]. injection Ej as ->.
  apply in_product in Hin.
  unfold Checker.huge_event in Hh.
  destruct act; unfold damage_alt, defender in *;
    cbn [get_side opp Model.active Model.sideA Model.sideB Model.cmb Model.pend] in *.
  - (* A attacks: B's side is the same, A's attackers may be huge *)
    assert (Eu : unblocked_of a c (fights_of c js) = unblocked_of a' c (fights_of c js)).
    { unfold unblocked_of. f_equal. f_equal. apply map_ext_in. intros [[i bs] j] Hf.
      destruct bs; [| reflexivity]. apply nonhuge_eq; [exact Hbf |].
      destruct (Nat.lt_ge_cases (walker_power a i) H) as [Hl | Hg]; [exact Hl | exfalso].
      unfold fights_of in Hf. apply in_combine_l in Hf.
      destruct (huge_A_false _ _ _ Hh i [] Hf Hg) as [N _]. congruence. }
    assert (Hd : forall i, In i (adead_of a b (fights_of c js)) -> walker_power a i = walker_power a' i).
    { intros i Hi. unfold adead_of in Hi. apply in_map_iff in Hi as [[[i' bs] j] [<- Hi]].
      apply filter_In in Hi as [Hf Hk]. destruct bs as [| x bs]; [discriminate |].
      apply nonhuge_eq; [exact Hbf |].
      destruct (Nat.lt_ge_cases (walker_power a i') H) as [Hl | Hg]; [exact Hl | exfalso].
      unfold fights_of in Hf. apply in_combine_l in Hf.
      destruct (huge_A_false _ _ _ Hh i' _ Hf Hg) as [_ Hs].
      apply Nat.leb_le in Hk.  lia. }
    assert (Ed : adead_of a' b (fights_of c js) = adead_of a b (fights_of c js)).
    { unfold adead_of. f_equal. apply filter_ext_in. intros [[i bs] j] Hf.
      destruct bs as [| x bs]; [reflexivity |].
      destruct (Nat.lt_ge_cases (walker_power a i) H) as [Hl | Hg];
        [rewrite (nonhuge_eq a a' i Hbf Hl); reflexivity |].
      unfold fights_of in Hf. apply in_combine_l in Hf.
      destruct (huge_A_false _ _ _ Hh i _ Hf Hg) as [_ Hs].
      destruct (walker_power_rel a a' i Hbf) as [E | (_ & Hg')]; [rewrite E; reflexivity |].
      destruct (Nat.leb_spec (walker_power a i) (list_sum (map (blocker_toughness b) (x :: bs))));
        destruct (Nat.leb_spec (walker_power a' i) (list_sum (map (blocker_toughness b) (x :: bs)))); lia. }
    rewrite <- Eu, Ed.
    destruct (_ <=? _); apply RA_set_pend; try exact I; try apply RA_mapB;
      apply RA_set_cmb; apply RA_setB; (apply RA_setA; [| apply RA_intro; [exact I | exact HA]]);
      (apply sa_bury; [pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Et);
                       rewrite Et; apply sa_set_thop_t; exact HA | exact Hd]).
  - (* B attacks: A's blockers may be huge *)
    assert (Ed : adead_of b a' (fights_of c js) = adead_of b a (fights_of c js)).
    { unfold adead_of. f_equal. apply filter_ext_in. intros [[i bs] j] Hf.
      destruct bs as [| x bs]; [reflexivity |].
      unfold fights_of in Hf. apply in_combine_l in Hf.
      destruct (existsb (fun b0 => match b0 with BW j => is_huge H a j | BT => false end) (x :: bs)) eqn:Ex.
      - apply existsb_exists in Ex as [[j0 |] [Hj0 Hx]]; [| discriminate].
        unfold is_huge in Hx. apply Nat.leb_le in Hx.
        pose proof (huge_B_false _ _ _ Hh i _ j0 Hf Hj0 Hx) as Hl.
        assert (Hs : forall d, H <= walker_power d j0 -> walker_power b i <=? list_sum (map (blocker_toughness d) (x :: bs)) = true).
        { intros d Hd. apply Nat.leb_le.
          pose proof (in_le_sum (blocker_toughness d (BW j0)) (map (blocker_toughness d) (x :: bs)) (in_map _ _ _ Hj0)) as Hle.
          cbn [blocker_toughness] in Hle. lia. }
        rewrite !Hs; [reflexivity | exact Hx |].
        destruct (walker_power_rel a a' j0 Hbf) as [E | (_ & Hg')]; [rewrite <- E; exact Hx | exact Hg'].
      - f_equal. f_equal. apply map_ext_in. intros [j0 |] Hj0; [| reflexivity].
        cbn [blocker_toughness]. symmetry. apply nonhuge_eq; [exact Hbf |].
        destruct (Nat.lt_ge_cases (walker_power a j0) H) as [Hl | Hg]; [exact Hl | exfalso].
        assert (Ht : existsb (fun b0 => match b0 with BW j => is_huge H a j | BT => false end) (x :: bs) = true).
        { apply existsb_exists. exists (BW j0). split; [exact Hj0 | apply Nat.leb_le; exact Hg]. }
        congruence. }
    assert (Hd : forall i, In i (flat_map (fun b => match b with BW i => [i] | BT => [] end) (killed_of (fights_of c js))) ->
                 walker_power a i = walker_power a' i).
    { intros i Hi. apply in_flat_map in Hi as [[i' |] [Hk Hi]]; [| destruct Hi].
      destruct Hi as [<- | []].
      unfold killed_of in Hk. apply in_flat_map in Hk as [[[i0 bs] j] [Hf Hk]].
      apply nonhuge_eq; [exact Hbf |].
      destruct (Nat.lt_ge_cases (walker_power a i') H) as [Hl | Hg]; [exact Hl | exfalso].
      pose proof (in_fight (fun p bs => kill_choices p (map (blocker_toughness a) bs)) (walker_power b) _ _ _ _ _ _
                    Hin ltac:(unfold fights_of in Hf; exact Hf)) as Hj.
      cbv beta in Hj. apply kill_bound in Hj. rewrite firstn_map in Hj.
      pose proof (in_le_sum _ _ (in_map (blocker_toughness a) _ _ Hk)) as Hle.
      cbn [blocker_toughness] in Hle.
      unfold fights_of in Hf. apply in_combine_l in Hf.
      pose proof (huge_B_false _ _ _ Hh i0 bs i' Hf (in_firstn _ _ _ Hk) Hg). lia. }
    rewrite Ed.
    assert (El : forall l n sd, life (bury l (set_thop_u n sd)) = life sd) by reflexivity.
    rewrite !El.
    pose proof HA as (Hl & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hu & _). rewrite <- Hl.
    destruct (_ <=? _); apply RA_set_pend; try exact I;
      try (apply RA_mapA; [intros x x' Hx; pose proof Hx as (Ex & _); rewrite Ex; apply sa_set_life; exact Hx |]);
      apply RA_set_cmb; (apply RA_setA; [| apply RA_setB; apply RA_intro; [exact I | exact HA]]);
      (apply sa_bury; [rewrite Hu; apply sa_set_thop_u; exact HA | exact Hd]).
Qed.

(** *** One step *)

Lemma RA_step : forall s u m, RA s u -> In m (moves s) -> huge_event s = false ->
  RA (step s m) (step u m).
Proof.
  intros s u m HR Hin Hh. revert Hin.
  pose proof HR as (E1 & E2 & E3 & E4 & Hns & HA & EB).
  unfold step, moves. rewrite <- E4.
  destruct (pend s) as [st p passed | | | | | st p cards | w] eqn:Ep, m; intros Hin; try exact HR.
  - destruct passed; [apply RA_end_step; exact HR | apply RA_set_pend; [exact I | exact HR]].
  - (* Pump *)
    unfold do_pump. apply RA_with_payment; [| exact HR]. intros s' u' HR'.
    apply RA_set_pend; [exact I |].
    destruct p; [apply RA_mapA; [| exact HR'] | apply RA_mapB; exact HR'].
    intros x x' Hx. apply sa_set_bf; [exact Hx |].
    apply F2_update; [apply sa_bf; exact Hx | apply walker_rel_pump].
  - (* ActElixir *)
    destruct p.
    + exfalso. apply window_elixir in Hin. cbn [get_side] in Hin.
      pose proof HA as (_ & _ & _ & _ & _ & _ & Hx & _). congruence.
    + unfold do_elixir. apply RA_with_payment; [| exact HR]. intros s' u' HR'. cbv beta zeta.
      rewrite (RA_getB _ _ HR'). apply RA_set_pend; [exact I |]. apply RA_setB. exact HR'.
  - (* CastWalker *)
    unfold do_cast_walker. apply RA_with_payment; [| exact HR]. intros s' u' HR'. cbv beta zeta.
    apply RA_set_pend; [exact I |]. destruct p.
    + apply RA_setA; [apply sa_cast_walker, RA_getA, HR' | exact HR'].
    + rewrite (RA_getB _ _ HR'). apply RA_setB. exact HR'.
  - (* CastElixir *)
    destruct p.
    + exfalso. apply window_cast_elixir in Hin. cbn [get_side] in Hin.
      pose proof HA as (_ & _ & _ & _ & He & _). congruence.
    + unfold do_cast_elixir. apply RA_with_payment; [| exact HR]. intros s' u' HR'.
      apply RA_set_pend; [exact I |]. apply RA_mapB. exact HR'.
  - (* Attack *)
    unfold do_attack. cbv zeta. rewrite <- E1. apply RA_set_pend; [exact I |]. apply RA_set_cmb.
    destruct (active s); [apply RA_mapA; [intros x x' Hx; apply sa_attack; exact Hx | exact HR] |
                          apply RA_mapB; exact HR].
  - apply RA_block. exact HR.
  - apply RA_order. exact HR.
  - apply RA_damage; assumption.
  - destruct p; [exfalso; try rewrite Ep in Hns; exact Hns |].
    apply RA_set_pend; [exact I |]. apply RA_mapB. exact HR.
Qed.

(** ** [R] as [RA], then more B Thopters, then more B life *)

Lemma R_split : forall s t, R s t ->
  exists u v k, RA s u /\ thop_le PB u v /\ t = bump PB k v.
Proof.
  intros [act ft a b c pd] [act' ft' a' b' c' pd'] (E1 & E2 & E3 & E4 & Hn & HA & HB).
  cbn [Model.active Model.first_turn Model.cmb Model.pend Model.sideA Model.sideB] in *. subst.
  destruct HB as (Hl & Hu & Ht & Hs).
  exists (mkState act' ft' a' b c' pd'), (more_thop PB b'.(thop_u) b'.(thop_t) (mkState act' ft' a' b c' pd')),
         (b'.(life) - b.(life)).
  split; [apply RA_intro; assumption |]. split.
  - exists b'.(thop_u), b'.(thop_t). cbn. auto.
  - apply strip_b_fields in Hs. destruct Hs as (Ec & Ep & Ew & Ee & Ebf & Ex & Elib & Eg).
    destruct b, b'; cbn in *. unfold bump, more_thop, map_side, get_side, set_side, bump_side,
      set_life, set_thop_t, set_thop_u. cbn. subst. repeat f_equal. lia.
Qed.

Lemma R_join : forall x y z k, RA x y -> thop_le PB y z -> R x (bump PB k z).
Proof.
  intros [act ft a b c pd] [act' ft' a' b' c' pd'] z k (E1 & E2 & E3 & E4 & Hn & HA & EB) [tu [tv [Hu [Hv ->]]]].
  ra_cbn. subst act' ft' c' pd' b'.
  unfold R; cbn. repeat (split; [reflexivity |]). split; [exact Hn |]. split; [exact HA |].
  destruct b. cbn in *. unfold sideB_rel, strip_b, set_life, set_thop_t, set_thop_u; cbn.
  repeat split; lia.
Qed.

(** [Checker.cert_safe]'s third hypothesis. *)
Theorem sim_step : forall s t m,
  R s t -> In m (moves s) -> huge_event s = false -> winner (step s m) <> Some PA ->
  R (step s m) (step t m).
Proof.
  intros s t m HR Hin Hh Hw.
  destruct (R_split s t HR) as [u [v [k [Hsu [Huv ->]]]]].
  pose proof (RA_step s u m Hsu Hin Hh) as Hsu'.
  pose proof (step_thop PB u v m Huv) as Huv'.
  rewrite step_bump.
  - eapply R_join; eassumption.
  - cbn [opp]. rewrite (winner_thop PB _ _ Huv').
    pose proof Hsu' as (_ & _ & _ & E4 & _). unfold winner. rewrite <- E4. exact Hw.
Qed.

End Saturation.

(** ** The checker's guarantee, with no hypotheses left but the check itself *)

Theorem certified_safe : forall H ott tt lookup hint,
  (forall s v, lookup s = Some v -> exists fuel, check_node H ott tt lookup hint fuel true (entry s v) = true) ->
  forall s v t, lookup s = Some v -> R H (entry s v) t -> safe PB t.
Proof.
  intros H ott tt lookup hint Hok.
  apply (cert_safe H ott tt lookup hint Hok (sim_mine H) (sim_theirs H) (sim_step H)).
Qed.

Lemma R_init : forall H p, R H (init p) (init p).
Proof.
  intros H []; unfold R, init, sideA_rel, sideB_rel; cbn;
    repeat split; auto; constructor.
Qed.

(** If every certificate entry checks and the opening's entry asks for at
    most B's starting 20 life, B is safe (does not lose) from the opening. *)
Theorem certified_opening : forall H ott tt lookup hint p v,
  (forall s v, lookup s = Some v -> exists fuel, check_node H ott tt lookup hint fuel true (entry s v) = true) ->
  lookup (key H tt (init p)) = Some v -> v <= 20 -> safe PB (init p).
Proof.
  intros H ott tt lookup hint p v Hok Hl Hv.
  apply (certified_safe H ott tt lookup hint Hok _ v _ Hl).
  apply (R_key H tt (init p) (init p) v (R_init H p)).
  destruct p; exact Hv.
Qed.
