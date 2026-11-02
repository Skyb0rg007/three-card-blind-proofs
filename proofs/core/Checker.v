(** * Checking B-safety certificates (REDUCTION.md R3, R4)

    The solver's B-safe tables become a proof through this checker. A
    certificate is a partial map [lookup] from normalised turn starts to the
    least life B needs there. [check_node] re-searches one turn of the real
    model from an entry. B may play any legal move the untrusted [hint]
    allows; A may play every legal move. At the next turn start the search
    looks the position up again. If every entry checks, B is safe from every
    real state that an entry abstracts.

    The certificate abstracts real states in four ways, the same ones the
    solver uses:
    - **B's life** is a threshold: more life only helps B (R2, [safe_bump]).
    - **B's Thopters** are cut to [tt]: more Thopters only help B (R3,
      [safe_thop]).
    - **A's graveyard** is dropped: A has no Elixir, so nothing reads it.
    - **A's Walkers** are saturated at [H] counters (R4). A Walker with at
      least [H] counters stands for every size from [H] up. Combat where the
      exact size of such a Walker would matter is a loss for B
      ([huge_event]), and so is A having more than [ott] Thopters
      ([too_many]).

    [R s t] says that the certificate-side state [s] abstracts the real
    state [t]. The soundness theorem [cert_safe] needs three facts about [R]
    and the model: B's moves at [s] are legal at [t] ([sim_mine]); A's moves
    at [t] are moves at [s] when no huge event is pending ([sim_theirs]);
    and steps preserve [R] when B is not lost ([sim_step]). They are
    hypotheses of this section, discharged in a separate file. *)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.
From TCB.Spec Require Import Model Game.

(** Turn starts: an upkeep window where the active player has priority and
    nobody has passed. (The solvers also stop where the other player has
    just acted in that window; the checker searches on from there.) *)
Definition is_turn_start (s : state) : bool :=
  match s.(pend) with Window Upkeep p false => player_eqb p s.(active) | _ => false end.

(** Short-circuiting [existsb] and [forallb]. Under [vm_compute], which
    evaluates arguments first, [existsb] would search every remaining move
    after the first that works. *)
Fixpoint some_move (f : move -> bool) (l : list move) : bool :=
  match l with [] => false | m :: r => if f m then true else some_move f r end.

Fixpoint all_moves (f : move -> bool) (l : list move) : bool :=
  match l with [] => true | m :: r => if f m then all_moves f r else false end.

Lemma some_move_existsb : forall f l, some_move f l = existsb f l.
Proof. intros f l. induction l as [| m r IH]; cbn; [reflexivity |]. destruct (f m); auto. Qed.

Lemma all_moves_forallb : forall f l, all_moves f l = forallb f l.
Proof. intros f l. induction l as [| m r IH]; cbn; [reflexivity |]. destruct (f m); auto. Qed.

Section Checker.

(** A's Walkers with at least [H] counters are huge; more than [ott] A
    Thopters is a loss for B; B's Thopters are cut to [tt] in keys. *)
Variables H ott tt : nat.

(** ** Normalised keys *)

Definition clamp_walker (w : walker) : walker :=
  mkWalker (Nat.min w.(counters) H) w.(wtapped) w.(sick).

(** Keep at most [tt] Thopters, dropping tapped ones first (as the solver). *)
Definition cut_thop (sd : side) : side :=
  let extra := sd.(thop_u) + sd.(thop_t) - tt in
  let dt := Nat.min extra sd.(thop_t) in
  set_thop_u (sd.(thop_u) - (extra - dt)) (set_thop_t (sd.(thop_t) - dt) sd).

Definition key (s : state) : state :=
  mkState s.(active) s.(first_turn)
    (set_gy_w 0 (set_bf (map clamp_walker s.(sideA).(bf)) s.(sideA)))
    (set_life 0 (cut_thop s.(sideB))) s.(cmb) s.(pend).

(** The position an entry of the certificate stands for. *)
Definition entry (s : state) (v : nat) : state := map_side PB (set_life v) s.

(** ** Events the abstraction can't follow *)

Definition is_huge (sd : side) (i : nat) : bool := H <=? walker_power sd i.

(** Combat damage where a huge Walker's exact size matters: a huge A
    attacker unblocked, or blocked by enough toughness to kill it; or a
    huge A blocker meeting a B attacker big enough to kill it. *)
Definition huge_event (s : state) : bool :=
  match s.(pend) with
  | ChooseDamage =>
      let a := get_side s.(active) s in
      let d := get_side (defender s) s in
      let fights := combine s.(cmb).(atk) s.(cmb).(blk) in
      match s.(active) with
      | PA =>
          existsb (fun '(i, bs) =>
            is_huge a i &&
            match bs with
            | [] => true
            | _ => H <=? list_sum (map (blocker_toughness d) bs)
            end) fights
      | PB =>
          existsb (fun '(i, bs) =>
            (H <=? walker_power a i) &&
            existsb (fun b => match b with BW j => is_huge d j | BT => false end) bs) fights
      end
  | _ => false
  end.

Definition too_many (s : state) : bool :=
  ott <? s.(sideA).(thop_u) + s.(sideA).(thop_t).

(** ** The checker *)

Variable lookup : state -> option nat.
Variable hint : state -> move -> bool.

(** Does B stay safe through the rest of this turn from [s]? At the next
    turn start the certificate is consulted ([root] is false below the
    entry being checked). *)
Fixpoint check_node (fuel : nat) (root : bool) (s : state) : bool :=
  match fuel with
  | 0 => false
  | S f =>
      match winner s with
      | Some PB => true
      | Some PA => false
      | None =>
          if negb root && is_turn_start s then
            match lookup (key s) with
            | Some v => v <=? s.(sideB).(life)
            | None => false
            end
          else if huge_event s then false
          else
            let next m := let s' := step s m in if too_many s' then false else check_node f false s' in
            match to_move s with
            | PB => some_move (fun m => if hint s m then next m else false) (moves s)
            | PA => all_moves next (moves s)
            end
      end
  end.

(** ** The abstraction relation *)

Definition walker_rel (w w' : walker) : Prop :=
  w.(wtapped) = w'.(wtapped) /\ w.(sick) = w'.(sick) /\
  (w.(counters) = w'.(counters) \/ (H <= w.(counters) /\ H <= w'.(counters))).

(** A's side: equal except for saturated Walkers and the graveyard. A has
    no Elixir anywhere. *)
Definition sideA_rel (a a' : side) : Prop :=
  a.(life) = a'.(life) /\ a.(city) = a'.(city) /\ a.(pool) = a'.(pool) /\
  a.(hand_w) = a'.(hand_w) /\
  a.(hand_e) = false /\ a'.(hand_e) = false /\
  a.(elixir_bf) = false /\ a'.(elixir_bf) = false /\
  Forall (eq CWalker) a.(library) /\ a.(library) = a'.(library) /\
  Forall2 walker_rel a.(bf) a'.(bf) /\
  a.(thop_u) = a'.(thop_u) /\ a.(thop_t) = a'.(thop_t).

Definition strip_b (b : side) : side := set_life 0 (set_thop_u 0 (set_thop_t 0 b)).

(** B's side: no more life and Thopters than the real one, else equal. *)
Definition sideB_rel (b b' : side) : Prop :=
  b.(life) <= b'.(life) /\ b.(thop_u) <= b'.(thop_u) /\ b.(thop_t) <= b'.(thop_t) /\
  strip_b b = strip_b b'.

(** A never shuffles: it has no Elixir. *)
Definition no_a_shuffle (pd : pending) : Prop :=
  match pd with ChooseShuffle _ PA _ => False | _ => True end.

Definition R (s t : state) : Prop :=
  s.(active) = t.(active) /\ s.(first_turn) = t.(first_turn) /\
  s.(cmb) = t.(cmb) /\ s.(pend) = t.(pend) /\ no_a_shuffle s.(pend) /\
  sideA_rel s.(sideA) t.(sideA) /\ sideB_rel s.(sideB) t.(sideB).

(** ** Facts about [R] *)

Lemma walker_rel_trans : forall u v w, walker_rel u v -> walker_rel v w -> walker_rel u w.
Proof.
  intros u v w (H1 & H2 & H3) (H4 & H5 & H6). repeat split; try congruence.
  destruct H3, H6; lia.
Qed.

Lemma Forall2_walker_trans : forall l1 l2 l3,
  Forall2 walker_rel l1 l2 -> Forall2 walker_rel l2 l3 -> Forall2 walker_rel l1 l3.
Proof.
  intros l1 l2 l3 H12. revert l3.
  induction H12 as [| x y l1 l2 Hxy H12 IH]; intros l3 H23; inversion H23; subst; constructor.
  - eapply walker_rel_trans; eassumption.
  - apply IH. assumption.
Qed.

Lemma R_trans : forall s u t, R s u -> R u t -> R s t.
Proof.
  unfold R, sideA_rel, sideB_rel.
  intros s u t (E1 & E2 & E3 & E4 & N1 & A1 & B1) (F1 & F2 & F3 & F4 & N2 & A2 & B2).
  destruct A1 as (a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & a9 & a10 & a11 & a12 & a13).
  destruct A2 as (c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13).
  destruct B1 as (b1 & b2 & b3 & b4). destruct B2 as (d1 & d2 & d3 & d4).
  repeat split; try congruence; try lia.
  eapply Forall2_walker_trans; eassumption.
Qed.

Lemma R_winner : forall s t, R s t -> winner t = winner s.
Proof. intros s t (_ & _ & _ & E & _). unfold winner. rewrite E. reflexivity. Qed.

Lemma R_to_move : forall s t, R s t -> to_move t = to_move s.
Proof. intros s t (E1 & _ & _ & E4 & _). unfold to_move. rewrite E1, E4. reflexivity. Qed.

Lemma R_turn_start : forall s t, R s t -> is_turn_start t = is_turn_start s.
Proof. intros s t (Ea & _ & _ & E & _). unfold is_turn_start. rewrite E, Ea. reflexivity. Qed.

Lemma R_too_many : forall s t, R s t -> too_many t = too_many s.
Proof.
  intros s t (_ & _ & _ & _ & _ & A & _). unfold too_many, sideA_rel in *.
  destruct A as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eu & Et). rewrite Eu, Et. reflexivity.
Qed.

Lemma clamp_walker_rel : forall w, walker_rel (clamp_walker w) w.
Proof.
  intros [c tp sk]. unfold walker_rel, clamp_walker. cbn. repeat split.
  destruct (Nat.le_gt_cases H c); [right; lia | left; lia].
Qed.

Lemma clamp_bf_rel : forall l, Forall2 walker_rel (map clamp_walker l) l.
Proof. induction l; constructor; [apply clamp_walker_rel | assumption]. Qed.

(** An entry abstracts the state it was looked up from, when that state has
    at least the life the entry asks for. *)
Lemma R_key : forall s t v, R s t -> v <= s.(sideB).(life) -> R (entry (key s) v) s.
Proof.
  intros [act ft a b c pd] t v Hx Hv.
  destruct Hx as (_ & _ & _ & _ & Hn & A & _). cbn in A, Hv, Hn.
  destruct A as (_ & _ & _ & _ & Hea & _ & Hxa & _ & Hlib & _ & _ & _ & _).
  destruct a as [la ca pa hwa hea bfa ea tua tta liba gya]; cbn in *.
  destruct b as [lb cb pb hwb heb bfb eb tub ttb libb gyb]; cbn in *.
  unfold R, entry, key, sideA_rel, sideB_rel, strip_b, cut_thop; cbn.
  repeat split; auto; try lia.
  apply clamp_bf_rel.
Qed.

(** ** Soundness *)


(** Every entry checks. *)
Hypothesis cert_ok : forall s v, lookup s = Some v -> exists fuel, check_node fuel true (entry s v) = true.

(** The simulation facts (discharged in a separate file). *)
Hypothesis sim_mine : forall s t m,
  R s t -> to_move s = PB -> winner s = None -> huge_event s = false ->
  In m (moves s) -> In m (moves t).
Hypothesis sim_theirs : forall s t m,
  R s t -> to_move s = PA -> winner s = None -> huge_event s = false ->
  In m (moves t) -> In m (moves s).
Hypothesis sim_step : forall s t m,
  R s t -> In m (moves s) -> huge_event s = false -> winner (step s m) <> Some PA ->
  R (step s m) (step t m).

Lemma check_winner : forall f r s, check_node f r s = true -> winner s <> Some PA.
Proof.
  intros [| f] r s Hc; [discriminate |]. cbn [check_node] in Hc.
  destruct (winner s) as [[] |]; congruence.
Qed.

(** Below the root, a check either consults the certificate at a turn
    start or is the same as a check rooted there. *)
Lemma check_below : forall f s, check_node f false s = true ->
  (winner s = None /\ is_turn_start s = true /\
   exists v, lookup (key s) = Some v /\ v <= s.(sideB).(life)) \/
  check_node f true s = true.
Proof.
  intros [| f] s Hc; [discriminate |]. cbn [check_node negb andb] in *.
  destruct (winner s) as [[] |] eqn:Ew; auto.
  destruct (is_turn_start s) eqn:Et; auto.
  left. repeat split; auto.
  destruct (lookup (key s)) as [v |]; [| discriminate].
  exists v. split; [reflexivity | apply Nat.leb_le; exact Hc].
Qed.

Definition good (t : state) : Prop :=
  exists s f, R s t /\ check_node f true s = true.

Lemma good_next : forall s t m f,
  R s t -> In m (moves s) -> huge_event s = false ->
  check_node f false (step s m) = true -> good (step t m).
Proof.
  intros s t m f HR Hin Hh Hc.
  assert (HR' : R (step s m) (step t m)).
  { apply sim_step; auto. eapply check_winner. exact Hc. }
  destruct (check_below f (step s m) Hc) as [(_ & _ & v & Hl & Hv) | Hr].
  - destruct (cert_ok _ _ Hl) as [fuel Hf]. exists (entry (key (step s m)) v), fuel. split.
    + eapply R_trans; [| exact HR']. eapply R_key; eassumption.
    + exact Hf.
  - exists (step s m), f. auto.
Qed.

Theorem good_safe : safe_set PB good.
Proof.
  intros t (s & [| f] & HR & Hc); [discriminate |].
  pose proof (R_winner _ _ HR) as Ew. pose proof (R_to_move _ _ HR) as Em.
  cbn [check_node negb andb] in Hc.
  split; [rewrite Ew; cbn [opp]; destruct (winner s) as [[] |]; cbv beta iota in Hc; congruence |].
  destruct (winner s) as [[] |] eqn:Ews; cbv beta iota in Hc.
  - discriminate.
  - (* B has won *) split; intros Hn; rewrite Ew in Hn; discriminate.
  - destruct (huge_event s) eqn:Eh; [discriminate |].
    split.
    + intros _ Hturn. rewrite Em in Hturn. rewrite Hturn in Hc.
      rewrite some_move_existsb in Hc. apply existsb_exists in Hc as (m & Hin & Hm).
      destruct (hint s m); [| discriminate]. destruct (too_many (step s m)); [discriminate |].
      exists m. split; [exact (sim_mine s t m HR Hturn Ews Eh Hin) |].
      eapply good_next; eauto.
    + intros _ Hturn m Hin. rewrite Em in Hturn. cbn in Hturn. rewrite Hturn in Hc.
      assert (Hin' : In m (moves s)) by (eapply sim_theirs; eauto).
      rewrite all_moves_forallb, forallb_forall in Hc. specialize (Hc m Hin').
      destruct (too_many (step s m)); [discriminate |].
      eapply good_next; eauto.
Qed.

(** B is safe from every real state an entry abstracts. *)
Theorem cert_safe : forall s v t, lookup s = Some v -> R (entry s v) t -> safe PB t.
Proof.
  intros s v t Hl HR. exists good. split; [exact good_safe |].
  destruct (cert_ok _ _ Hl) as [fuel Hf]. exists (entry s v), fuel. split; [exact HR | exact Hf].
Qed.

End Checker.
