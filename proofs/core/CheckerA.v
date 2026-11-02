(** * Checking A-safety certificates with a growing Walker (REDUCTION.md, BIG mode)

    The mirror of [Checker]: A is the protagonist. A certificate maps
    normalised turn starts to a *line* [(c, b)]: A is safe whenever B's
    life is at most [c + b * n], where [n] measures A's BIG Walker.

    The abstraction differs from [Checker] in one place. A's Walker may grow
    without bound, and A's defence depends on that growth, so no cap on it
    is sound. Instead, a Walker with exactly [K] counters in a certificate
    state stands for a real Walker with [K + n] counters, for an unknown
    [n >= 0] shared by the whole turn. [K] is above every total of B's, so
    the only thing [n] changes is the damage the BIG Walker deals to B when
    unblocked (the [hit] edges); that is what [b] counts. Everything else
    follows [Checker]:
    - **B's life** is not in the state: a certificate state carries some
      life (each entry chooses its own, [entry m]), and each edge moves the
      line by B's life change.
    - **A's Thopters** are cut to [tt]: more Thopters only help A.
    - **A's graveyard** is dropped: A has no Elixir, so nothing reads it.
    - **B's Walkers** are saturated at [Hb] counters (R4, mirrored). Combat
      where such a Walker's exact size matters is a loss for A
      ([huge_event]), and so is B having more than [ott] Thopters
      ([too_many]).

    [RA n s t] says that the certificate state [s] abstracts the real state
    [t] whose BIG Walker has [K + n] counters. The soundness theorem
    [cert_safe] needs three facts about [RA] and the model, discharged in a
    separate file, as in [Checker]. *)

From Stdlib Require Import List Bool Arith ZArith Lia.
Import ListNotations.
From TCB.Spec Require Import Model Game.
From TCB.Proofs Require Import Checker.

Open Scope Z_scope.

Section CheckerA.

(** A's BIG size, B's saturation size, B's Thopter limit and A's Thopter
    cut. *)
Variables K Hb ott tt : nat.

(** ** Normalised states and keys *)

Definition clamp_b (w : walker) : walker :=
  mkWalker (Nat.min w.(counters) Hb) w.(wtapped) w.(sick).

(** Keep at most [tt] Thopters, dropping tapped ones first (as the solver). *)
Definition cut_a (sd : side) : side :=
  let extra := (sd.(thop_u) + sd.(thop_t) - tt)%nat in
  let dt := Nat.min extra sd.(thop_t) in
  set_thop_u (sd.(thop_u) - (extra - dt)) (set_thop_t (sd.(thop_t) - dt) sd).

(** The solver's [clamp], applied after every step. *)
Definition norm (s : state) : state :=
  mkState s.(active) s.(first_turn) (cut_a s.(sideA))
    (set_bf (map clamp_b s.(sideB).(bf)) s.(sideB)) s.(cmb) s.(pend).

Definition key (s : state) : state :=
  let s := norm s in
  mkState s.(active) s.(first_turn) (set_gy_w 0 s.(sideA))
    (set_life 0 s.(sideB)) s.(cmb) s.(pend).

(** The position an entry of the certificate stands for, with B on [m]
    life. Any [m] is sound: B's life is tracked by the line, and the
    certificate state's life only has to stay positive through the turn. *)
Definition entry (m : nat) (s : state) : state := map_side PB (set_life m) s.

Definition has_big (s : state) : bool :=
  existsb (fun w => Nat.eqb w.(counters) K) s.(sideA).(bf).

(** ** The BIG Walker's edges (the solver's [big_flags])

    A pump on the BIG Walker is [n -> n + 1]: the Walker goes back to [K]
    ([fix_big]). A pump from [K - 1] to [K] creates a BIG Walker with
    [n = 0], and is a loss if A already has one. Combat damage with the BIG
    Walker unblocked deals [n] more to B than the certificate state shows. *)
Definition is_pump_big (s : state) (m : move) : bool :=
  match s.(pend), m with
  | Window _ PA _, Pump i => Nat.eqb (walker_power s.(sideA) i) K
  | _, _ => false
  end.

Definition is_create (s : state) (m : move) : bool :=
  match s.(pend), m with
  | Window _ PA _, Pump i => Nat.eqb (S (walker_power s.(sideA) i)) K
  | _, _ => false
  end.

Definition is_hit (s : state) : bool :=
  match s.(pend), s.(active) with
  | ChooseDamage, PA =>
      existsb (fun '(i, bs) =>
        match bs with [] => Nat.eqb (walker_power s.(sideA) i) K | _ => false end)
        (combine s.(cmb).(atk) s.(cmb).(blk))
  | _, _ => false
  end.

Definition set_counters (i k : nat) (s : state) : state :=
  map_side PA (fun sd => set_bf (update_nth i (fun w => mkWalker k w.(wtapped) w.(sick)) sd.(bf)) sd) s.

Definition fix_big (s : state) (m : move) (s' : state) : state :=
  match m with
  | Pump i => if is_pump_big s m then set_counters i K s' else s'
  | _ => s'
  end.

(** The certificate's step. *)
Definition stepA (s : state) (m : move) : state := norm (fix_big s m (step s m)).

(** ** Events the abstraction can't follow *)

Definition is_huge (sd : side) (i : nat) : bool := (Hb <=? walker_power sd i)%nat.

(** Combat damage where a saturated B Walker's exact size matters (the
    solver's [huge_event] with B as the opponent): a huge B attacker
    unblocked, or blocked by enough toughness to kill it; or a huge B
    blocker meeting an A attacker big enough to kill it. *)
Definition huge_event (s : state) : bool :=
  match s.(pend) with
  | ChooseDamage =>
      let a := get_side s.(active) s in
      let d := get_side (defender s) s in
      let fights := combine s.(cmb).(atk) s.(cmb).(blk) in
      match s.(active) with
      | PB =>
          existsb (fun '(i, bs) =>
            is_huge a i &&
            match bs with
            | [] => true
            | _ => (Hb <=? list_sum (map (blocker_toughness d) bs))%nat
            end) fights
      | PA =>
          existsb (fun '(i, bs) =>
            (Hb <=? walker_power a i)%nat &&
            existsb (fun b => match b with BW j => is_huge d j | BT => false end) bs) fights
      end
  | _ => false
  end.

(** Combat where the BIG Walker could die. The solver checks that this
    never happens ([big_check]); here it is a loss. *)
Definition big_event (s : state) : bool :=
  match s.(pend) with
  | ChooseDamage =>
      let a := get_side s.(active) s in
      let d := get_side (defender s) s in
      let fights := combine s.(cmb).(atk) s.(cmb).(blk) in
      match s.(active) with
      | PA =>
          existsb (fun '(i, bs) =>
            Nat.eqb (walker_power a i) K &&
            match bs with [] => false | _ => (K <=? list_sum (map (blocker_toughness d) bs))%nat end) fights
      | PB =>
          existsb (fun '(i, bs) =>
            (K <=? walker_power a i)%nat &&
            existsb (fun b => match b with BW j => Nat.eqb (walker_power d j) K | BT => false end) bs) fights
      end
  | _ => false
  end.

Definition too_many (s : state) : bool :=
  (ott <? s.(sideB).(thop_u) + s.(sideB).(thop_t))%nat.

(** ** The checker *)

Variable lookup : state -> option (Z * Z).
Variable hint : state -> move -> bool.

Definition blife (s : state) : Z := Z.of_nat s.(sideB).(life).

(** Is A safe through the rest of this turn from [s], whenever B's life is
    at most [c + b * n]? Here [n] is known to be at least [lo] (the pumps on
    BIG since the entry). At the next turn start the certificate is
    consulted ([root] is false below the entry being checked); its line
    must be above this one for every [n >= lo]. The edge moves the line as
    the solver's [ltrans] does, the other way round: a pump on BIG reads the
    child at [n + 1] (and [lo + 1]), a new BIG at [n = 0], a hit takes [n]
    more life. A child line that is at most 0 for every [n >= lo] means B
    has died. *)
Fixpoint check_node (fuel : nat) (root : bool) (s : state) (c b : Z) (lo : nat) : bool :=
  match fuel with
  | O => false
  | S f =>
      match winner s with
      | Some _ => false
      | None =>
          if negb root && is_turn_start s then
            match lookup (key s) with
            | Some (c', b') =>
                (c + b * Z.of_nat lo <=? c' + b' * Z.of_nat lo) && (negb (has_big s) || (b <=? b'))
            | None => false
            end
          else if huge_event s || big_event s then false
          else
            let next m :=
              if is_create s m && has_big s then false else
              let s' := stepA s m in
              if too_many s' then false else
              match winner s' with
              | Some _ => false
              | None =>
                  let c1 := if is_pump_big s m then c - b else c in
                  let b1 := if is_create s m then 0 else b in
                  let c2 := c1 + (blife s' - blife s) in
                  let b2 := if is_hit s then b1 - 1 else b1 in
                  let lo2 := if is_pump_big s m then S lo else if is_create s m then O else lo in
                  if (c2 + b2 * Z.of_nat lo2 <=? 0) && (b2 <=? 0) then true
                  else check_node f false s' c2 b2 lo2
              end in
            match to_move s with
            | PA => some_move (fun m => if hint s m then next m else false) (moves s)
            | PB => all_moves next (moves s)
            end
      end
  end.

(** ** The abstraction relation *)

(** A's Walkers: the BIG one has [n] more counters for real, the others are
    exact. *)
Definition big_rel (n : nat) (w w' : walker) : Prop :=
  w.(wtapped) = w'.(wtapped) /\ w.(sick) = w'.(sick) /\
  ((w.(counters) = K /\ w'.(counters) = (K + n)%nat) \/
   (w.(counters) < K /\ w'.(counters) = w.(counters))%nat).

(** The Walkers in [l] with exactly [K] counters. *)
Definition bigs (l : list walker) : nat := length (filter (fun w => Nat.eqb w.(counters) K) l).

(** A's side: equal except for the BIG Walker, fewer Thopters and the
    graveyard. A has no Elixir anywhere. Without a BIG Walker, [n] is 0.
    There is at most one BIG Walker: [n] describes a single Walker. *)
Definition sideA_rel (n : nat) (a a' : side) : Prop :=
  a.(life) = a'.(life) /\ a.(city) = a'.(city) /\ a.(pool) = a'.(pool) /\
  a.(hand_w) = a'.(hand_w) /\
  a.(hand_e) = false /\ a'.(hand_e) = false /\
  a.(elixir_bf) = false /\ a'.(elixir_bf) = false /\
  Forall (eq CWalker) a.(library) /\ a.(library) = a'.(library) /\
  Forall2 (big_rel n) a.(bf) a'.(bf) /\
  (Forall (fun w => w.(counters) <> K) a.(bf) -> n = O) /\ (bigs a.(bf) <= 1)%nat /\
  (a.(thop_u) <= a'.(thop_u))%nat /\ (a.(thop_t) <= a'.(thop_t))%nat.

(** B's side: equal except for life (not related here) and saturated
    Walkers. *)
Definition sideB_rel (b b' : side) : Prop :=
  Forall2 (walker_rel Hb) b.(bf) b'.(bf) /\
  set_bf [] (set_life 0 b) = set_bf [] (set_life 0 b').

(** No Walker attacks twice, so an unblocked BIG Walker deals its extra
    [n] once. *)
Definition RA (n : nat) (s t : state) : Prop :=
  s.(active) = t.(active) /\ s.(first_turn) = t.(first_turn) /\
  s.(cmb) = t.(cmb) /\ s.(pend) = t.(pend) /\ no_a_shuffle s.(pend) /\
  sideA_rel n s.(sideA) t.(sideA) /\ sideB_rel s.(sideB) t.(sideB) /\
  NoDup s.(cmb).(atk).

Lemma RA_winner : forall n s t, RA n s t -> winner t = winner s.
Proof. intros n s t (_ & _ & _ & E & _). unfold winner. rewrite E. reflexivity. Qed.

Lemma RA_to_move : forall n s t, RA n s t -> to_move t = to_move s.
Proof. intros n s t (E1 & _ & _ & E4 & _). unfold to_move. rewrite E1, E4. reflexivity. Qed.

Lemma no_big_n : forall n s t, RA n s t -> has_big s = false -> n = O.
Proof.
  intros n s t (_ & _ & _ & _ & _ & A & _) Hnb. destruct A as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _).
  apply Hn. unfold has_big in Hnb. apply Forall_forall. intros w Hw E.
  assert (existsb (fun w => Nat.eqb w.(counters) K) s.(sideA).(bf) = true) as Ht
    by (apply existsb_exists; exists w; split; [exact Hw | apply Nat.eqb_eq; exact E]).
  congruence.
Qed.

Lemma pump_create : forall s m, is_pump_big s m = true -> is_create s m = false.
Proof.
  intros s m. unfold is_pump_big, is_create.
  destruct (pend s) as [st [] pa | | | | | st p l | w]; destruct m; try discriminate; try reflexivity.
  intros E. apply Nat.eqb_eq in E. rewrite E. apply Nat.eqb_neq. lia.
Qed.

Lemma pump_hit : forall s m, is_pump_big s m = true -> is_hit s = false.
Proof.
  intros s m. unfold is_pump_big, is_hit. destruct (pend s); try discriminate; reflexivity.
Qed.

Lemma create_hit : forall s m, is_create s m = true -> is_hit s = false.
Proof.
  intros s m. unfold is_create, is_hit. destruct (pend s); try discriminate; reflexivity.
Qed.

(** ** Soundness *)

(** Every entry checks, with some life for B and some fuel. *)
Hypothesis cert_ok : forall s c b, lookup s = Some (c, b) ->
  exists m fuel, check_node fuel true (entry m s) c b O = true.

(** The simulation facts (discharged in a separate file). *)
Hypothesis sim_mine : forall n s t m,
  RA n s t -> to_move s = PA -> winner s = None ->
  huge_event s = false -> big_event s = false ->
  In m (moves s) -> In m (moves t).
Hypothesis sim_theirs : forall n s t m,
  RA n s t -> to_move s = PB -> winner s = None ->
  huge_event s = false -> big_event s = false ->
  In m (moves t) -> In m (moves s).

(** A step either ends the real game in A's favour, or keeps [RA] (with
    [n] moved by the BIG edges) and moves B's life by the certificate's
    change, less [n] on a hit. *)
Hypothesis sim_step : forall n s t m,
  RA n s t -> In m (moves s) -> huge_event s = false -> big_event s = false ->
  (is_create s m && has_big s)%bool = false ->
  winner (stepA s m) = None -> (1 <= t.(sideB).(life))%nat ->
  winner (step t m) = Some PA \/
  (RA (if is_pump_big s m then S n else if is_create s m then O else n) (stepA s m) (step t m) /\
   (1 <= (step t m).(sideB).(life))%nat /\
   blife (step t m) = blife t + (blife (stepA s m) - blife s) - (if is_hit s then Z.of_nat n else 0)).

(** The key's fact: an entry abstracts the state it was looked up from. *)
Hypothesis RA_key : forall n m s t, RA n s t -> RA n (entry m (key s)) t.

Lemma check_below : forall f s c b lo, check_node f false s c b lo = true ->
  (winner s = None /\ is_turn_start s = true /\
   exists c' b', lookup (key s) = Some (c', b') /\
     c + b * Z.of_nat lo <= c' + b' * Z.of_nat lo /\ (has_big s = true -> b <= b')) \/
  check_node f true s c b lo = true.
Proof.
  intros [| f] s c b lo Hc; [discriminate |]. cbn [check_node negb andb] in *.
  destruct (winner s) as [w |] eqn:Ew; [discriminate |].
  destruct (is_turn_start s) eqn:Et; auto.
  left. repeat split; auto.
  destruct (lookup (key s)) as [[c' b'] |]; [| discriminate].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1.
  exists c', b'. repeat split; auto.
  intros Hbb. rewrite Hbb in H2. apply Z.leb_le. exact H2.
Qed.

(** [n] is the real BIG Walker's excess, [lo] the bound [check_node] knows. *)
Definition good (t : state) : Prop :=
  winner t = Some PA \/
  exists n s c b lo f, RA n s t /\ (lo <= n)%nat /\ (1 <= t.(sideB).(life))%nat /\
    blife t <= c + b * Z.of_nat n /\ check_node f true s c b lo = true.

Lemma good_entry : forall n s t c b, RA n s t -> (1 <= t.(sideB).(life))%nat ->
  is_turn_start s = true ->
  lookup (key s) = Some (c, b) -> blife t <= c + b * Z.of_nat n -> good t.
Proof.
  intros n s t c b HR Hl _ Hk Hv. right.
  destruct (cert_ok _ _ _ Hk) as (m & fuel & Hc).
  exists n, (entry m (key s)), c, b, O, fuel.
  split; [apply RA_key; exact HR |]. split; [lia |]. split; [exact Hl |]. split; [exact Hv | exact Hc].
Qed.

(** The edge's arithmetic: the child's line bounds the child's life. *)
Lemma next_bound : forall n s t m c b,
  RA n s t -> blife t <= c + b * Z.of_nat n ->
  (is_create s m && has_big s)%bool = false ->
  blife (step t m) = blife t + (blife (stepA s m) - blife s) - (if is_hit s then Z.of_nat n else 0) ->
  let n' := if is_pump_big s m then S n else if is_create s m then O else n in
  let c1 := if is_pump_big s m then c - b else c in
  let b1 := if is_create s m then 0 else b in
  let c2 := c1 + (blife (stepA s m) - blife s) in
  let b2 := if is_hit s then b1 - 1 else b1 in
  blife (step t m) <= c2 + b2 * Z.of_nat n'.
Proof.
  intros n s t m c b HR Hv Hc Hl n' c1 b1 c2 b2. subst n' c1 b1 c2 b2. rewrite Hl.
  destruct (is_pump_big s m) eqn:Ep.
  - rewrite (pump_create _ _ Ep), (pump_hit _ _ Ep). rewrite Nat2Z.inj_succ. nia.
  - destruct (is_create s m) eqn:Ec.
    + rewrite (create_hit _ _ Ec).
      destruct (has_big s) eqn:Eb; [discriminate |].
      rewrite (no_big_n _ _ _ HR Eb) in Hv. cbn in *. lia.
    + destruct (is_hit s); nia.
Qed.

Lemma good_next : forall n s t m f c b lo,
  RA n s t -> (lo <= n)%nat -> (1 <= t.(sideB).(life))%nat -> blife t <= c + b * Z.of_nat n ->
  In m (moves s) -> huge_event s = false -> big_event s = false ->
  (if is_create s m && has_big s then false else
   let s' := stepA s m in
   if too_many s' then false else
   match winner s' with
   | Some _ => false
   | None =>
       let c1 := if is_pump_big s m then c - b else c in
       let b1 := if is_create s m then 0 else b in
       let c2 := c1 + (blife s' - blife s) in
       let b2 := if is_hit s then b1 - 1 else b1 in
       let lo2 := if is_pump_big s m then S lo else if is_create s m then O else lo in
       if (c2 + b2 * Z.of_nat lo2 <=? 0) && (b2 <=? 0) then true
       else check_node f false s' c2 b2 lo2
   end) = true ->
  good (step t m).
Proof.
  intros n s t m f c b lo HR Hlo Hl Hv Hin Hh Hbe Hc.
  destruct (is_create s m && has_big s)%bool eqn:Ecb; [discriminate |].
  cbv zeta in Hc. destruct (too_many (stepA s m)); [discriminate |].
  destruct (winner (stepA s m)) as [w |] eqn:Ew; [discriminate |].
  destruct (sim_step n s t m HR Hin Hh Hbe Ecb Ew Hl) as [Hwin | (HR' & Hl' & Hlife)];
    [left; exact Hwin |].
  pose proof (next_bound n s t m c b HR Hv Ecb Hlife) as Hbd. cbv zeta in Hbd.
  set (n' := if is_pump_big s m then S n else if is_create s m then O else n) in *.
  set (lo2 := if is_pump_big s m then S lo else if is_create s m then O else lo) in *.
  assert (Hlo2 : (lo2 <= n')%nat)
    by (subst lo2 n'; destruct (is_pump_big s m); [lia |]; destruct (is_create s m); lia).
  set (c2 := (if is_pump_big s m then c - b else c) + (blife (stepA s m) - blife s)) in *.
  set (b2 := if is_hit s then (if is_create s m then 0 else b) - 1 else if is_create s m then 0 else b) in *.
  destruct ((c2 + b2 * Z.of_nat lo2 <=? 0) && (b2 <=? 0)) eqn:Ez.
  - (* B has no life left at any n >= lo2: impossible, it has at least 1 *)
    exfalso. apply andb_prop in Ez as [E1 E2]. apply Z.leb_le in E1, E2.
    unfold blife in Hbd. apply Nat2Z.inj_le in Hlo2. nia.
  - destruct (check_below f (stepA s m) c2 b2 lo2 Hc) as [(_ & Ht & c' & b' & Hk & H1 & H2) | Hr].
    + apply (good_entry n' (stepA s m) (step t m) c' b'); auto.
      destruct (has_big (stepA s m)) eqn:Ebig.
      * specialize (H2 eq_refl). apply Nat2Z.inj_le in Hlo2. nia.
      * pose proof (no_big_n _ _ _ HR' Ebig) as En. rewrite En in Hbd, Hlo2 |- *.
        assert (lo2 = O) as E0 by lia. rewrite E0 in H1. cbn in *. lia.
    + right. exists n', (stepA s m), c2, b2, lo2, f. split; [exact HR' |]. auto.
Qed.

Theorem good_safe : safe_set PA good.
Proof.
  intros t [Hw | (n & s & c & b & lo & [| f] & HR & Hlo & Hl & Hv & Hc)].
  - rewrite Hw. repeat split; try discriminate; intros Hn; discriminate.
  - discriminate.
  - pose proof (RA_winner _ _ _ HR) as Ew. pose proof (RA_to_move _ _ _ HR) as Em.
    cbn [check_node negb andb] in Hc.
    destruct (winner s) as [w |] eqn:Ews; [discriminate |].
    destruct (huge_event s) eqn:Eh; [discriminate |].
    destruct (big_event s) eqn:Eb; [discriminate |]. cbn [orb] in Hc.
    split; [rewrite Ew; discriminate |].
    split.
    + intros _ Hturn. rewrite Em in Hturn. rewrite Hturn in Hc.
      rewrite some_move_existsb in Hc. apply existsb_exists in Hc as (m & Hin & Hm).
      destruct (hint s m); [| discriminate].
      exists m. split; [exact (sim_mine n s t m HR Hturn Ews Eh Eb Hin) |].
      eapply good_next; eauto.
    + intros _ Hturn m Hin. rewrite Em in Hturn. cbn in Hturn. rewrite Hturn in Hc.
      assert (Hin' : In m (moves s)) by (eapply sim_theirs; eauto).
      rewrite all_moves_forallb, forallb_forall in Hc. specialize (Hc m Hin').
      eapply good_next; eauto.
Qed.

(** A is safe from every real state that a turn start [s] abstracts, if
    [s]'s key has an entry and B's life is on or below its line. *)
Theorem cert_safe : forall n s t c b, RA n s t -> (1 <= t.(sideB).(life))%nat ->
  is_turn_start s = true -> lookup (key s) = Some (c, b) -> blife t <= c + b * Z.of_nat n ->
  safe PA t.
Proof.
  intros n s t c b HR Hl Ht Hk Hv. exists good. split; [exact good_safe |].
  exact (good_entry n s t c b HR Hl Ht Hk Hv).
Qed.

End CheckerA.
