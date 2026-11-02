(** * Monotonicity lemmas behind the solver's reductions

    ** Life (REDUCTION.md R2 and R5)

    More life never hurts a player. Life is only read by the lethal check
    in combat damage, and only changed by adding (Elixir) or subtracting
    (combat damage). So a state where [p] has [k] more life behaves exactly
    like the original, except that some lines where [p] lost no longer end
    there.

    Consequences, for either player [p]:
    - [wins_bump]: if [p] wins, [p] wins with more life;
    - [safe_bump]: if [p] is safe, [p] is safe with more life;
    - [wins_opp_bump]: if the opponent wins against [p] with more life, it
      wins against [p] with less.

    These justify replacing B's life by a threshold (R2) and pinning A's
    life at 20 for B-safety (R5). *)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.
From TCB.Spec Require Import Model Game.
From TCB.Proofs Require Import GameFacts.

Definition player_eq_dec (p q : player) : {p = q} + {p <> q}.
Proof. decide equality. Defined.

Definition bump_side (k : nat) (d : side) : side := set_life (d.(life) + k) d.

Definition bump (p : player) (k : nat) (s : state) : state :=
  map_side p (bump_side k) s.

(** [p] with [u] untapped and [v] tapped Thopters (used for R3 below). *)
Definition more_thop (p : player) (u v : nat) (s : state) : state :=
  map_side p (fun d => set_thop_t v (set_thop_u u d)) s.

Lemma winner_bump : forall p k s, winner (bump p k s) = winner s.
Proof. intros [] k []; reflexivity. Qed.

Lemma to_move_bump : forall p k s, to_move (bump p k s) = to_move s.
Proof. intros [] k []; reflexivity. Qed.


(** Reduce [step] on a state whose fields are known. Strong reduction,
    restricted to the model's own definitions, so arithmetic and list
    functions stay folded. *)
Ltac simpl_step :=
  cbv beta iota zeta delta [step bump bump_side more_thop map_side get_side set_side
    do_pump do_elixir do_cast_walker do_cast_elixir do_attack do_block do_order
    do_damage end_step next_turn empty_pools with_payment pay defender draw
    opp andb orb negb player_eqb is_main walker_power blocker_toughness
    untap_side bury set_life set_city set_pool set_hand_w set_hand_e set_bf
    set_elixir_bf set_thop_u set_thop_t set_library set_gy_w set_cmb set_pend
    winner Model.pend Model.active Model.first_turn Model.sideA Model.sideB
    Model.cmb Model.life Model.city Model.pool Model.hand_w Model.hand_e Model.bf
    Model.elixir_bf Model.thop_u Model.thop_t Model.library Model.gy_w
    Model.atk Model.atk_thop Model.blk Model.trades] in *.

(** Case split on every stuck test in the goal, simplifying after each
    with [simp]. *)
Ltac split_with simp :=
  repeat (match goal with
  | |- context [?a <=? ?b] => destruct (a <=? b) eqn:?
  | |- context [?a <? ?b] => destruct (a <? b) eqn:?
  | |- context [if ?b then _ else _] => is_var b; destruct b
  | |- context [?b && _] => is_var b; destruct b
  | |- context [is_main ?st] => is_var st; destruct st
  | |- context [has_multiblock ?c] => destruct (has_multiblock c)
  | |- context [match ?n with 0 => _ | S _ => _ end] => is_var n; destruct n
  | |- context [match ?l with [] => _ | _ :: _ => _ end] => is_var l; destruct l
  | |- context [match ?c with CWalker => _ | CElixir => _ end] => is_var c; destruct c
  end; simp).

Ltac split_tests :=
  split_with ltac:(cbv beta iota zeta delta [andb orb negb opp player_eqb is_main pred] in * ).

Ltac leb_facts :=
  repeat match goal with
  | H : (_ <=? _) = true |- _ => apply Nat.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Nat.leb_gt in H
  end.

Ltac simpl_moves :=
  cbv beta iota zeta delta [moves window_moves attack_moves block_moves
    order_moves damage_moves can_pay pay defender opp andb orb negb player_eqb
    walker_power blocker_toughness bump bump_side set_life is_main more_thop
    map_side get_side set_side set_pool set_city set_thop_u set_thop_t Model.pend Model.active Model.sideA Model.sideB
    Model.cmb Model.life Model.city Model.pool Model.hand_w Model.hand_e Model.bf
    Model.elixir_bf Model.thop_u Model.thop_t Model.library Model.gy_w] in *.

Lemma moves_bump : forall p k s, moves (bump p k s) = moves s.
Proof.
  intros [] k [[] ? [] [] ? [? [] ? | | | | | ? ? ? | ?]];
    simpl_moves; split_tests; reflexivity.
Qed.

(** The one place where life matters: the step must not be a loss for [p]. *)
Ltac fields :=
  repeat match goal with
  | |- mkState _ _ _ _ _ _ = mkState _ _ _ _ _ _ => f_equal
  | |- mkSide _ _ _ _ _ _ _ _ _ _ _ = mkSide _ _ _ _ _ _ _ _ _ _ _ => f_equal
  end.

Ltac finish Hw :=
  split_tests; leb_facts;
  try reflexivity; try lia; try (exfalso; apply Hw; reflexivity);
  fields; lia.

Lemma step_bump : forall p k s m,
  winner (step s m) <> Some (opp p) ->
  step (bump p k s) m = bump p k (step s m).
Proof.
  intros p k [act ft [] [] [] pd] m Hw.
  destruct pd as [st q passed | | | | | st q cards | w], m;
    try (destruct p, act; reflexivity).
  - (* Pass *)
    destruct passed; [| destruct p, q; reflexivity];
      destruct p, q, act, st, ft; simpl_step; finish Hw.
  - (* Pump *) destruct p, q, act; simpl_step; finish Hw.
  - (* ActElixir *) destruct p, q, act; simpl_step; finish Hw.
  - (* CastWalker *) destruct p, q, act; simpl_step; finish Hw.
  - (* CastElixir *) destruct p, q, act; simpl_step; finish Hw.
  - (* Block *) destruct p, act; simpl_step; finish Hw.
  - (* Assign *) destruct p, act; simpl_step; finish Hw.
  - (* Arrange *) destruct p, q, act; simpl_step; finish Hw.
Qed.

Lemma wins_bump : forall p k s, wins p s -> wins p (bump p k s).
Proof.
  intros p k s Hw. induction Hw as [s Hwin | s m Hnone Hturn Hin Hw IH | s Hnone Hturn Hall IH].
  - apply wins_over. rewrite winner_bump. exact Hwin.
  - apply wins_mine with m.
    + rewrite winner_bump. exact Hnone.
    + rewrite to_move_bump. exact Hturn.
    + rewrite moves_bump. exact Hin.
    + rewrite step_bump; [exact IH | apply wins_winner; exact Hw].
  - apply wins_theirs.
    + rewrite winner_bump. exact Hnone.
    + rewrite to_move_bump. exact Hturn.
    + intros m Hin. rewrite moves_bump in Hin.
      rewrite step_bump; [apply IH; exact Hin | apply wins_winner; apply Hall; exact Hin].
Qed.

Lemma safe_bump : forall p k s, safe p s -> safe p (bump p k s).
Proof.
  intros p k s [S [HS Hs]].
  exists (fun t => exists s, S s /\ t = bump p k s). split; [| eauto].
  intros t [s0 [HS0 ->]]. destruct (HS s0 HS0) as [Hnot [Hmine Htheirs]].
  split; [rewrite winner_bump; exact Hnot |]. split.
  - intros Hnone Hturn. rewrite winner_bump in Hnone. rewrite to_move_bump in Hturn.
    destruct (Hmine Hnone Hturn) as [m [Hin HSm]].
    exists m. rewrite moves_bump. split; [exact Hin |].
    exists (step s0 m). split; [exact HSm |].
    apply step_bump. exact (proj1 (HS _ HSm)).
  - intros Hnone Hturn m Hin. rewrite winner_bump in Hnone. rewrite to_move_bump in Hturn.
    rewrite moves_bump in Hin.
    exists (step s0 m). split; [apply Htheirs; auto |].
    apply step_bump. exact (proj1 (HS _ (Htheirs Hnone Hturn m Hin))).
Qed.

Lemma wins_opp_bump : forall p k s, wins (opp p) (bump p k s) -> wins (opp p) s.
Proof.
  intros p k s Hw. remember (bump p k s) as t eqn:Ht. revert s Ht.
  induction Hw as [t Hwin | t m Hnone Hturn Hin Hw IH | t Hnone Hturn Hall IH];
    intros s ->.
  - apply wins_over. rewrite winner_bump in Hwin. exact Hwin.
  - rewrite winner_bump in Hnone. rewrite to_move_bump in Hturn. rewrite moves_bump in Hin.
    destruct (winner (step s m)) as [w |] eqn:E.
    + destruct (player_eq_dec w (opp p)) as [-> | Hne'].
      * apply wins_mine with m; auto. apply wins_over. exact E.
      * apply wins_mine with m; auto. apply IH. apply step_bump. congruence.
    + apply wins_mine with m; auto. apply IH. apply step_bump. congruence.
  - rewrite winner_bump in Hnone. rewrite to_move_bump in Hturn.
    apply wins_theirs; auto. intros m Hin. rewrite moves_bump in IH.
    destruct (winner (step s m)) as [w |] eqn:E.
    + destruct (player_eq_dec w (opp p)) as [-> | Hne'].
      * apply wins_over. exact E.
      * apply (IH m Hin). apply step_bump. congruence.
    + apply (IH m Hin). apply step_bump. congruence.
Qed.

(** ** Certificates with dominated entries

    A certificate may answer for a position with an entry where the
    opponent [q] of the protagonist has more life (the entry is [bump q d]
    of the position), or where the protagonist [p] has less life (the
    position is [bump p d] of the entry). The two closures below turn a set
    of positions that is safe "up to such bumps" into a safe set. *)

Lemma bump_bump : forall p k k' s, bump p k (bump p k' s) = bump p (k' + k) s.
Proof.
  intros [] k k' [? ? [] [] ? ?];
    unfold bump, bump_side, map_side, get_side, set_side, set_life; cbn; do 2 f_equal; lia.
Qed.

Lemma bump_zero : forall p s, bump p 0 s = s.
Proof.
  intros [] [? ? [] [] ? ?];
    unfold bump, bump_side, map_side, get_side, set_side, set_life; cbn; rewrite Nat.add_0_r; reflexivity.
Qed.

(** What [safe_set p] asks of one position, with the successors in [T]. *)
Definition safe_step (p : player) (T : state -> Prop) (s : state) : Prop :=
  winner s <> Some (opp p) /\
  (winner s = None -> to_move s = p -> exists m, In m (moves s) /\ T (step s m)) /\
  (winner s = None -> to_move s = opp p -> forall m, In m (moves s) -> T (step s m)).

(** The positions where [p] has at least the life of a position in [S]. *)
Definition up (p : player) (S : state -> Prop) (t : state) : Prop :=
  exists d t0, t = bump p d t0 /\ S t0.

Lemma up_self : forall p (S : state -> Prop) t, S t -> up p S t.
Proof. intros p S t H. exists 0, t. rewrite bump_zero. auto. Qed.

(** [p] safe with less life is safe with more ([safe_bump]), so a set
    whose successors are safe up to raising [p]'s life is safe once closed
    upwards. *)
Lemma safe_set_up : forall p S, (forall s, S s -> safe_step p (up p S) s) -> safe_set p (up p S).
Proof.
  intros p S HS t (d & t0 & -> & H0).
  destruct (HS t0 H0) as (Hw & Hmine & Htheirs).
  assert (Hst : forall m, up p S (step t0 m) -> up p S (step (bump p d t0) m)).
  { intros m (d' & t1 & E & H1). destruct (HS t1 H1) as (Hw1 & _ & _).
    exists (d' + d), t1. split; [| exact H1].
    rewrite step_bump by (rewrite E, winner_bump; exact Hw1). rewrite E. apply bump_bump. }
  split; [rewrite winner_bump; exact Hw |]. split.
  - intros Hn Ht. rewrite winner_bump in Hn. rewrite to_move_bump in Ht.
    destruct (Hmine Hn Ht) as (m & Hin & Hm). exists m. rewrite moves_bump. auto.
  - intros Hn Ht m Hin. rewrite winner_bump in Hn. rewrite to_move_bump in Ht. rewrite moves_bump in Hin.
    auto.
Qed.

(** The positions where the protagonist [opp q] has won, or where [q] has
    at most the life of a position in [S]. *)
Definition down (q : player) (S : state -> Prop) (t : state) : Prop :=
  winner t = Some (opp q) \/ exists d, S (bump q d t).

Lemma down_self : forall q (S : state -> Prop) t, S t -> down q S t.
Proof. intros q S t H. right. exists 0. rewrite bump_zero. exact H. Qed.

(** The opponent [q] winning with more life wins with less
    ([wins_opp_bump]); so a set whose successors are safe up to lowering
    [q]'s life is safe once closed downwards. *)
Lemma safe_set_down : forall q S, (forall s, S s -> safe_step (opp q) (down q S) s) ->
  safe_set (opp q) (down q S).
Proof.
  intros q S HS t [Hw | (d & H0)].
  - rewrite Hw. rewrite opp_involutive. split; [| split; intros Hn; discriminate].
    intros E. injection E. apply opp_neq.
  - destruct (HS _ H0) as (Hw & Hmine & Htheirs).
    assert (Hst : forall m, down q S (step (bump q d t) m) -> down q S (step t m)).
    { intros m Hd. destruct (winner (step t m)) as [w |] eqn:E.
      - destruct (player_eq_dec w (opp q)) as [-> | Hne]; [left; exact E |].
        rewrite step_bump in Hd by (rewrite E; congruence).
        destruct Hd as [Hd | (d' & Hd)]; [rewrite winner_bump, E in Hd; congruence |].
        right. exists (d + d'). rewrite <- bump_bump. exact Hd.
      - rewrite step_bump in Hd by (rewrite E; discriminate).
        destruct Hd as [Hd | (d' & Hd)]; [rewrite winner_bump, E in Hd; discriminate |].
        right. exists (d + d'). rewrite <- bump_bump. exact Hd. }
    rewrite winner_bump in Hw. rewrite to_move_bump in Hmine, Htheirs. rewrite winner_bump in Hmine, Htheirs.
    split; [exact Hw |]. split.
    + intros Hn Ht. destruct (Hmine Hn Ht) as (m & Hin & Hm). rewrite moves_bump in Hin. eauto.
    + intros Hn Ht m Hin. rewrite <- (moves_bump q d) in Hin. auto.
Qed.

(** * Thopter monotonicity (REDUCTION.md R3)

    A player with at least as many untapped and at least as many tapped
    Thopters, everything else equal, is at least as well off. The player can
    make exactly the same moves and ignore the extra Thopters: their own
    attack and block options only grow, and nothing the opponent can do
    depends on them. Every operation on Thopter counts (attacking, untapping,
    blocking, dying, trading) is monotone, so the relation survives each step;
    with truncated subtraction this holds even for moves that would not be
    legal. *)

Definition thop_le (p : player) (s t : state) : Prop :=
  exists u v, (get_side p s).(thop_u) <= u /\ (get_side p s).(thop_t) <= v /\
              t = more_thop p u v s.

Lemma winner_thop : forall p s t, thop_le p s t -> winner t = winner s.
Proof. intros [] [] t [u [v [_ [_ ->]]]]; reflexivity. Qed.

Lemma to_move_thop : forall p s t, thop_le p s t -> to_move t = to_move s.
Proof. intros [] [] t [u [v [_ [_ ->]]]]; reflexivity. Qed.

Ltac fin_thop :=
  split_tests; leb_facts; repeat split; try lia; try reflexivity.

Lemma step_thop : forall p s t m, thop_le p s t -> thop_le p (step s m) (step t m).
Proof.
  intros p s t m [u [v [Hu [Hv ->]]]].
  exists (get_side p (step (more_thop p u v s) m)).(thop_u),
         (get_side p (step (more_thop p u v s) m)).(thop_t).
  destruct s as [act ft [] [] [] pd].
  destruct pd as [st q passed | | | | | st q cards | w], m;
    try (destruct p, act; cbv beta iota delta [more_thop map_side get_side set_side
      set_thop_u set_thop_t step Model.pend] in *; cbn in *; repeat split; lia).
  - (* Pass *)
    destruct passed; [| destruct p, q, act; simpl_step; fin_thop].
    destruct p, q, act, st, ft; simpl_step; fin_thop.
  - (* Pump *) destruct p, q, act; simpl_step; fin_thop.
  - (* ActElixir *) destruct p, q, act; simpl_step; fin_thop.
  - (* CastWalker *) destruct p, q, act; simpl_step; fin_thop.
  - (* CastElixir *) destruct p, q, act; simpl_step; fin_thop.
  - (* Block *) destruct p, act; simpl_step; fin_thop.
  - (* Assign *) destruct p, act; simpl_step; fin_thop.
  - (* Arrange *) destruct p, q, act; simpl_step; fin_thop.
Qed.

(** Only the player's own attack and block options depend on their Thopter
    counts; every other move list is unchanged. *)
Lemma moves_thop_eq : forall p s t, thop_le p s t ->
  ~ (s.(pend) = ChooseAttack /\ s.(active) = p) ->
  ~ (s.(pend) = ChooseBlock /\ s.(active) = opp p) ->
  moves t = moves s.
Proof.
  intros p s t [u [v [_ [_ ->]]]] H1 H2.
  destruct p, s as [[] ? [] [] ? [? [] ? | | | | | ? ? ? | ?]]; cbn in H1, H2;
    try (exfalso; apply H1; split; reflexivity);
    try (exfalso; apply H2; split; reflexivity);
    simpl_moves; split_tests; reflexivity.
Qed.

Lemma moves_thop_opp : forall p s t, thop_le p s t -> to_move s = opp p -> moves t = moves s.
Proof.
  intros p s t Hle Hm. apply (moves_thop_eq p s t Hle); intros [E1 E2];
    unfold to_move in Hm; rewrite E1 in Hm.
  - rewrite E2 in Hm. exact (opp_neq p (eq_sym Hm)).
  - rewrite E2, opp_involutive in Hm. exact (opp_neq p (eq_sym Hm)).
Qed.

Lemma bounded_vectors_mono : forall n a b v,
  a <= b -> In v (bounded_vectors n a) -> In v (bounded_vectors n b).
Proof.
  induction n; intros a b v Hab Hv; cbn [bounded_vectors] in *; [exact Hv |].
  apply in_flat_map in Hv as [k [Hk Hv]]. apply in_map_iff in Hv as [w [<- Hw]].
  apply in_seq in Hk. apply in_flat_map. exists k. split; [apply in_seq; lia |].
  apply in_map. apply IHn with (a - k); [lia | exact Hw].
Qed.

Ltac simpl_combat_moves :=
  cbv beta iota zeta delta [moves attack_moves block_moves defender opp
    more_thop map_side get_side set_side set_thop_u set_thop_t Model.pend Model.active
    Model.sideA Model.sideB Model.cmb Model.thop_u Model.thop_t Model.bf] in *.

Lemma moves_thop_mine : forall p s t m, thop_le p s t -> In m (moves s) -> In m (moves t).
Proof.
  intros p [act ft sa sb c pd] t m Hle Hin.
  destruct p, act, pd;
    try (rewrite (moves_thop_eq _ _ _ Hle);
         [exact Hin | cbn; intros [? ?]; discriminate | cbn; intros [? ?]; discriminate]);
    destruct Hle as [u [v [Hu [Hv ->]]]]; destruct sa, sb; simpl_combat_moves.
  (* the player's own attacks and blocks *)
  all: first
    [ apply in_flat_map in Hin as [wb [Hwb Hin]]; apply in_flat_map in Hin as [tb [Htb Hin]];
      apply in_map_iff in Hin as [k [<- Hk]]; apply in_seq in Hk;
      apply in_flat_map; exists wb; split; [exact Hwb |];
      apply in_flat_map; exists tb; split; [eapply bounded_vectors_mono; [| exact Htb]; lia |];
      apply in_map; apply in_seq; lia
    | apply in_flat_map in Hin as [ws [Hws Hin]]; apply in_map_iff in Hin as [k [<- Hk]];
      apply in_seq in Hk; apply in_flat_map; exists ws; split; [exact Hws |];
      apply in_map; apply in_seq; lia ].
Qed.

Theorem wins_thop : forall p s t, thop_le p s t -> wins p s -> wins p t.
Proof.
  intros p s t Hle Hw. revert t Hle.
  induction Hw as [s Hwin | s m Hnone Hturn Hin Hw IH | s Hnone Hturn Hall IH];
    intros t Hle.
  - apply wins_over. rewrite (winner_thop _ _ _ Hle). exact Hwin.
  - apply wins_mine with m.
    + rewrite (winner_thop _ _ _ Hle). exact Hnone.
    + rewrite (to_move_thop _ _ _ Hle). exact Hturn.
    + exact (moves_thop_mine _ _ _ _ Hle Hin).
    + apply IH. apply step_thop. exact Hle.
  - apply wins_theirs.
    + rewrite (winner_thop _ _ _ Hle). exact Hnone.
    + rewrite (to_move_thop _ _ _ Hle). exact Hturn.
    + intros m Hin. rewrite (moves_thop_opp _ _ _ Hle Hturn) in Hin.
      apply (IH m Hin). apply step_thop. exact Hle.
Qed.

Theorem safe_thop : forall p s t, thop_le p s t -> safe p s -> safe p t.
Proof.
  intros p s t Hle [S [HS Hs]].
  exists (fun t => exists s, S s /\ thop_le p s t). split; [| eauto].
  intros t' [s0 [HS0 Hle0]]. destruct (HS s0 HS0) as [Hnot [Hmine Htheirs]].
  split; [rewrite (winner_thop _ _ _ Hle0); exact Hnot |]. split.
  - intros Hnone Hturn.
    rewrite (winner_thop _ _ _ Hle0) in Hnone. rewrite (to_move_thop _ _ _ Hle0) in Hturn.
    destruct (Hmine Hnone Hturn) as [m [Hin HSm]].
    exists m. split; [exact (moves_thop_mine _ _ _ _ Hle0 Hin) |].
    exists (step s0 m). split; [exact HSm | apply step_thop; exact Hle0].
  - intros Hnone Hturn m Hin.
    rewrite (winner_thop _ _ _ Hle0) in Hnone. rewrite (to_move_thop _ _ _ Hle0) in Hturn.
    rewrite (moves_thop_opp _ _ _ Hle0 Hturn) in Hin.
    exists (step s0 m). split; [apply Htheirs; auto | apply step_thop; exact Hle0].
Qed.
