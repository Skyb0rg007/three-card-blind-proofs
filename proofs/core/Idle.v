(** * No idle moves: every legal move changes the state

    If some legal move left the state as it was, a player could repeat it
    forever and stall the game into a draw that the real game doesn't
    have. Every legal move changes something: a choice moves [pend] on,
    a pass moves the window or the step on, and every action in a window
    pays mana (changing the pool or City) or, for a Walker cast with X = 0,
    takes a card from the hand. *)
From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.
From TCB.Spec Require Import Model.

(** Paying at least one mana changes the pool or taps City. *)
Lemma pay_changes : forall n sd sd', pay n sd = Some sd' -> 1 <= n ->
  (sd'.(pool), sd'.(city)) <> (sd.(pool), sd.(city)).
Proof.
  intros n [l c p hw he bf e tu tt lib g] sd' Hp Hn. unfold pay in Hp. cbn in Hp.
  destruct (n <=? p) eqn:E1.
  - injection Hp as <-. cbn. apply Nat.leb_le in E1. intros H. injection H. lia.
  - destruct (c && (n <=? p + 2)) eqn:E2; [| discriminate].
    injection Hp as <-. cbn. apply andb_prop in E2 as [-> _]. intros H. injection H. discriminate.
Qed.

Lemma get_set_side : forall p sd s, get_side p (set_side p sd s) = sd.
Proof. intros [] sd s; reflexivity. Qed.

Lemma get_map_side : forall p f s, get_side p (map_side p f s) = f (get_side p s).
Proof. intros [] f s; reflexivity. Qed.

Lemma get_set_pend : forall p pd s, get_side p (set_pend pd s) = get_side p s.
Proof. intros [] pd s; reflexivity. Qed.

(** A paid action [k] that keeps the payer's pool and City changes the state. *)
Lemma paid_changes : forall n p s k, 1 <= n -> can_pay n (get_side p s) = true ->
  (forall s', (get_side p (k s')).(pool) = (get_side p s').(pool) /\
              (get_side p (k s')).(city) = (get_side p s').(city)) ->
  with_payment n p s k <> s.
Proof.
  intros n p s k Hn Hc Hk Heq. unfold can_pay in Hc. unfold with_payment in Heq.
  destruct (pay n (get_side p s)) as [sd |] eqn:Ep; [| discriminate].
  apply (pay_changes n _ sd Ep Hn).
  destruct (Hk (set_side p sd s)) as [E1 E2]. rewrite get_set_side in E1, E2.
  rewrite <- E1, <- E2, Heq. reflexivity.
Qed.

Lemma pend_changes : forall s s', s'.(pend) <> s.(pend) -> s' <> s.
Proof. intros s s' H E. subst. contradiction. Qed.

(** Every legal move changes the state. *)
Theorem step_changes : forall s m, In m (moves s) -> step s m <> s.
Proof.
  intros [act ft a b c pd] m Hin.
  set (s := mkState act ft a b c pd) in *.
  unfold moves in Hin. cbn [pend s] in Hin.
  destruct pd as [st p passed | | | | | st p cards | w].
  - (* a priority window *)
    unfold window_moves in Hin. cbn [In] in Hin.
    destruct Hin as [<- | Hin].
    + (* pass *)
      apply pend_changes. destruct passed.
      * destruct st; cbn; try discriminate.
        destruct (atk c), (atk_thop c); discriminate.
      * cbn. intros H. injection H. intros. destruct p; discriminate.
    + apply in_app_or in Hin as [Hin | Hin].
      * (* pump *)
        destruct (can_pay 1 (get_side p s)) eqn:Ec; [| contradiction].
        apply in_map_iff in Hin as (i & <- & _).
        apply paid_changes; [lia | assumption | intros s'; rewrite get_set_pend, get_map_side; split; reflexivity].
      * apply in_app_or in Hin as [Hin | Hin].
        -- (* Elixir *)
           destruct (elixir_bf (get_side p s) && can_pay 2 (get_side p s)) eqn:Ec; [| contradiction].
           destruct Hin as [<- | []]. apply andb_prop in Ec as [_ Ec].
           apply paid_changes; [lia | assumption | intros s'; rewrite get_set_pend, get_set_side; split; reflexivity].
        -- (* sorcery-speed casts *)
           destruct (player_eqb p (active s) && is_main st); [| contradiction].
           apply in_app_or in Hin as [Hin | Hin].
           ++ destruct (0 <? hand_w (get_side p s)) eqn:Eh; [| contradiction].
              destruct Hin as [<- | Hin].
              ** (* X = 0: pay nothing, lose a card *)
                 apply Nat.ltb_lt in Eh. intros Heq.
                 apply (f_equal (fun t => hand_w (get_side p t))) in Heq.
                 revert Heq Eh. destruct p; cbn; lia.
              ** destruct (can_pay 2 (get_side p s)) eqn:Ec; [| contradiction].
                 destruct Hin as [<- | []].
                 apply paid_changes; [lia | assumption | intros s'; rewrite get_set_pend, get_set_side; split; reflexivity].
           ++ destruct (hand_e (get_side p s) && can_pay 1 (get_side p s)) eqn:Ec; [| contradiction].
              destruct Hin as [<- | []]. apply andb_prop in Ec as [_ Ec].
              apply paid_changes; [lia | assumption | intros s'; rewrite get_set_pend, get_map_side; split; reflexivity].
  - (* attack *)
    unfold attack_moves in Hin. apply in_flat_map in Hin as (ws & _ & Hin).
    apply in_map_iff in Hin as (k & <- & _).
    apply pend_changes. cbn. discriminate.
  - (* block *)
    unfold block_moves in Hin. apply in_flat_map in Hin as (wb & _ & Hin).
    apply in_flat_map in Hin as (tb & _ & Hin). apply in_map_iff in Hin as (tr & <- & _).
    apply pend_changes. cbn [step pend s]. unfold do_block.
    destruct (has_multiblock _); cbn; discriminate.
  - (* damage assignment order *)
    unfold order_moves in Hin. apply in_map_iff in Hin as (os & <- & _).
    apply pend_changes. cbn. discriminate.
  - (* combat damage *)
    unfold damage_moves in Hin. apply in_map_iff in Hin as (js & <- & _).
    apply pend_changes. cbn [step pend s]. unfold do_damage. cbv zeta.
    destruct (_ <=? _); cbn; discriminate.
  - (* library order *)
    apply in_map_iff in Hin as (lib & <- & _).
    apply pend_changes. cbn. discriminate.
  - contradiction.
Qed.
