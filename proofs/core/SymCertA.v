(** * A-safety certificates that store one order of A's Walkers

    [CheckerA.cert_safe] again, for a [lookup] that may answer for a
    position with the entry of the position with A's two Walkers swapped
    ([sw = true]), e.g. a table of [Sym.normA]-sorted keys looked up with
    [lookup s = table (normA s)]. The checker itself is unchanged; the safe
    set is closed under [Sym] as well as under more A life
    ([Sym.safe_set_up_sym]). *)

From Stdlib Require Import List Bool Arith ZArith Lia.
Import ListNotations.
From TCB.Spec Require Import Model Game.
From TCB.Proofs Require Import Mono Sym SymCert.
From TCB.Proofs Require Import CheckerA SaturationA.

Open Scope Z_scope.

Lemma sideB_bumpA : forall d s, (bump PA d s).(sideB) = s.(sideB).
Proof. intros d []. reflexivity. Qed.

Section CheckerASym.

Variables K Hb ott tt : nat.
Hypothesis HbK : (Hb < K)%nat.
Hypothesis Hb1 : (1 <= Hb)%nat.
Variable lookup : state -> option (Z * Z).
Variable hint : state -> move -> bool.

Notation RA := (RA K Hb).
Notation good := (good K Hb ott tt lookup hint).
Notation check_node := (check_node K Hb ott tt lookup hint).
Notation key := (key Hb tt).
Notation stepA := (stepA K Hb tt).
Notation is_create := (is_create K).
Notation is_pump_big := (is_pump_big K).
Notation is_hit := (is_hit K).
Notation has_big := (has_big K).
Notation huge_event := (huge_event Hb).
Notation big_event := (big_event K).
Notation too_many := (too_many ott).

Hypothesis cert_ok : forall s c b, lookup s = Some (c, b) ->
  exists d e m fuel (sw : bool), (if sw then swapA s else s) = bump PA d e /\
    check_node fuel true (entry m e) c b O = true.

Lemma good_entry_sym : forall n s t c b, RA n s t -> (1 <= t.(sideB).(life))%nat ->
  lookup (key s) = Some (c, b) -> blife t <= c + b * Z.of_nat n -> up PA (symc good) t.
Proof.
  intros n s t c b HR Hl Hk Hv.
  destruct (cert_ok _ _ _ Hk) as (d & e & m & fuel & sw & Ee & Hc).
  pose proof (SaturationA.RA_key K Hb tt HbK Hb1 n m s t HR) as HR'.
  assert (HR1 : RA n (entry m (if sw then swapA (key s) else key s)) (if sw then swapA t else t))
    by (destruct sw; [rewrite entryA_swapA; apply RA_swapA |]; exact HR').
  rewrite Ee, entry_bump in HR1.
  destruct (RA_unbump K Hb n d (entry m e) _ HR1) as (t0 & Et1 & HR0).
  assert (Et : t = bump PA d (if sw then swapA t0 else t0)).
  { destruct sw; [| exact Et1]. rewrite <- swapA_bump, <- Et1. symmetry. apply swapA_swapA. }
  assert (EB : t0.(sideB) = t.(sideB))
    by (rewrite Et, sideB_bumpA; destruct sw; [rewrite sideB_swapA |]; reflexivity).
  exists d, (if sw then swapA t0 else t0). split; [exact Et |].
  exists t0. split.
  - right. exists n, (entry m e), c, b, O, fuel. split; [exact HR0 |]. split; [lia |].
    split; [rewrite EB; exact Hl |]. split; [unfold blife; rewrite EB; exact Hv | exact Hc].
  - destruct sw; [apply syms_one, Sym_swapA | apply syms_refl].
Qed.

(** [CheckerA.good_next], with the entry closed under [Sym]. *)
Lemma good_next_sym : forall n s t m f c b lo,
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
  up PA (symc good) (step t m).
Proof.
  intros n s t m f c b lo HR Hlo Hl Hv Hin Hh Hbe Hc.
  destruct (is_create s m && has_big s)%bool eqn:Ecb; [discriminate |].
  cbv zeta in Hc. destruct (too_many (stepA s m)); [discriminate |].
  destruct (winner (stepA s m)) as [w |] eqn:Ew; [discriminate |].
  destruct (SaturationA.sim_step K Hb tt HbK Hb1 n s t m HR Hin Hh Hbe Ecb Ew Hl)
    as [Hwin | (HR' & Hl' & Hlife)];
    [apply up_self, symc_self; left; exact Hwin |].
  pose proof (next_bound K Hb tt n s t m c b HR Hv Ecb Hlife) as Hbd. cbv zeta in Hbd.
  set (n' := if is_pump_big s m then S n else if is_create s m then O else n) in *.
  set (lo2 := if is_pump_big s m then S lo else if is_create s m then O else lo) in *.
  assert (Hlo2 : (lo2 <= n')%nat)
    by (subst lo2 n'; destruct (is_pump_big s m); [lia |]; destruct (is_create s m); lia).
  set (c2 := (if is_pump_big s m then c - b else c) + (blife (stepA s m) - blife s)) in *.
  set (b2 := if is_hit s then (if is_create s m then 0 else b) - 1 else if is_create s m then 0 else b) in *.
  destruct ((c2 + b2 * Z.of_nat lo2 <=? 0) && (b2 <=? 0)) eqn:Ez.
  - exfalso. apply andb_prop in Ez as [E1 E2]. apply Z.leb_le in E1, E2.
    unfold blife in Hbd. apply Nat2Z.inj_le in Hlo2. nia.
  - destruct (check_below K Hb ott tt lookup hint f (stepA s m) c2 b2 lo2 Hc)
      as [(_ & Ht & c' & b' & Hk & H1 & H2) | Hr].
    + apply (good_entry_sym n' (stepA s m) (step t m) c' b'); auto.
      destruct (has_big (stepA s m)) eqn:Ebig.
      * specialize (H2 eq_refl). apply Nat2Z.inj_le in Hlo2. nia.
      * pose proof (no_big_n _ _ _ _ _ HR' Ebig) as En. rewrite En in Hbd, Hlo2 |- *.
        assert (lo2 = O) as E0 by lia. rewrite E0 in H1. cbn in *. lia.
    + apply up_self, symc_self. right. exists n', (stepA s m), c2, b2, lo2, f. split; [exact HR' |]. auto.
Qed.

Lemma good_step_sym : forall t, good t -> safe_step PA (up PA (symc good)) t.
Proof.
  intros t [Hw | (n & s & c & b & lo & [| f] & HR & Hlo & Hl & Hv & Hc)]; unfold safe_step.
  - rewrite Hw. repeat split; try discriminate; intros Hn; discriminate.
  - discriminate.
  - pose proof (RA_winner _ _ _ _ _ HR) as Ew. pose proof (RA_to_move _ _ _ _ _ HR) as Em.
    cbn [CheckerA.check_node negb andb] in Hc.
    destruct (winner s) as [w |] eqn:Ews; [discriminate |].
    destruct (huge_event s) eqn:Eh; [discriminate |].
    destruct (big_event s) eqn:Eb; [discriminate |]. cbn [orb] in Hc.
    split; [rewrite Ew; discriminate |].
    split.
    + intros _ Hturn. rewrite Em in Hturn. rewrite Hturn in Hc.
      rewrite Checker.some_move_existsb in Hc. apply existsb_exists in Hc as (m & Hin & Hm).
      destruct (hint s m); [| discriminate].
      exists m. split; [exact (SaturationA.sim_mine K Hb HbK Hb1 n s t m HR Hturn Ews Eh Eb Hin) |].
      eapply good_next_sym; eauto.
    + intros _ Hturn m Hin. rewrite Em in Hturn. cbn in Hturn. rewrite Hturn in Hc.
      assert (Hin' : In m (moves s)) by exact (SaturationA.sim_theirs K Hb HbK Hb1 n s t m HR Hturn Ews Eh Eb Hin).
      rewrite Checker.all_moves_forallb, forallb_forall in Hc. specialize (Hc m Hin').
      eapply good_next_sym; eauto.
Qed.

Theorem good_safe_sym : safe_set PA (up PA (symc good)).
Proof. exact (safe_set_up_sym PA good good_step_sym). Qed.

Theorem cert_safe_sym : forall n s t c b, RA n s t -> (1 <= t.(sideB).(life))%nat ->
  lookup (key s) = Some (c, b) -> blife t <= c + b * Z.of_nat n -> safe PA t.
Proof.
  intros n s t c b HR Hl Hk Hv. exists (up PA (symc good)). split; [exact good_safe_sym |].
  exact (good_entry_sym n s t c b HR Hl Hk Hv).
Qed.

End CheckerASym.

(** [SaturationA.certified_opening_a] for such certificates. *)
Theorem certified_opening_a_sym : forall K Hb ott tt lookup hint c b,
  (Hb < K)%nat -> (1 <= Hb)%nat ->
  (forall s c b, lookup s = Some (c, b) ->
     exists d e M fuel (sw : bool), (if sw then swapA s else s) = bump PA d e /\
       check_node K Hb ott tt lookup hint fuel true (entry M e) c b O = true) ->
  lookup (key Hb tt (init PA)) = Some (c, b) -> 20 <= c -> safe PA (init PA).
Proof.
  intros K Hb ott tt lookup hint c b HbK Hb1 Hok Hk Hc.
  apply (cert_safe_sym K Hb ott tt HbK Hb1 lookup hint Hok 0 (init PA) (init PA) c b (RA_init K Hb PA)).
  - cbn. lia.
  - exact Hk.
  - unfold blife. cbn. lia.
Qed.
