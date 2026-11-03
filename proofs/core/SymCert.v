(** * Sorting A's Walkers in the certificate checkers

    [Sym.swapA] commutes with the abstractions of [Checker] ([key],
    [entry]) and [CheckerA] ([norm], [key], [entry]) and keeps their
    relations [R] and [RA] ([R_swapA], [RA_swapA]); so a certificate state
    abstracting a real state still does after [normA], against the real
    state with its Walkers in the same order ([R_normA], [RA_normA]).

    With these, [Checker.cert_safe] and [WinCert.cert_wins] hold for
    certificates whose [lookup] may answer for a position with the entry of
    the position with A's Walkers swapped ([cert_safe_sym],
    [cert_wins_sym], and the openings [certified_opening_sym],
    [certified_win_opening_sym]); [SymCertA] does the same for
    [CheckerA]. *)

From Stdlib Require Import List Bool Arith Lia Permutation.
Import ListNotations.
From TCB.Spec Require Import Model Game.
From TCB.Proofs Require Import GameFacts Mono Checker Saturation WinCert Sym.
From TCB.Proofs Require CheckerA.

Lemma is_turn_start_swapA : forall s, is_turn_start (swapA s) = is_turn_start s.
Proof. intros s. unfold is_turn_start. rewrite pend_swapA, active_swapA. reflexivity. Qed.

(** *** [Checker] (B-safety and B-wins certificates) *)

Lemma key_swapA : forall H tt s, Checker.key H tt (swapA s) = swapA (Checker.key H tt s).
Proof.
  intros H tt [act ft [] [] c pd]. unfold swapA, Checker.key, sw_side, set_bf, set_gy_w, set_life.
  st_cbn. rewrite length_map. dle2; st_cbn; rewrite ?map_swap01; reflexivity.
Qed.

Lemma entry_swapA : forall s v, Checker.entry (swapA s) v = swapA (Checker.entry s v).
Proof.
  intros [act ft [] [] c pd] v. unfold swapA, Checker.entry, map_side, get_side, set_side, set_life.
  st_cbn. dle2; reflexivity.
Qed.

Lemma R_swapA : forall H s t, Checker.R H s t -> Checker.R H (swapA s) (swapA t).
Proof.
  intros H [act ft a b c pd] [act' ft' a' b' c' pd'] HR.
  pose proof HR as (E1 & E2 & E3 & E4 & Hn & HA & HB).
  cbn [Model.active Model.first_turn Model.sideA Model.sideB Model.cmb Model.pend] in *. subst act' ft' c' pd'.
  pose proof HA as (a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & a9 & a10 & a11 & a12 & a13).
  unfold swapA. cbn [Model.active Model.first_turn Model.sideA Model.sideB Model.cmb Model.pend].
  rewrite <- (Forall2_length a11). destruct (2 <=? length a.(bf)); [| exact HR].
  unfold Checker.R. cbn [Model.active Model.first_turn Model.sideA Model.sideB Model.cmb Model.pend].
  repeat (split; [reflexivity |]). split; [exact Hn |]. split; [| exact HB].
  destruct a, a'; unfold sw_side, set_bf, Checker.sideA_rel in *. cbn in *.
  repeat split; auto. apply Forall2_swap01. exact a11.
Qed.

(** A certificate state [s] that abstracts a real state [t] still does after
    sorting, against [t] with its Walkers in the same order as [s]'s. *)
Theorem R_normA : forall H s t, Checker.R H s t -> exists t', Sym t t' /\ Checker.R H (normA s) t'.
Proof.
  intros H s t HR. unfold normA. destruct (unsorted _).
  - exists (swapA t). split; [apply Sym_swapA | apply R_swapA; exact HR].
  - exists t. split; [left; reflexivity | exact HR].
Qed.

(** *** [CheckerA] (A-safety certificates) *)

Lemma normA_swapA : forall Hb tt s, CheckerA.norm Hb tt (swapA s) = swapA (CheckerA.norm Hb tt s).
Proof.
  intros Hb tt [act ft [] [] c pd]. unfold swapA, CheckerA.norm, CheckerA.cut_a, sw_side, set_bf, set_thop_u, set_thop_t.
  st_cbn. dle2; reflexivity.
Qed.

Lemma keyA_swapA : forall Hb tt s, CheckerA.key Hb tt (swapA s) = swapA (CheckerA.key Hb tt s).
Proof.
  intros Hb tt [act ft [] [] c pd]. unfold swapA, CheckerA.key, CheckerA.norm, CheckerA.cut_a, sw_side,
    set_bf, set_thop_u, set_thop_t, set_gy_w, set_life.
  st_cbn. dle2; reflexivity.
Qed.

Lemma entryA_swapA : forall m s, CheckerA.entry m (swapA s) = swapA (CheckerA.entry m s).
Proof.
  intros m [act ft [] [] c pd]. unfold swapA, CheckerA.entry, map_side, get_side, set_side, set_life.
  st_cbn. dle2; reflexivity.
Qed.

Lemma RA_swapA : forall K Hb n s t, CheckerA.RA K Hb n s t -> CheckerA.RA K Hb n (swapA s) (swapA t).
Proof.
  intros K Hb n [act ft a b c pd] [act' ft' a' b' c' pd'] HR.
  pose proof HR as (E1 & E2 & E3 & E4 & Hn & HA & HB & Hd).
  cbn [Model.active Model.first_turn Model.sideA Model.sideB Model.cmb Model.pend] in *. subst act' ft' c' pd'.
  pose proof HA as (a1 & a2 & a3 & a4 & a5 & a6 & a7 & a8 & a9 & a10 & a11 & a12 & a13 & a14 & a15).
  unfold swapA. cbn [Model.active Model.first_turn Model.sideA Model.sideB Model.cmb Model.pend].
  rewrite <- (Forall2_length a11). destruct (2 <=? length a.(bf)); [| exact HR].
  unfold CheckerA.RA. cbn [Model.active Model.first_turn Model.sideA Model.sideB Model.cmb Model.pend].
  repeat (split; [reflexivity |]). split; [exact Hn |]. split; [| split; [exact HB |]].
  - destruct a, a'; unfold sw_side, set_bf, CheckerA.sideA_rel in *. cbn in *.
    repeat split; auto.
    + apply Forall2_swap01. exact a11.
    + intros Hf. apply a12. apply Forall_swap01. exact Hf.
    + unfold CheckerA.bigs in *. rewrite (Permutation_length (filter_perm _ _ _ (perm_swap01 _))). exact a13.
  - destruct act; cbn; [| exact Hd].
    apply FinFun.Injective_map_NoDup; [exact swi_inj | exact Hd].
Qed.

Theorem RA_normA : forall K Hb n s t, CheckerA.RA K Hb n s t ->
  exists t', Sym t t' /\ CheckerA.RA K Hb n (normA s) t'.
Proof.
  intros K Hb n s t HR. unfold normA. destruct (unsorted _).
  - exists (swapA t). split; [apply Sym_swapA | apply RA_swapA; exact HR].
  - exists t. split; [left; reflexivity | exact HR].
Qed.

(** ** Certificates that store one order of A's Walkers

    The checkers' soundness theorems again, for a [lookup] that may answer
    for a position with the entry of the position with A's two Walkers
    swapped ([sw = true]), e.g. a table of [normA]-sorted keys looked up
    with [lookup s = table (normA s)]. The checkers themselves are
    unchanged. *)

Section CheckerSym.

Variables H ott tt : nat.
Variable lookup : state -> option nat.
Variable hint : state -> move -> bool.

Notation good := (Checker.good H ott tt lookup hint).

Hypothesis cert_ok : forall s v, lookup s = Some v ->
  exists d fuel (sw : bool),
    check_node H ott tt lookup hint fuel true (entry (bump PA d (if sw then swapA s else s)) v) = true.

Lemma R_sw : forall (sw : bool) d e v t, R H (entry e v) t ->
  R H (entry (bump PA d (if sw then swapA e else e)) v) (bump PA d (if sw then swapA t else t)) /\
  Sym (bump PA d (if sw then swapA t else t)) (bump PA d t).
Proof.
  intros sw d e v t HR. split.
  - rewrite entry_bump. apply R_bump. destruct sw; [rewrite entry_swapA; apply R_swapA |]; exact HR.
  - apply Sym_bump. destruct sw; [apply Sym_swapA' | left; reflexivity].
Qed.

Lemma down_entry : forall e v t, lookup e = Some v -> R H (entry e v) t -> down PA (symc good) t.
Proof.
  intros e v t Hl HR. destruct (cert_ok e v Hl) as (d & fuel & sw & Hf).
  destruct (R_sw sw d e v t HR) as [HR' HS].
  right. exists d. exists (bump PA d (if sw then swapA t else t)). split; [| apply syms_one, HS].
  exists (entry (bump PA d (if sw then swapA e else e)) v), fuel. auto.
Qed.

Lemma good_next_sym : forall s t m f,
  R H s t -> In m (moves s) -> huge_event H s = false ->
  check_node H ott tt lookup hint f false (step s m) = true -> down PA (symc good) (step t m).
Proof.
  intros s t m f HR Hin Hh Hc.
  assert (HR' : R H (step s m) (step t m)).
  { apply Saturation.sim_step; auto. eapply check_winner. exact Hc. }
  destruct (check_below H ott tt lookup hint f (step s m) Hc) as [(_ & _ & v & Hl & Hv) | Hr].
  - apply (down_entry _ v _ Hl). eapply R_trans; [| exact HR']. eapply R_key; eassumption.
  - apply down_self, symc_self. exists (step s m), f. auto.
Qed.

Lemma good_step_sym : forall t, good t -> safe_step PB (down PA (symc good)) t.
Proof.
  intros t (s & [| f] & HR & Hc); [discriminate |]. unfold safe_step.
  pose proof (R_winner _ _ _ HR) as Ew. pose proof (R_to_move _ _ _ HR) as Em.
  cbn [check_node negb andb] in Hc.
  split; [rewrite Ew; cbn [opp]; destruct (winner s) as [[] |]; cbv beta iota in Hc; congruence |].
  destruct (winner s) as [[] |] eqn:Ews; cbv beta iota in Hc.
  - discriminate.
  - split; intros Hn; rewrite Ew in Hn; discriminate.
  - destruct (huge_event H s) eqn:Eh; [discriminate |].
    split.
    + intros _ Hturn. rewrite Em in Hturn. rewrite Hturn in Hc.
      rewrite some_move_existsb in Hc. apply existsb_exists in Hc as (m & Hin & Hm).
      destruct (hint s m); [| discriminate]. destruct (too_many ott (step s m)); [discriminate |].
      exists m. split; [exact (Saturation.sim_mine H s t m HR Hturn Ews Eh Hin) |].
      eapply good_next_sym; eauto.
    + intros _ Hturn m Hin. rewrite Em in Hturn. cbn in Hturn. rewrite Hturn in Hc.
      assert (Hin' : In m (moves s)) by (eapply Saturation.sim_theirs; eauto).
      rewrite all_moves_forallb, forallb_forall in Hc. specialize (Hc m Hin').
      destruct (too_many ott (step s m)); [discriminate |].
      eapply good_next_sym; eauto.
Qed.

Theorem good_safe_sym : safe_set PB (down PA (symc good)).
Proof. exact (safe_set_down_sym PA good good_step_sym). Qed.

Theorem cert_safe_sym : forall s v t, lookup s = Some v -> R H (entry s v) t -> safe PB t.
Proof.
  intros s v t Hl HR. exists (down PA (symc good)). split; [exact good_safe_sym |].
  exact (down_entry s v t Hl HR).
Qed.

End CheckerSym.

(** [Saturation.certified_opening] for such certificates. *)
Theorem certified_opening_sym : forall H ott tt lookup hint p v,
  (forall s v, lookup s = Some v ->
     exists d fuel (sw : bool),
       check_node H ott tt lookup hint fuel true (entry (bump PA d (if sw then swapA s else s)) v) = true) ->
  lookup (key H tt (init p)) = Some v -> v <= 20 -> safe PB (init p).
Proof.
  intros H ott tt lookup hint p v Hok Hl Hv.
  apply (cert_safe_sym H ott tt lookup hint Hok _ v _ Hl).
  apply (R_key H tt (init p) (init p) v (R_init H p)).
  destruct p; exact Hv.
Qed.

(** [WinCert.cert_wins] for such certificates. *)
Theorem cert_wins_sym : forall H ott tt lookup below hint,
  (forall s r v, lookup s r = Some v ->
     exists d fuel (sw : bool),
       check_win H ott tt lookup below hint r fuel true (entry (bump PA d (if sw then swapA s else s)) v) = true) ->
  forall r s v t, lookup s r = Some v -> R H (entry s v) t -> wins PB t.
Proof.
  intros H ott tt lookup below hint Hok r.
  induction r as [r IH] using lt_wf_ind. intros s v t Hl HR.
  destruct (Hok s r v Hl) as (d & fuel & sw & Hf).
  destruct (R_sw H sw d s v t HR) as [HR' HS].
  apply (wins_opp_bump PA d t). apply (wins_sym PB _ _ HS).
  exact (check_win_wins H ott tt lookup below hint r IH fuel true _ _ Hf HR').
Qed.

(** [WinCert.certified_win_opening] for such certificates. *)
Theorem certified_win_opening_sym : forall H ott tt lookup below hint p r v,
  (forall s r v, lookup s r = Some v ->
     exists d fuel (sw : bool),
       check_win H ott tt lookup below hint r fuel true (entry (bump PA d (if sw then swapA s else s)) v) = true) ->
  lookup (key H tt (init p)) r = Some v -> v <= 20 -> wins PB (init p).
Proof.
  intros H ott tt lookup below hint p r v Hok Hl Hv.
  apply (cert_wins_sym H ott tt lookup below hint Hok r _ v _ Hl).
  apply (R_key H tt (init p) (init p) v (R_init H p)).
  destruct p; exact Hv.
Qed.
