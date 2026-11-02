(** * Faster searches for [Checker.check_node] and [WinCert.check_win]

    The B-side counterparts of [MemoA.check_m]: [check_mb] searches the
    turn [Checker.check_node] does and [check_mw] the one
    [WinCert.check_win] does (both with every move of B's allowed:
    [StateEq.hint]), keeping the result of every node they have searched in
    [MemoA]'s memo. They are proved to imply the original checks
    ([check_mb_true], [check_mw_true]); nothing is assumed about [hash].
    B tries its moves in the model's order. *)

From Stdlib Require Import Bool List Arith ZArith Lia.
From Stdlib Require PrimInt63.
Import ListNotations.
From TCB.Spec Require Import Model.
From TCB.Proofs Require Import Checker StateEq MemoA.
From TCB.Proofs Require WinCert.

(** A memo entry for a state alone (no line). *)
Definition sfind (s : state) (es : list mentry) : option bool := efind s 0%Z 0%Z 0 es.

(** A node with a single move is searched without the memo: most nodes
    are, and the memo would cost more there than it saves. *)
Definition forced (ms : list move) : bool := match ms with [_] => true | _ => false end.

Section MemoB.

Variables H ott tt : nat.
Variable hash : state -> PrimInt63.int.

Notation CN := (check_node H ott tt).
Notation CW := (WinCert.check_win H ott tt).

(** The trees whose entries are all real results of [chk]. *)
Definition tree_okB (chk : nat -> bool -> state -> bool) (t : mtree) : Prop :=
  forall e, In e (elements t) -> me_c e = 0%Z /\ me_b e = 0%Z /\ me_lo e = 0 /\
    (me_r e = true -> exists f, chk f true (me_s e) = true).

Lemma sfind_ok : forall chk t s r, tree_okB chk t -> sfind s (tfind (hash s) t) = Some r -> r = true ->
  exists f, chk f true s = true.
Proof.
  intros chk t s r Ht Hf ->. destruct (efind_spec _ _ _ _ _ _ Hf) as (e & He & ->).
  destruct (Ht _ (tfind_incl _ _ _ He)) as (_ & _ & _ & Hr). exact (Hr eq_refl).
Qed.

Lemma tadd_okB : forall chk t s r, tree_okB chk t -> (r = true -> exists f, chk f true s = true) ->
  tree_okB chk (tadd (hash s) (ME s 0%Z 0%Z 0 r) t).
Proof.
  intros chk t s r Ht Hr e He. destruct (tadd_elements _ _ _ _ He) as [-> | He']; [| exact (Ht e He')].
  cbn. auto.
Qed.

(** ** B's safety ([Checker.check_node]) *)

Section Safe.

Variable lookup : state -> option nat.

Fixpoint check_mb (fuel : nat) (root : bool) (s : state) (t : mtree) : bool * mtree :=
  match fuel with
  | O => (false, t)
  | S f =>
      match winner s with
      | Some PB => (true, t)
      | Some PA => (false, t)
      | None =>
          if (if root then false else is_turn_start s) then
            (match lookup (key H tt s) with Some v => v <=? s.(sideB).(life) | None => false end, t)
          else if huge_event H s then (false, t)
          else
            let g m t := let s' := step s m in if too_many ott s' then (false, t) else check_mb f false s' t in
            let ms := moves s in
            let search t := match to_move s with PB => any_m g ms t | PA => all_m g ms t end in
            if forced ms then search t
            else
              let h := hash s in
              match sfind s (tfind h t) with
              | Some r => (r, t)
              | None => let (r, t) := search t in (r, tadd h (ME s 0%Z 0%Z 0 r) t)
              end
      end
  end.

Notation CNl := (CN lookup hint).

Lemma CNl_S : forall f root s, CNl (S f) root s =
  match winner s with
  | Some PB => true
  | Some PA => false
  | None =>
      if negb root && is_turn_start s then
        match lookup (key H tt s) with Some v => v <=? s.(sideB).(life) | None => false end
      else if huge_event H s then false
      else
        let next m := let s' := step s m in if too_many ott s' then false else CNl f false s' in
        match to_move s with
        | PB => some_move (fun m => if hint s m then next m else false) (moves s)
        | PA => all_moves next (moves s)
        end
  end.
Proof. reflexivity. Qed.

Lemma CNl_mono_S : forall f root s, CNl f root s = true -> CNl (S f) root s = true.
Proof.
  induction f as [| f IH]; intros root s Hc; [discriminate |].
  rewrite CNl_S in Hc |- *.
  destruct (winner s) as [[] |]; [exact Hc | exact Hc |].
  destruct (negb root && is_turn_start s); [exact Hc |].
  destruct (huge_event H s); [exact Hc |]. cbv zeta in *.
  assert (Hn : forall m, (if too_many ott (step s m) then false else CNl f false (step s m)) = true ->
                         (if too_many ott (step s m) then false else CNl (S f) false (step s m)) = true)
    by (intros m; destruct (too_many ott (step s m)); auto).
  destruct (to_move s).
  - revert Hc. apply all_moves_mono. exact Hn.
  - revert Hc. apply some_move_mono. intros m. destruct (hint s m); auto.
Qed.

Lemma CNl_mono : forall f f' root s, f <= f' -> CNl f root s = true -> CNl f' root s = true.
Proof. intros f f' root s Hle. induction Hle; auto. intros Hc. apply CNl_mono_S. auto. Qed.

Lemma CNl_root : forall f s, is_turn_start s = false -> CNl f true s = CNl f false s.
Proof. intros [| f] s Ht; [reflexivity |]. rewrite !CNl_S, Ht. reflexivity. Qed.

Theorem check_mb_sound : forall f root s t r t', tree_okB CNl t ->
  check_mb f root s t = (r, t') -> tree_okB CNl t' /\ (r = true -> exists f', CNl f' root s = true).
Proof.
  induction f as [| f IH]; intros root s t r t' Ht Hc; cbn [check_mb] in Hc.
  { injection Hc as <- <-. split; [exact Ht | discriminate]. }
  destruct (winner s) as [[] |] eqn:Ew.
  { injection Hc as <- <-. split; [exact Ht | discriminate]. }
  { injection Hc as <- <-. split; [exact Ht |]. intros _. exists 1. rewrite CNl_S, Ew. reflexivity. }
  destruct (if root then false else is_turn_start s) eqn:Er.
  { injection Hc as <- <-. split; [exact Ht |]. intros Hr. exists (S f). rewrite CNl_S, Ew.
    replace (negb root && is_turn_start s) with true by (destruct root; [discriminate | exact (eq_sym Er)]).
    exact Hr. }
  assert (Hts : root = true \/ is_turn_start s = false) by (destruct root; auto).
  assert (Hroot : forall f', CNl f' true s = true -> CNl f' root s = true).
  { intros f' Hf. destruct Hts as [-> | Hts]; [exact Hf |]. destruct root; [exact Hf |]. rewrite <- CNl_root; auto. }
  assert (Hroot' : forall f', CNl f' root s = true -> CNl f' true s = true).
  { intros f' Hf. destruct Hts as [-> | Hts]; [exact Hf |]. destruct root; [exact Hf |]. rewrite CNl_root; auto. }
  destruct (huge_event H s) eqn:Eh.
  { injection Hc as <- <-. split; [exact Ht | discriminate]. }
  set (g := fun m t => let s' := step s m in if too_many ott s' then (false, t) else check_mb f false s' t) in Hc.
  set (Q := fun m => exists f', (if too_many ott (step s m) then false else CNl f' false (step s m)) = true).
  assert (Hg : forall x t0 r0 t0', tree_okB CNl t0 -> g x t0 = (r0, t0') -> tree_okB CNl t0' /\ (r0 = true -> Q x)).
  { intros x t0 r0 t0' Ht0 E. unfold g in E. cbv zeta in E. unfold Q.
    destruct (too_many ott (step s x)).
    - injection E as <- <-. split; [exact Ht0 | discriminate].
    - exact (IH false (step s x) t0 r0 t0' Ht0 E). }
  assert (Hnode : forall f', (match to_move s with
      | PB => some_move (fun m => if hint s m then
                (if too_many ott (step s m) then false else CNl f' false (step s m)) else false) (moves s)
      | PA => all_moves (fun m => if too_many ott (step s m) then false else CNl f' false (step s m)) (moves s)
      end) = true -> CNl (S f') root s = true).
  { intros f' Hf. rewrite CNl_S, Ew.
    replace (negb root && is_turn_start s) with false by (destruct root; [reflexivity | exact (eq_sym Er)]).
    rewrite Eh. exact Hf. }
  assert (Hsearch : forall t0 r1 t1, tree_okB CNl t0 ->
    (match to_move s with PB => any_m g (moves s) t0 | PA => all_m g (moves s) t0 end) = (r1, t1) ->
    tree_okB CNl t1 /\ (r1 = true -> exists f', CNl f' root s = true)).
  { intros t0 r1 t1 Ht0 E1. destruct (to_move s).
    - destruct (all_m_spec (tree_okB CNl) g Q _ t0 r1 t1 (fun x t0 r0 t0' _ => Hg x t0 r0 t0') Ht0 E1) as [Ht1 Hr].
      split; [exact Ht1 |]. intros E.
      destruct (uniform_fuel (fun f' m => (if too_many ott (step s m) then false else CNl f' false (step s m)) = true)
                  (moves s)) as [f' Hf]; [| exact (Hr E) |].
      + intros f1 f2 x Hle. destruct (too_many ott (step s x)); [auto |]. apply CNl_mono. exact Hle.
      + exists (S f'). apply Hnode. rewrite all_moves_forallb. apply forallb_forall. exact Hf.
    - destruct (any_m_spec (tree_okB CNl) g Q _ t0 r1 t1 (fun x t0 r0 t0' _ => Hg x t0 r0 t0') Ht0 E1) as [Ht1 Hr].
      split; [exact Ht1 |]. intros E. destruct (Hr E) as (x & Hx & f' & Hf). exists (S f'). apply Hnode.
      rewrite some_move_existsb. apply existsb_exists. exists x. split; [exact Hx | exact Hf]. }
  destruct (forced (moves s)).
  { exact (Hsearch t r t' Ht Hc). }
  destruct (sfind s (tfind (hash s) t)) as [r0 |] eqn:Ef.
  { injection Hc as <- <-. split; [exact Ht |]. intros E.
    destruct (sfind_ok _ _ _ _ Ht Ef E) as [f' Hf]. exists f'. apply Hroot. exact Hf. }
  destruct (match to_move s with PB => any_m g (moves s) t | PA => all_m g (moves s) t end) as [r1 t1] eqn:E1.
  injection Hc as <- <-.
  destruct (Hsearch t r1 t1 Ht E1) as [Ht1 Hres]. split; [| exact Hres].
  apply tadd_okB; [exact Ht1 |]. intros E. destruct (Hres E) as [f' Hf]. exists f'. apply Hroot'. exact Hf.
Qed.

Corollary check_mb_true : forall f s, fst (check_mb f true s MLeaf) = true -> exists f', CNl f' true s = true.
Proof.
  intros f s Hc. destruct (check_mb f true s MLeaf) as [r t] eqn:E. cbn in Hc. subst r.
  apply (check_mb_sound f true s MLeaf true t); [intros e [] | exact E | reflexivity].
Qed.

End Safe.

(** ** B's wins ([WinCert.check_win]) *)

Section Win.

Variable lookup : state -> nat -> option nat.
Variable below : state -> nat -> option nat.
Variable r : nat.

Fixpoint check_mw (fuel : nat) (root : bool) (s : state) (t : mtree) : bool * mtree :=
  match fuel with
  | O => (false, t)
  | S f =>
      match winner s with
      | Some PB => (true, t)
      | Some PA => (false, t)
      | None =>
          if (if root then false else is_turn_start s) then
            (match below (key H tt s) r with
             | Some r' =>
                 if r' <? r then
                   match lookup (key H tt s) r' with Some v => v <=? s.(sideB).(life) | None => false end
                 else false
             | None => false
             end, t)
          else if huge_event H s then (false, t)
          else
            let g m t := let s' := step s m in if too_many ott s' then (false, t) else check_mw f false s' t in
            let ms := moves s in
            let search t :=
              match to_move s with
              | PB => any_m g ms t
              | PA => match ms with [] => (false, t) | ms => all_m g ms t end
              end in
            if forced ms then search t
            else
              let h := hash s in
              match sfind s (tfind h t) with
              | Some x => (x, t)
              | None => let (x, t) := search t in (x, tadd h (ME s 0%Z 0%Z 0 x) t)
              end
      end
  end.

Notation CWl := (fun f => CW lookup below hint r f).

Lemma CWl_S : forall f root s, CWl (S f) root s =
  match winner s with
  | Some PB => true
  | Some PA => false
  | None =>
      if negb root && is_turn_start s then
        match below (key H tt s) r with
        | Some r' =>
            if r' <? r then
              match lookup (key H tt s) r' with Some v => v <=? s.(sideB).(life) | None => false end
            else false
        | None => false
        end
      else if huge_event H s then false
      else
        let next m := let s' := step s m in if too_many ott s' then false else CWl f false s' in
        match to_move s with
        | PB => some_move (fun m => if hint s m then next m else false) (moves s)
        | PA => match moves s with [] => false | ms => all_moves next ms end
        end
  end.
Proof. reflexivity. Qed.

Lemma CWl_mono_S : forall f root s, CWl f root s = true -> CWl (S f) root s = true.
Proof.
  induction f as [| f IH]; intros root s Hc; [discriminate |].
  rewrite CWl_S in Hc |- *.
  destruct (winner s) as [[] |]; [exact Hc | exact Hc |].
  destruct (negb root && is_turn_start s); [exact Hc |].
  destruct (huge_event H s); [exact Hc |]. cbv zeta in *.
  assert (Hn : forall m, (if too_many ott (step s m) then false else CWl f false (step s m)) = true ->
                         (if too_many ott (step s m) then false else CWl (S f) false (step s m)) = true)
    by (intros m; destruct (too_many ott (step s m)); auto).
  destruct (to_move s).
  - destruct (moves s) as [| m0 ms]; [exact Hc |]. revert Hc. apply all_moves_mono. exact Hn.
  - revert Hc. apply some_move_mono. intros m. destruct (hint s m); auto.
Qed.

Lemma CWl_mono : forall f f' root s, f <= f' -> CWl f root s = true -> CWl f' root s = true.
Proof. intros f f' root s Hle. induction Hle; auto. intros Hc. apply CWl_mono_S. auto. Qed.

Lemma CWl_root : forall f s, is_turn_start s = false -> CWl f true s = CWl f false s.
Proof. intros [| f] s Ht; [reflexivity |]. rewrite !CWl_S, Ht. reflexivity. Qed.

Theorem check_mw_sound : forall f root s t x t', tree_okB CWl t ->
  check_mw f root s t = (x, t') -> tree_okB CWl t' /\ (x = true -> exists f', CWl f' root s = true).
Proof.
  induction f as [| f IH]; intros root s t x t' Ht Hc; cbn [check_mw] in Hc.
  { injection Hc as <- <-. split; [exact Ht | discriminate]. }
  destruct (winner s) as [[] |] eqn:Ew.
  { injection Hc as <- <-. split; [exact Ht | discriminate]. }
  { injection Hc as <- <-. split; [exact Ht |]. intros _. exists 1. rewrite CWl_S, Ew. reflexivity. }
  destruct (if root then false else is_turn_start s) eqn:Er.
  { injection Hc as <- <-. split; [exact Ht |]. intros Hr. exists (S f). rewrite CWl_S, Ew.
    replace (negb root && is_turn_start s) with true by (destruct root; [discriminate | exact (eq_sym Er)]).
    exact Hr. }
  assert (Hts : root = true \/ is_turn_start s = false) by (destruct root; auto).
  assert (Hroot : forall f', CWl f' true s = true -> CWl f' root s = true).
  { intros f' Hf. destruct Hts as [-> | Hts]; [exact Hf |]. destruct root; [exact Hf |]. rewrite <- CWl_root; auto. }
  assert (Hroot' : forall f', CWl f' root s = true -> CWl f' true s = true).
  { intros f' Hf. destruct Hts as [-> | Hts]; [exact Hf |]. destruct root; [exact Hf |]. rewrite CWl_root; auto. }
  destruct (huge_event H s) eqn:Eh.
  { injection Hc as <- <-. split; [exact Ht | discriminate]. }
  set (g := fun m t => let s' := step s m in if too_many ott s' then (false, t) else check_mw f false s' t) in Hc.
  set (Q := fun m => exists f', (if too_many ott (step s m) then false else CWl f' false (step s m)) = true).
  assert (Hg : forall y t0 r0 t0', tree_okB CWl t0 -> g y t0 = (r0, t0') -> tree_okB CWl t0' /\ (r0 = true -> Q y)).
  { intros y t0 r0 t0' Ht0 E. unfold g in E. cbv zeta in E. unfold Q.
    destruct (too_many ott (step s y)).
    - injection E as <- <-. split; [exact Ht0 | discriminate].
    - exact (IH false (step s y) t0 r0 t0' Ht0 E). }
  assert (Hnode : forall f', (match to_move s with
      | PB => some_move (fun m => if hint s m then
                (if too_many ott (step s m) then false else CWl f' false (step s m)) else false) (moves s)
      | PA => match moves s with
              | [] => false
              | ms => all_moves (fun m => if too_many ott (step s m) then false else CWl f' false (step s m)) ms
              end
      end) = true -> CWl (S f') root s = true).
  { intros f' Hf. rewrite CWl_S, Ew.
    replace (negb root && is_turn_start s) with false by (destruct root; [reflexivity | exact (eq_sym Er)]).
    rewrite Eh. exact Hf. }
  assert (Hsearch : forall t0 x1 t1, tree_okB CWl t0 ->
    (match to_move s with
     | PB => any_m g (moves s) t0
     | PA => match moves s with [] => (false, t0) | _ :: _ => all_m g (moves s) t0 end
     end) = (x1, t1) ->
    tree_okB CWl t1 /\ (x1 = true -> exists f', CWl f' root s = true)).
  { intros t0 x1 t1 Ht0 E1. destruct (to_move s).
    - destruct (moves s) as [| m0 ms] eqn:Ems.
      { injection E1 as <- <-. split; [exact Ht0 | discriminate]. }
      destruct (all_m_spec (tree_okB CWl) g Q (m0 :: ms) t0 x1 t1 (fun y t0 r0 t0' _ => Hg y t0 r0 t0') Ht0 E1)
        as [Ht1 Hr].
      split; [exact Ht1 |]. intros E.
      destruct (uniform_fuel (fun f' m => (if too_many ott (step s m) then false else CWl f' false (step s m)) = true)
                  (m0 :: ms)) as [f' Hf]; [| exact (Hr E) |].
      + intros f1 f2 y Hle. destruct (too_many ott (step s y)); [auto |]. apply CWl_mono. exact Hle.
      + exists (S f'). apply Hnode. cbv iota. rewrite all_moves_forallb. apply forallb_forall. exact Hf.
    - destruct (any_m_spec (tree_okB CWl) g Q _ t0 x1 t1 (fun y t0 r0 t0' _ => Hg y t0 r0 t0') Ht0 E1) as [Ht1 Hr].
      split; [exact Ht1 |]. intros E. destruct (Hr E) as (y & Hy & f' & Hf). exists (S f'). apply Hnode.
      rewrite some_move_existsb. apply existsb_exists. exists y. split; [exact Hy | exact Hf]. }
  destruct (forced (moves s)).
  { exact (Hsearch t x t' Ht Hc). }
  destruct (sfind s (tfind (hash s) t)) as [r0 |] eqn:Ef.
  { injection Hc as <- <-. split; [exact Ht |]. intros E.
    destruct (sfind_ok _ _ _ _ Ht Ef E) as [f' Hf]. exists f'. apply Hroot. exact Hf. }
  destruct (match to_move s with
            | PB => any_m g (moves s) t
            | PA => match moves s with [] => (false, t) | _ :: _ => all_m g (moves s) t end
            end) as [x1 t1] eqn:E1.
  injection Hc as <- <-.
  destruct (Hsearch t x1 t1 Ht E1) as [Ht1 Hres]. split; [| exact Hres].
  apply tadd_okB; [exact Ht1 |]. intros E. destruct (Hres E) as [f' Hf]. exists f'. apply Hroot'. exact Hf.
Qed.

Corollary check_mw_true : forall f s, fst (check_mw f true s MLeaf) = true -> exists f', CW lookup below hint r f' true s = true.
Proof.
  intros f s Hc. destruct (check_mw f true s MLeaf) as [x t] eqn:E. cbn in Hc. subst x.
  apply (check_mw_sound f true s MLeaf true t); [intros e [] | exact E | reflexivity].
Qed.

End Win.

End MemoB.
