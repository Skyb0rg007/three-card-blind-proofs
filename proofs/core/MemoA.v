(** * A faster search for [CheckerA.check_node]

    [check_m] searches the same turn as [CheckerA.check_node] (with every
    move allowed: [Packed.hint]), and is proved to imply it
    ([check_m_sound]), so a table checked with [check_m] satisfies
    [CheckerA.cert_safe]'s hypothesis. Two things make it faster:

    - **A memo.** Within a turn the same node [(s, c, b, lo)] is often
      reached along different paths (the same pumps in a different order,
      say). [check_m] keeps the result of every node it has searched, in a
      binary tree indexed by [hash s], and answers a node it has seen from
      there. Nothing is assumed about [hash]: a stored node is used only if
      it is equal to the node asked for ([state_eqb]), so a bad hash only
      makes the memo miss.
    - **A's attacks, most aggressive first.** A needs one move that works,
      and when A's first move fails, its whole subtree has been searched in
      vain. The first attack ([Model.attack_moves] lists the empty attack
      first) is the one that fails most often, so [check_m] tries A's
      attacks in reverse. Any order is sound: A only needs one move.
    - **A hinted move first.** [ahint s h] (from [s] and its hash [h]) names
      a move for A to try before the others ([hfirst]); [PackedA] reads it
      from a table the exporter fills with the moves that work where the
      first one fails. Nothing is assumed about [ahint]: every move is
      still tried, so a wrong hint costs time only. *)

From Stdlib Require Import Bool List Arith ZArith Lia.
From Stdlib Require PrimInt63.
Import ListNotations.
From TCB.Spec Require Import Model.
From TCB.Proofs Require Import Checker StateEq.
From TCB.Proofs Require CheckerA.

(** The order A tries its moves in. *)
Definition a_order (s : state) (ms : list move) : list move :=
  match s.(pend) with ChooseAttack => rev ms | _ => ms end.

Lemma a_order_in : forall s ms m, In m (a_order s ms) -> In m ms.
Proof. intros s ms m. unfold a_order. destruct (pend s); auto. apply in_rev. Qed.

(** A hinted move first: [i] is 0 for no hint, or 1 + the index in [ms]
    of the move to try first. The hinted move is tried again in its place
    if it fails (the memo usually answers it then). Any hint is sound: the
    protagonist only needs one move that works, and every move of the list
    is still tried. *)
Definition hfirst (i : nat) (ms : list move) : list move :=
  match i with
  | O => ms
  | S k => match nth_error ms k with Some m => m :: ms | None => ms end
  end.

Lemma hfirst_in : forall i ms m, In m (hfirst i ms) -> In m ms.
Proof.
  intros [| k] ms m; cbn; [auto |].
  destruct (nth_error ms k) as [x |] eqn:E; [| auto].
  intros [<- | H]; [exact (nth_error_In _ _ E) | exact H].
Qed.

(** ** The memo *)

(** A node and its result. *)
Record mentry := ME { me_s : state; me_c : Z; me_b : Z; me_lo : nat; me_r : bool }.

(** A binary search tree on the hashes; each node holds the entries of one
    hash. It isn't balanced: the hashes are spread well enough. *)
Inductive mtree := MLeaf | MNode (l : mtree) (h : PrimInt63.int) (es : list mentry) (r : mtree).

Fixpoint tfind (h : PrimInt63.int) (t : mtree) : list mentry :=
  match t with
  | MLeaf => []
  | MNode l k es r => if PrimInt63.ltb h k then tfind h l else if PrimInt63.ltb k h then tfind h r else es
  end.

Fixpoint tadd (h : PrimInt63.int) (e : mentry) (t : mtree) : mtree :=
  match t with
  | MLeaf => MNode MLeaf h [e] MLeaf
  | MNode l k es r =>
      if PrimInt63.ltb h k then MNode (tadd h e l) k es r
      else if PrimInt63.ltb k h then MNode l k es (tadd h e r)
      else MNode l k (e :: es) r
  end.

Fixpoint elements (t : mtree) : list mentry :=
  match t with MLeaf => [] | MNode l _ es r => elements l ++ es ++ elements r end.

(** The result stored for exactly this node, if any. *)
Fixpoint efind (s : state) (c b : Z) (lo : nat) (es : list mentry) : option bool :=
  match es with
  | [] => None
  | e :: es =>
      if Z.eqb e.(me_c) c then
        if Z.eqb e.(me_b) b then
          if Nat.eqb e.(me_lo) lo then
            if state_eqb e.(me_s) s then Some e.(me_r) else efind s c b lo es
          else efind s c b lo es
        else efind s c b lo es
      else efind s c b lo es
  end.

Lemma tfind_incl : forall h t e, In e (tfind h t) -> In e (elements t).
Proof.
  intros h t. induction t as [| l IHl k es r IHr]; intros e He; [destruct He |]. cbn in *.
  apply in_or_app. destruct (PrimInt63.ltb h k); [left; auto |].
  destruct (PrimInt63.ltb k h); right; apply in_or_app; auto.
Qed.

Lemma tadd_elements : forall h e t x, In x (elements (tadd h e t)) -> x = e \/ In x (elements t).
Proof.
  intros h e t. induction t as [| l IHl k es r IHr]; intros x Hx; cbn in *.
  - destruct Hx as [-> | []]; auto.
  - destruct (PrimInt63.ltb h k); [| destruct (PrimInt63.ltb k h)]; cbn [elements] in Hx;
      rewrite !in_app_iff in Hx |- *.
    + destruct Hx as [Hx | Hx]; [destruct (IHl x Hx) |]; tauto.
    + destruct Hx as [Hx | [Hx | Hx]]; [| | destruct (IHr x Hx)]; tauto.
    + destruct Hx as [Hx | [[<- | Hx] | Hx]]; tauto.
Qed.

Lemma efind_spec : forall s c b lo es r, efind s c b lo es = Some r ->
  exists e, In e es /\ e = ME s c b lo r.
Proof.
  intros s c b lo es r. induction es as [| e es IH]; intros Hf; [discriminate |]. cbn in Hf.
  destruct (Z.eqb_spec (me_c e) c); [| destruct (IH Hf) as (e' & ? & ?); exists e'; cbn; auto].
  destruct (Z.eqb_spec (me_b e) b); [| destruct (IH Hf) as (e' & ? & ?); exists e'; cbn; auto].
  destruct (Nat.eqb_spec (me_lo e) lo); [| destruct (IH Hf) as (e' & ? & ?); exists e'; cbn; auto].
  destruct (state_eqb (me_s e) s) eqn:Es; [| destruct (IH Hf) as (e' & ? & ?); exists e'; cbn; auto].
  injection Hf as <-. apply state_eqb_eq in Es. exists e. split; [left; reflexivity |].
  destruct e; cbn in *; subst; reflexivity.
Qed.

(** Short-circuiting searches over the moves that thread the memo. *)
Fixpoint any_m (g : move -> mtree -> bool * mtree) (l : list move) (t : mtree) : bool * mtree :=
  match l with
  | [] => (false, t)
  | x :: l => let (r, t) := g x t in if r then (true, t) else any_m g l t
  end.

Fixpoint all_m (g : move -> mtree -> bool * mtree) (l : list move) (t : mtree) : bool * mtree :=
  match l with
  | [] => (true, t)
  | x :: l => let (r, t) := g x t in if r then all_m g l t else (false, t)
  end.

Lemma any_m_spec : forall (inv : mtree -> Prop) (g : move -> mtree -> bool * mtree) (Q : move -> Prop) l t r t',
  (forall x t0 r0 t0', In x l -> inv t0 -> g x t0 = (r0, t0') -> inv t0' /\ (r0 = true -> Q x)) ->
  inv t -> any_m g l t = (r, t') -> inv t' /\ (r = true -> exists x, In x l /\ Q x).
Proof.
  intros inv g Q l. induction l as [| x l IH]; intros t r t' Hg Ht Ha; cbn in Ha.
  - injection Ha as <- <-. split; [exact Ht | discriminate].
  - destruct (g x t) as [r0 t0] eqn:Eg.
    destruct (Hg x t r0 t0 (or_introl eq_refl) Ht Eg) as [Ht0 HQ].
    destruct r0.
    + injection Ha as <- <-. split; [exact Ht0 |]. intros _. exists x. split; [left; reflexivity | auto].
    + destruct (IH t0 r t' (fun x' t1 r1 t1' Hx => Hg x' t1 r1 t1' (or_intror Hx)) Ht0 Ha) as [Ht' Hr].
      split; [exact Ht' |]. intros E. destruct (Hr E) as (x' & Hx & Hq). exists x'. split; [right |]; auto.
Qed.

Lemma all_m_spec : forall (inv : mtree -> Prop) (g : move -> mtree -> bool * mtree) (Q : move -> Prop) l t r t',
  (forall x t0 r0 t0', In x l -> inv t0 -> g x t0 = (r0, t0') -> inv t0' /\ (r0 = true -> Q x)) ->
  inv t -> all_m g l t = (r, t') -> inv t' /\ (r = true -> forall x, In x l -> Q x).
Proof.
  intros inv g Q l. induction l as [| x l IH]; intros t r t' Hg Ht Ha; cbn in Ha.
  - injection Ha as <- <-. split; [exact Ht | intros _ x []].
  - destruct (g x t) as [r0 t0] eqn:Eg.
    destruct (Hg x t r0 t0 (or_introl eq_refl) Ht Eg) as [Ht0 HQ].
    destruct r0.
    + destruct (IH t0 r t' (fun x' t1 r1 t1' Hx => Hg x' t1 r1 t1' (or_intror Hx)) Ht0 Ha) as [Ht' Hr].
      split; [exact Ht' |]. intros E x' [<- | Hx]; auto.
    + injection Ha as <- <-. split; [exact Ht0 | discriminate].
Qed.

(** One fuel for every move of a B node. *)
Lemma uniform_fuel : forall (R : nat -> move -> Prop) l,
  (forall f f' x, f <= f' -> R f x -> R f' x) -> (forall x, In x l -> exists f, R f x) ->
  exists f, forall x, In x l -> R f x.
Proof.
  intros R l Hm. induction l as [| x l IH]; intros Hl; [exists 0; intros _ [] |].
  destruct (Hl x (or_introl eq_refl)) as [f1 H1].
  destruct IH as [f2 H2]; [intros; apply Hl; right; auto |].
  exists (Nat.max f1 f2). intros y [<- | Hy].
  - apply (Hm f1); [lia | exact H1].
  - apply (Hm f2); [lia | auto].
Qed.

Section Memo.

Variables K Hb ott tt : nat.
Variable lookup : state -> option (Z * Z).
Variable hash : state -> PrimInt63.int.
(** The move A tries first at a node, from the node's hash ([hfirst]):
    untrusted, any function is sound. *)
Variable ahint : state -> PrimInt63.int -> nat.

(** [CheckerA.check_node]'s edge, with the recursive call [rec]. [bs],
    [hb] and [hit] are [blife s], [has_big s] and [is_hit s], computed
    once per node. *)
Definition next_m (rec : state -> Z -> Z -> nat -> mtree -> bool * mtree) (s : state) (c b : Z) (lo : nat)
    (bs : Z) (hb hit : bool) (m : move) (t : mtree) : bool * mtree :=
  let pb := CheckerA.is_pump_big K s m in
  let cr := CheckerA.is_create K s m in
  if (if cr then hb else false) then (false, t) else
  let s' := CheckerA.stepA K Hb tt s m in
  if CheckerA.too_many ott s' then (false, t) else
  match winner s' with
  | Some _ => (false, t)
  | None =>
      let c1 := if pb then (c - b)%Z else c in
      let b1 := if cr then 0%Z else b in
      let c2 := (c1 + (CheckerA.blife s' - bs))%Z in
      let b2 := if hit then (b1 - 1)%Z else b1 in
      let lo2 := if pb then S lo else if cr then O else lo in
      if (if (c2 + b2 * Z.of_nat lo2 <=? 0)%Z then (b2 <=? 0)%Z else false) then (true, t)
      else rec s' c2 b2 lo2 t
  end.

(** [CheckerA.check_node] with the memo [t]. *)
Fixpoint check_m (fuel : nat) (root : bool) (s : state) (c b : Z) (lo : nat) (t : mtree) : bool * mtree :=
  match fuel with
  | O => (false, t)
  | S f =>
      match winner s with
      | Some _ => (false, t)
      | None =>
          if (if root then false else is_turn_start s) then
            (match lookup (CheckerA.key Hb tt s) with
             | Some (c', b') =>
                 ((c + b * Z.of_nat lo <=? c' + b' * Z.of_nat lo) && (negb (CheckerA.has_big K s) || (b <=? b')))%Z
             | None => false
             end, t)
          else if (if CheckerA.huge_event Hb s then true else CheckerA.big_event K s) then (false, t)
          else
            let h := hash s in
            match efind s c b lo (tfind h t) with
            | Some r => (r, t)
            | None =>
                let g := next_m (check_m f false) s c b lo (CheckerA.blife s) (CheckerA.has_big K s) (CheckerA.is_hit K s) in
                let (r, t) :=
                  match to_move s with
                  | PA => any_m g (hfirst (ahint s h) (a_order s (moves s))) t
                  | PB => all_m g (moves s) t
                  end in
                (r, tadd h (ME s c b lo r) t)
            end
      end
  end.

(** ** Soundness *)

Notation CN := (CheckerA.check_node K Hb ott tt lookup hint).

(** [CheckerA.check_node]'s edge, with the recursive call [rec]. *)
Definition next_g (rec : state -> Z -> Z -> nat -> bool) (s : state) (c b : Z) (lo : nat) (m : move) : bool :=
  if CheckerA.is_create K s m && CheckerA.has_big K s then false else
  let s' := CheckerA.stepA K Hb tt s m in
  if CheckerA.too_many ott s' then false else
  match winner s' with
  | Some _ => false
  | None =>
      let c1 := if CheckerA.is_pump_big K s m then (c - b)%Z else c in
      let b1 := if CheckerA.is_create K s m then 0%Z else b in
      let c2 := (c1 + (CheckerA.blife s' - CheckerA.blife s))%Z in
      let b2 := if CheckerA.is_hit K s then (b1 - 1)%Z else b1 in
      let lo2 := if CheckerA.is_pump_big K s m then S lo else if CheckerA.is_create K s m then O else lo in
      if (c2 + b2 * Z.of_nat lo2 <=? 0)%Z && (b2 <=? 0)%Z then true
      else rec s' c2 b2 lo2
  end.

Lemma CN_S : forall f root s c b lo, CN (S f) root s c b lo =
  match winner s with
  | Some _ => false
  | None =>
      if negb root && is_turn_start s then
        match lookup (CheckerA.key Hb tt s) with
        | Some (c', b') =>
            ((c + b * Z.of_nat lo <=? c' + b' * Z.of_nat lo) && (negb (CheckerA.has_big K s) || (b <=? b')))%Z
        | None => false
        end
      else if CheckerA.huge_event Hb s || CheckerA.big_event K s then false
      else
        match to_move s with
        | PA => some_move (fun m => if hint s m then next_g (CN f false) s c b lo m else false) (moves s)
        | PB => all_moves (next_g (CN f false) s c b lo) (moves s)
        end
  end.
Proof. reflexivity. Qed.

Lemma next_g_mono : forall (g g' : state -> Z -> Z -> nat -> bool) s c b lo m,
  (forall s' c' b' lo', g s' c' b' lo' = true -> g' s' c' b' lo' = true) ->
  next_g g s c b lo m = true -> next_g g' s c b lo m = true.
Proof.
  intros g g' s c b lo m Hg. unfold next_g.
  destruct (CheckerA.is_create K s m && CheckerA.has_big K s); [auto |].
  destruct (CheckerA.too_many ott (CheckerA.stepA K Hb tt s m)); [auto |].
  destruct (winner (CheckerA.stepA K Hb tt s m)); [auto |]. cbv zeta.
  match goal with |- (if ?x then _ else _) = _ -> _ => destruct x end; auto.
Qed.

Lemma some_move_mono : forall (g g' : move -> bool) l,
  (forall x, g x = true -> g' x = true) -> some_move g l = true -> some_move g' l = true.
Proof.
  intros g g' l Hg. rewrite !some_move_existsb, !existsb_exists. intros (x & Hx & E). eauto.
Qed.

Lemma all_moves_mono : forall (g g' : move -> bool) l,
  (forall x, g x = true -> g' x = true) -> all_moves g l = true -> all_moves g' l = true.
Proof.
  intros g g' l Hg. rewrite !all_moves_forallb, !forallb_forall. auto.
Qed.

Lemma CN_mono_S : forall f root s c b lo, CN f root s c b lo = true -> CN (S f) root s c b lo = true.
Proof.
  induction f as [| f IH]; intros root s c b lo Hc; [discriminate |].
  rewrite CN_S in Hc |- *.
  destruct (winner s); [exact Hc |].
  destruct (negb root && is_turn_start s); [exact Hc |].
  destruct (CheckerA.huge_event Hb s || CheckerA.big_event K s); [exact Hc |].
  assert (Hn : forall m, next_g (CN f false) s c b lo m = true -> next_g (CN (S f) false) s c b lo m = true)
    by (intros m; apply next_g_mono; intros; apply IH; auto).
  destruct (to_move s).
  - revert Hc. apply some_move_mono. intros m. destruct (hint s m); auto.
  - revert Hc. apply all_moves_mono. exact Hn.
Qed.

Lemma CN_mono : forall f f' root s c b lo, f <= f' -> CN f root s c b lo = true -> CN f' root s c b lo = true.
Proof.
  intros f f' root s c b lo Hle. induction Hle as [| f' Hle IH]; auto.
  intros Hc. apply CN_mono_S. auto.
Qed.

Lemma CN_root : forall f s c b lo, is_turn_start s = false -> CN f true s c b lo = CN f false s c b lo.
Proof. intros [| f] s c b lo Ht; [reflexivity |]. rewrite !CN_S, Ht. reflexivity. Qed.

(** An edge of [check_m] either calls [rec] on the child, as [next_g]
    does, or gives a result that doesn't depend on the call. *)
Lemma next_m_spec : forall rec s c b lo m t r t',
  next_m rec s c b lo (CheckerA.blife s) (CheckerA.has_big K s) (CheckerA.is_hit K s) m t = (r, t') ->
  (exists s' c2 b2 lo2, rec s' c2 b2 lo2 t = (r, t') /\ forall g, next_g g s c b lo m = g s' c2 b2 lo2) \/
  (t' = t /\ forall g, next_g g s c b lo m = r).
Proof.
  intros rec s c b lo m t r t'. unfold next_m, next_g. cbv zeta.
  destruct (CheckerA.is_create K s m), (CheckerA.has_big K s); cbn [andb];
    try (intros E; injection E as <- <-; right; auto; fail).
  all: destruct (CheckerA.too_many ott (CheckerA.stepA K Hb tt s m));
    [intros E; injection E as <- <-; right; auto |].
  all: destruct (winner (CheckerA.stepA K Hb tt s m)); [intros E; injection E as <- <-; right; auto |].
  all: match goal with |- (if (if ?x then ?y else false) then _ else _) = _ -> _ =>
         destruct x; [destruct y |]; cbn [andb] end.
  all: first [intros E; injection E as <- <-; right; auto | intros E; left; eauto 6].
Qed.

Definition entry_ok (e : mentry) : Prop :=
  e.(me_r) = true -> exists f, CN f true e.(me_s) e.(me_c) e.(me_b) e.(me_lo) = true.

Definition tree_ok (t : mtree) : Prop := forall e, In e (elements t) -> entry_ok e.

Theorem check_m_sound : forall f root s c b lo t r t', tree_ok t ->
  check_m f root s c b lo t = (r, t') ->
  tree_ok t' /\ (r = true -> exists f', CN f' root s c b lo = true).
Proof.
  induction f as [| f IH]; intros root s c b lo t r t' Ht Hc; cbn [check_m] in Hc.
  { injection Hc as <- <-. split; [exact Ht | discriminate]. }
  destruct (winner s) eqn:Ew.
  { injection Hc as <- <-. split; [exact Ht | discriminate]. }
  destruct (if root then false else is_turn_start s) eqn:Er.
  { injection Hc as <- <-. split; [exact Ht |]. intros Hr. exists (S f). rewrite CN_S, Ew.
    replace (negb root && is_turn_start s) with true by (destruct root; [discriminate | exact (eq_sym Er)]).
    exact Hr. }
  assert (Hts : root = true \/ is_turn_start s = false) by (destruct root; auto).
  assert (Hroot : forall f', CN f' true s c b lo = true -> CN f' root s c b lo = true).
  { intros f' H. destruct Hts as [-> | Hts]; [exact H |]. destruct root; [exact H |]. rewrite <- CN_root; auto. }
  assert (Hroot' : forall f', CN f' root s c b lo = true -> CN f' true s c b lo = true).
  { intros f' H. destruct Hts as [-> | Hts]; [exact H |]. destruct root; [exact H |]. rewrite CN_root; auto. }
  destruct (if CheckerA.huge_event Hb s then true else CheckerA.big_event K s) eqn:Eh.
  { injection Hc as <- <-. split; [exact Ht | discriminate]. }
  set (g := next_m (check_m f false) s c b lo (CheckerA.blife s) (CheckerA.has_big K s) (CheckerA.is_hit K s)) in Hc.
  set (Q := fun m => exists f', next_g (CN f' false) s c b lo m = true).
  assert (Hg : forall x t0 r0 t0', tree_ok t0 -> g x t0 = (r0, t0') -> tree_ok t0' /\ (r0 = true -> Q x)).
  { intros x t0 r0 t0' Ht0 E. destruct (next_m_spec _ _ _ _ _ _ _ _ _ E)
      as [(s' & c2 & b2 & lo2 & Er' & Eg) | (-> & Eg)].
    - destruct (IH false s' c2 b2 lo2 t0 r0 t0' Ht0 Er') as [Ht0' Hr]. split; [exact Ht0' |].
      intros E0. destruct (Hr E0) as [f' Hf]. exists f'. rewrite Eg. exact Hf.
    - split; [exact Ht0 |]. intros ->. exists 0. apply Eg. }
  (* the node, searched: its result implies [CN] *)
  assert (Hnode : forall f', (match to_move s with
      | PA => some_move (fun m => if hint s m then next_g (CN f' false) s c b lo m else false) (moves s)
      | PB => all_moves (next_g (CN f' false) s c b lo) (moves s) end) = true -> CN (S f') root s c b lo = true).
  { intros f' H. rewrite CN_S, Ew.
    replace (negb root && is_turn_start s) with false by (destruct root; [reflexivity | exact (eq_sym Er)]).
    replace (CheckerA.huge_event Hb s || CheckerA.big_event K s) with false
      by (destruct (CheckerA.huge_event Hb s); [discriminate | exact (eq_sym Eh)]).
    exact H. }
  assert (Hsearch : forall t0 r0 t0', tree_ok t0 ->
    (match to_move s with PA => any_m g (hfirst (ahint s (hash s)) (a_order s (moves s))) t0 | PB => all_m g (moves s) t0 end) = (r0, t0') ->
    tree_ok t0' /\ (r0 = true -> exists f', CN f' root s c b lo = true)).
  { intros t0 r0 t0' Ht0 Es. destruct (to_move s).
    - destruct (any_m_spec tree_ok g Q _ t0 r0 t0' (fun x t1 r1 t1' _ => Hg x t1 r1 t1') Ht0 Es) as [Ht1 Hr].
      split; [exact Ht1 |]. intros E. destruct (Hr E) as (x & Hx & f' & Hf). exists (S f'). apply Hnode.
      rewrite some_move_existsb. apply existsb_exists. exists x. split; [exact (a_order_in _ _ _ (hfirst_in _ _ _ Hx)) | exact Hf].
    - destruct (all_m_spec tree_ok g Q _ t0 r0 t0' (fun x t1 r1 t1' _ => Hg x t1 r1 t1') Ht0 Es) as [Ht1 Hr].
      split; [exact Ht1 |]. intros E.
      destruct (uniform_fuel (fun f' m => next_g (CN f' false) s c b lo m = true) (moves s)) as [f' Hf];
        [| exact (Hr E) |].
      + intros f1 f2 x Hle. apply next_g_mono. intros. eapply CN_mono; eauto.
      + exists (S f'). apply Hnode. rewrite all_moves_forallb. apply forallb_forall. exact Hf. }
  assert (Hmemo : forall t0 r0 t0', tree_ok t0 ->
    (let (r1, t1) := (match to_move s with PA => any_m g (hfirst (ahint s (hash s)) (a_order s (moves s))) t0 | PB => all_m g (moves s) t0 end) in
     (r1, tadd (hash s) (ME s c b lo r1) t1)) = (r0, t0') ->
    tree_ok t0' /\ (r0 = true -> exists f', CN f' root s c b lo = true)).
  { intros t0 r0 t0' Ht0 Es.
    destruct (match to_move s with PA => any_m g (hfirst (ahint s (hash s)) (a_order s (moves s))) t0 | PB => all_m g (moves s) t0 end)
      as [r1 t1] eqn:E1.
    injection Es as <- <-. destruct (Hsearch t0 r1 t1 Ht0 E1) as [Ht1 Hres]. split; [| exact Hres].
    intros e He. destruct (tadd_elements _ _ _ _ He) as [-> | He']; [| exact (Ht1 e He')].
    intros E. destruct (Hres E) as [f' Hf]. exists f'. apply Hroot'. exact Hf. }
  destruct (efind s c b lo (tfind (hash s) t)) as [r0 |] eqn:Ef.
  - injection Hc as <- <-. split; [exact Ht |]. intros ->.
    destruct (efind_spec _ _ _ _ _ _ Ef) as (e & He & ->).
    destruct (Ht _ (tfind_incl _ _ _ He) eq_refl) as [f' Hf]. exists f'. apply Hroot. exact Hf.
  - exact (Hmemo t r t' Ht Hc).
Qed.

(** What a table check needs: [check_m] from an empty memo. *)
Corollary check_m_true : forall f s c b lo, fst (check_m f true s c b lo MLeaf) = true ->
  exists f', CN f' true s c b lo = true.
Proof.
  intros f s c b lo H. destruct (check_m f true s c b lo MLeaf) as [r t] eqn:E. cbn in H. subst r.
  apply (check_m_sound f true s c b lo MLeaf true t); [intros e [] | exact E | reflexivity].
Qed.

End Memo.
