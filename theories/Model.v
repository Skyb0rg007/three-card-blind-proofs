(** * The game model

    A direct implementation of RULES.md §3. Section and simplification
    numbers (S1–S12) refer to that document. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.

(** ** Players and cards *)

Inductive player := PA | PB.

Definition opp (p : player) : player :=
  match p with PA => PB | PB => PA end.

Definition player_eqb (p q : player) : bool :=
  match p, q with PA, PA | PB, PB => true | _, _ => false end.

(** City of Traitors is not a card in this model (S1): it is always on the
    battlefield from its controller's first turn. *)
Inductive card := CWalker | CElixir.

Definition card_eq_dec (x y : card) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

(** ** Per-player state (RULES.md §3.1) *)

Record walker := mkWalker {
  counters : nat;
  wtapped : bool;
  sick : bool;  (** not controlled since its controller's most recent turn began *)
}.

(** Thopter summoning sickness never matters: thopters are only created
    during a combat damage step, and their controller's next combat is in
    their controller's next turn, by which time they are no longer sick.
    So thopters are counted only as untapped or tapped (S6). *)
Record side := mkSide {
  life : nat;
  city : bool;        (** City of Traitors is untapped *)
  pool : nat;         (** colorless mana in the pool *)
  hand_w : nat;       (** Walkers in hand *)
  hand_e : bool;      (** Elixir in hand *)
  bf : list walker;   (** Walkers on the battlefield *)
  elixir_bf : bool;   (** Elixir on the battlefield, always untapped (S12) *)
  thop_u : nat;       (** untapped Thopters *)
  thop_t : nat;       (** tapped Thopters *)
  library : list card;
  gy_w : nat;         (** Walkers in the graveyard *)
}.

(** Field updates (Rocq has no record-update syntax). *)
Definition set_life n s :=
  mkSide n s.(city) s.(pool) s.(hand_w) s.(hand_e) s.(bf) s.(elixir_bf) s.(thop_u) s.(thop_t) s.(library) s.(gy_w).
Definition set_city b s :=
  mkSide s.(life) b s.(pool) s.(hand_w) s.(hand_e) s.(bf) s.(elixir_bf) s.(thop_u) s.(thop_t) s.(library) s.(gy_w).
Definition set_pool n s :=
  mkSide s.(life) s.(city) n s.(hand_w) s.(hand_e) s.(bf) s.(elixir_bf) s.(thop_u) s.(thop_t) s.(library) s.(gy_w).
Definition set_hand_w n s :=
  mkSide s.(life) s.(city) s.(pool) n s.(hand_e) s.(bf) s.(elixir_bf) s.(thop_u) s.(thop_t) s.(library) s.(gy_w).
Definition set_hand_e b s :=
  mkSide s.(life) s.(city) s.(pool) s.(hand_w) b s.(bf) s.(elixir_bf) s.(thop_u) s.(thop_t) s.(library) s.(gy_w).
Definition set_bf l s :=
  mkSide s.(life) s.(city) s.(pool) s.(hand_w) s.(hand_e) l s.(elixir_bf) s.(thop_u) s.(thop_t) s.(library) s.(gy_w).
Definition set_elixir_bf b s :=
  mkSide s.(life) s.(city) s.(pool) s.(hand_w) s.(hand_e) s.(bf) b s.(thop_u) s.(thop_t) s.(library) s.(gy_w).
Definition set_thop_u n s :=
  mkSide s.(life) s.(city) s.(pool) s.(hand_w) s.(hand_e) s.(bf) s.(elixir_bf) n s.(thop_t) s.(library) s.(gy_w).
Definition set_thop_t n s :=
  mkSide s.(life) s.(city) s.(pool) s.(hand_w) s.(hand_e) s.(bf) s.(elixir_bf) s.(thop_u) n s.(library) s.(gy_w).
Definition set_library l s :=
  mkSide s.(life) s.(city) s.(pool) s.(hand_w) s.(hand_e) s.(bf) s.(elixir_bf) s.(thop_u) s.(thop_t) l s.(gy_w).
Definition set_gy_w n s :=
  mkSide s.(life) s.(city) s.(pool) s.(hand_w) s.(hand_e) s.(bf) s.(elixir_bf) s.(thop_u) s.(thop_t) s.(library) n.

(** ** Global state *)

Inductive stepk :=
  Upkeep | DrawStep | Main1 | BeginCombat | DeclAtk | DeclBlk
| DamageStep | EndCombat | Main2 | EndStep.

Definition is_main (st : stepk) : bool :=
  match st with Main1 | Main2 => true | _ => false end.

(** A blocker of an attacking Walker: a defending Walker (by index into the
    defender's [bf]) or a Thopter. Thopters are interchangeable. *)
Inductive blocker := BW (i : nat) | BT.

Definition blocker_eq_dec (x y : blocker) : {x = y} + {x <> y}.
Proof. decide equality. apply Nat.eq_dec. Defined.

Record combat := mkCombat {
  atk : list nat;              (** indices of the attacking Walkers *)
  atk_thop : nat;              (** number of attacking Thopters *)
  blk : list (list blocker);   (** blockers of each attacking Walker, in damage assignment order *)
  trades : nat;                (** attacking Thopters blocked by a Thopter (S7) *)
}.

Definition no_combat := mkCombat [] 0 [] 0.

(** Who has to decide what next. *)
Inductive pending :=
| Window (st : stepk) (prio : player) (passed : bool)
    (** a priority window (§3.3); [passed] means the previous player passed *)
| ChooseAttack                 (** active player declares attackers *)
| ChooseBlock                  (** defending player declares blockers *)
| ChooseOrder                  (** active player announces damage assignment orders *)
| ChooseDamage                 (** active player assigns combat damage *)
| ChooseShuffle (st : stepk) (prio : player) (cards : list card)
    (** the opponent of [prio] orders [prio]'s library (S9); then the window resumes *)
| Over (winner : player).

Record state := mkState {
  active : player;
  first_turn : bool;  (** this is the starting player's first turn *)
  sideA : side;
  sideB : side;
  cmb : combat;
  pend : pending;
}.

Definition get_side (p : player) (s : state) : side :=
  match p with PA => s.(sideA) | PB => s.(sideB) end.

Definition set_side (p : player) (sd : side) (s : state) : state :=
  match p with
  | PA => mkState s.(active) s.(first_turn) sd s.(sideB) s.(cmb) s.(pend)
  | PB => mkState s.(active) s.(first_turn) s.(sideA) sd s.(cmb) s.(pend)
  end.

Definition map_side (p : player) (f : side -> side) (s : state) : state :=
  set_side p (f (get_side p s)) s.

Definition set_cmb c s := mkState s.(active) s.(first_turn) s.(sideA) s.(sideB) c s.(pend).
Definition set_pend pd s := mkState s.(active) s.(first_turn) s.(sideA) s.(sideB) s.(cmb) pd.

(** The player who makes the next decision. *)
Definition to_move (s : state) : player :=
  match s.(pend) with
  | Window _ p _ => p
  | ChooseAttack | ChooseOrder | ChooseDamage => s.(active)
  | ChooseBlock => opp s.(active)
  | ChooseShuffle _ p _ => opp p
  | Over w => w
  end.

Definition winner (s : state) : option player :=
  match s.(pend) with Over w => Some w | _ => None end.

(** ** Initial state *)

Definition start_side (walkers : nat) (elixir : bool) : side :=
  mkSide 20 false 0 walkers elixir [] false 0 0 [] 0.

(** Player A: Walker, Walker, City. Player B: Walker, Elixir, City.
    The starting player's City is untapped from the start (S1). *)
Definition init (starter : player) : state :=
  let a := start_side 2 false in
  let b := start_side 1 true in
  map_side starter (set_city true)
    (mkState starter true a b no_combat (Window Upkeep starter false)).

(** ** Moves *)

Inductive move :=
| Pass
| Pump (i : nat)                 (** [{1},{T}] on own Walker [i] *)
| ActElixir                      (** [{2},{T}] on Elixir *)
| CastWalker (x : nat)
| CastElixir
| Attack (ws : list nat) (k : nat)
    (** attack with the Walkers at indices [ws] (increasing) and [k] Thopters *)
| Block (wb : list (option nat)) (tb : list nat) (tr : nat)
    (** [wb]: for each defending Walker, the attacker (index into [atk]) it blocks;
        [tb]: for each attacking Walker, the number of Thopters blocking it;
        [tr]: the number of attacking Thopters blocked by a Thopter *)
| Order (os : list (list blocker))  (** damage assignment order per attacking Walker *)
| Assign (js : list nat)            (** number of blockers killed per attacking Walker *)
| Arrange (lib : list card).        (** library order after a shuffle *)

(** ** Helpers *)

(** [l]'s elements paired with their indices. *)
Definition enum {A} (l : list A) : list (nat * A) := combine (seq 0 (length l)) l.

(** Apply [f] to the element at index [n]. *)
Definition update_nth {A} (n : nat) (f : A -> A) (l : list A) : list A :=
  map (fun '(i, x) => if i =? n then f x else x) (enum l).

(** Indices [i] of [l] with [f i (nth i l)] true, in increasing order. *)
Definition indices_where {A} (f : nat -> A -> bool) (l : list A) : list nat :=
  map fst (filter (fun '(i, x) => f i x) (enum l)).

(** Remove the elements whose index is in [dead]. *)
Definition remove_indices {A} (dead : list nat) (l : list A) : list A :=
  map snd (filter (fun '(i, _) => negb (existsb (Nat.eqb i) dead)) (enum l)).

(** All sublists of [l], keeping its order. *)
Definition subsets (l : list nat) : list (list nat) :=
  fold_right (fun x rs => rs ++ map (cons x) rs) [[]] l.

(** All lists of [len] naturals whose sum is at most [total]. *)
Fixpoint bounded_vectors (len total : nat) : list (list nat) :=
  match len with
  | 0 => [[]]
  | S len' =>
      flat_map (fun k => map (cons k) (bounded_vectors len' (total - k))) (seq 0 (S total))
  end.

(** All lists taking one element from each list of [choices]. *)
Definition product {A} (choices : list (list A)) : list (list A) :=
  fold_right (fun c rs => flat_map (fun x => map (cons x) rs) c) [[]] choices.

Section Orders.
Context {A : Type} (dec : forall x y : A, {x = y} + {x <> y}).

Fixpoint remove_first (x : A) (l : list A) : list A :=
  match l with
  | [] => []
  | y :: r => if dec x y then r else y :: remove_first x r
  end.

Fixpoint orders_fuel (fuel : nat) (l : list A) : list (list A) :=
  match fuel, l with
  | S f, _ :: _ => flat_map (fun x => map (cons x) (orders_fuel f (remove_first x l))) (nodup dec l)
  | _, _ => [[]]
  end.

(** The distinct orders of [l]'s elements: of a damage assignment order's
    distinct Walkers and identical Thopters, or of a library's cards. *)
Definition orders (l : list A) : list (list A) := orders_fuel (length l) l.

End Orders.

(** ** Mana (S4, S5) *)

(** Pay [n] generic mana, tapping City for {C}{C} only if the pool is short. *)
Definition pay (n : nat) (s : side) : option side :=
  if n <=? s.(pool) then Some (set_pool (s.(pool) - n) s)
  else if s.(city) && (n <=? s.(pool) + 2) then
    Some (set_pool (s.(pool) + 2 - n) (set_city false s))
  else None.

Definition can_pay (n : nat) (s : side) : bool :=
  match pay n s with Some _ => true | None => false end.

(** ** Actions in a priority window (§3.4) *)

Definition can_pump (w : walker) : bool := negb w.(wtapped) && negb w.(sick).

Definition window_moves (st : stepk) (p : player) (s : state) : list move :=
  let sd := get_side p s in
  let pumps :=
    if can_pay 1 sd then
      map Pump (indices_where (fun _ w => can_pump w) sd.(bf))
    else [] in
  let elixir := if sd.(elixir_bf) && can_pay 2 sd then [ActElixir] else [] in
  let sorcery :=
    if player_eqb p s.(active) && is_main st then
      (if 0 <? sd.(hand_w) then
         CastWalker 0 :: (if can_pay 2 sd then [CastWalker 1] else [])
       else [])
      ++ (if sd.(hand_e) && can_pay 1 sd then [CastElixir] else [])
    else [] in
  Pass :: pumps ++ elixir ++ sorcery.

(** ** Combat (§3.5, §3.6) *)

Definition defender (s : state) : player := opp s.(active).

Definition attack_moves (s : state) : list move :=
  let sd := get_side s.(active) s in
  let ready := indices_where (fun _ w => can_pump w) sd.(bf) in
  flat_map (fun ws => map (Attack ws) (seq 0 (S sd.(thop_u)))) (subsets ready).

Definition block_moves (s : state) : list move :=
  let d := get_side (defender s) s in
  let n := length s.(cmb).(atk) in
  let wchoices :=
    map (fun w => if w.(wtapped) then [None] else None :: map Some (seq 0 n)) d.(bf) in
  flat_map (fun wb =>
    flat_map (fun tb =>
      let left := d.(thop_u) - list_sum tb in
      map (Block wb tb) (seq 0 (S (Nat.min left s.(cmb).(atk_thop)))))
      (bounded_vectors n d.(thop_u)))
    (product wchoices).

Definition order_moves (s : state) : list move :=
  map Order (product (map (orders blocker_eq_dec) s.(cmb).(blk))).

Definition walker_power (sd : side) (i : nat) : nat := nth i (map counters sd.(bf)) 0.

Definition blocker_toughness (d : side) (b : blocker) : nat :=
  match b with BW i => walker_power d i | BT => 1 end.

(** Largest [j] such that the first [j] blockers' toughnesses sum to at most [p]. *)
Fixpoint max_prefix (p : nat) (ts : list nat) : nat :=
  match ts with
  | [] => 0
  | t :: r => if t <=? p then S (max_prefix (p - t) r) else 0
  end.

(** The numbers of blockers an attacker with power [p] can kill, given its
    blockers' toughnesses in damage assignment order (CR 510.1c, §3.6). *)
Definition kill_choices (p : nat) (ts : list nat) : list nat :=
  match ts with
  | [] => [0]
  | t :: _ => if p <? t then [0] else seq 1 (max_prefix p ts)
  end.

(** Comparison mode (post-Foundations, §3.6): the attacker divides damage
    freely, so any set of blockers whose toughness fits in [p] can be the
    killed set, and the empty set when [p] can be spread without killing.
    A killed set is a bitmask over the blockers in [blk] order. *)
Definition masked {X} (m : nat) (xs : list X) : list X :=
  map snd (filter (fun '(i, _) => Nat.testbit m i) (enum xs)).

Definition kill_sets_new (p : nat) (ts : list nat) : list nat :=
  match ts with
  | [] => [0]
  | _ =>
      filter (fun m => if m =? 0 then p <=? list_sum (map pred ts) else list_sum (masked m ts) <=? p)
        (seq 0 (2 ^ length ts))
  end.

Definition damage_moves (nw : bool) (s : state) : list move :=
  let a := get_side s.(active) s in
  let d := get_side (defender s) s in
  let per_attacker :=
    combine (map (walker_power a) s.(cmb).(atk)) s.(cmb).(blk) in
  let choices := if nw then kill_sets_new else kill_choices in
  map Assign
    (product (map (fun '(p, bs) => choices p (map (blocker_toughness d) bs))
                  per_attacker)).

(** ** All legal moves *)

Definition moves_gen (nw : bool) (s : state) : list move :=
  match s.(pend) with
  | Window st p _ => window_moves st p s
  | ChooseAttack => attack_moves s
  | ChooseBlock => block_moves s
  | ChooseOrder => order_moves s
  | ChooseDamage => damage_moves nw s
  | ChooseShuffle _ _ cards => map Arrange (orders card_eq_dec cards)
  | Over _ => []
  end.

(** ** Turn structure (§3.2) *)

Definition empty_pools (s : state) : state :=
  map_side PA (set_pool 0) (map_side PB (set_pool 0) s).

Definition draw (sd : side) : side :=
  match sd.(library) with
  | [] => sd  (* F2: no loss for drawing from an empty library *)
  | CWalker :: r => set_library r (set_hand_w (S sd.(hand_w)) sd)
  | CElixir :: r => set_library r (set_hand_e true sd)
  end.

Definition untap_side (sd : side) : side :=
  set_thop_t 0 (set_thop_u (sd.(thop_u) + sd.(thop_t))
    (set_bf (map (fun w => mkWalker w.(counters) false false) sd.(bf))
      (set_city true sd))).

Definition next_turn (s : state) : state :=
  let p := opp s.(active) in
  let s := map_side p untap_side s in
  mkState p false s.(sideA) s.(sideB) no_combat (Window Upkeep p false).

Definition has_multiblock (c : combat) : bool :=
  existsb (fun bs => 2 <=? length bs) c.(blk).

(** The step [st] ends: mana empties (CR 500.4) and the next step begins. *)
Definition end_step (st : stepk) (s : state) : state :=
  let s := empty_pools s in
  let ap := s.(active) in
  match st with
  | Upkeep =>
      let s := if s.(first_turn) then s else map_side ap draw s in
      set_pend (Window DrawStep ap false) s
  | DrawStep => set_pend (Window Main1 ap false) s
  | Main1 => set_pend (Window BeginCombat ap false) s
  | BeginCombat => set_pend ChooseAttack s
  | DeclAtk =>
      match s.(cmb).(atk), s.(cmb).(atk_thop) with
      | [], 0 => set_pend (Window EndCombat ap false) s  (* CR 508.8 *)
      | _, _ => set_pend ChooseBlock s
      end
  | DeclBlk => set_pend ChooseDamage s
  | DamageStep => set_pend (Window EndCombat ap false) s
  | EndCombat => set_pend (Window Main2 ap false) (set_cmb no_combat s)
  | Main2 => set_pend (Window EndStep ap false) s
  | EndStep => next_turn s
  end.

(** ** Effects of actions *)

Definition with_payment (n : nat) (p : player) (s : state) (k : state -> state) : state :=
  match pay n (get_side p s) with
  | Some sd => k (set_side p sd s)
  | None => s
  end.

Definition tap_walker (w : walker) : walker := mkWalker w.(counters) true w.(sick).
Definition pump_walker (w : walker) : walker := mkWalker (S w.(counters)) true w.(sick).

Definition do_pump (st : stepk) (p : player) (i : nat) (s : state) : state :=
  with_payment 1 p s (fun s =>
    set_pend (Window st p false) (map_side p (fun sd => set_bf (update_nth i pump_walker sd.(bf)) sd) s)).

(** Elixir: gain 5 life, then the opponent orders the library (S9). *)
Definition do_elixir (st : stepk) (p : player) (s : state) : state :=
  with_payment 2 p s (fun s =>
    let sd := get_side p s in
    let cards := sd.(library) ++ [CElixir] ++ repeat CWalker sd.(gy_w) in
    let sd := set_gy_w 0 (set_library [] (set_elixir_bf false (set_life (sd.(life) + 5) sd))) in
    set_pend (ChooseShuffle st p cards) (set_side p sd s)).

(** Casting a Walker for X = 0: it dies at once with no counters, so no Thopters. *)
Definition do_cast_walker (st : stepk) (p : player) (x : nat) (s : state) : state :=
  with_payment (2 * x) p s (fun s =>
    let sd := get_side p s in
    let sd := set_hand_w (pred sd.(hand_w)) sd in
    let sd := match x with
              | 0 => set_gy_w (S sd.(gy_w)) sd
              | _ => set_bf (sd.(bf) ++ [mkWalker x false true]) sd
              end in
    set_pend (Window st p false) (set_side p sd s)).

Definition do_cast_elixir (st : stepk) (p : player) (s : state) : state :=
  with_payment 1 p s (fun s =>
    set_pend (Window st p false)
      (map_side p (fun sd => set_elixir_bf true (set_hand_e false sd)) s)).

Definition do_attack (ws : list nat) (k : nat) (s : state) : state :=
  let ap := s.(active) in
  let s := map_side ap (fun sd =>
             set_thop_t (sd.(thop_t) + k) (set_thop_u (sd.(thop_u) - k)
               (set_bf (fold_right (fun i l => update_nth i tap_walker l) sd.(bf) ws) sd))) s in
  set_pend (Window DeclAtk ap false)
    (set_cmb (mkCombat ws k (map (fun _ => []) ws) 0) s).

Definition do_block (nw : bool) (wb : list (option nat)) (tb : list nat) (tr : nat) (s : state) : state :=
  let c := s.(cmb) in
  let blks :=
    map (fun '(a, k) =>
           map BW (indices_where (fun _ o => match o with Some b => b =? a | None => false end) wb)
           ++ repeat BT k)
        (enum tb) in
  let c := mkCombat c.(atk) c.(atk_thop) blks tr in
  let s := set_cmb c s in
  if has_multiblock c && negb nw then set_pend ChooseOrder s
  else set_pend (Window DeclBlk s.(active) false) s.

Definition do_order (os : list (list blocker)) (s : state) : state :=
  let c := s.(cmb) in
  set_pend (Window DeclBlk s.(active) false)
    (set_cmb (mkCombat c.(atk) c.(atk_thop) os c.(trades)) s).

(** A Walker dies: it goes to the graveyard and its controller gets one
    untapped Thopter per counter (§3.7). *)
Definition bury (dead : list nat) (sd : side) : side :=
  let gone := map (walker_power sd) dead in
  set_gy_w (sd.(gy_w) + length dead)
    (set_thop_u (sd.(thop_u) + list_sum gone)
      (set_bf (remove_indices dead sd.(bf)) sd)).

(** Combat damage (§3.6, §3.7). [js] gives, per attacking Walker, how many of
    its blockers (a prefix of its damage assignment order) are killed. *)
Definition do_damage (nw : bool) (js : list nat) (s : state) : state :=
  let ap := s.(active) in
  let dp := defender s in
  let a := get_side ap s in
  let d := get_side dp s in
  let c := s.(cmb) in
  let fights := combine (combine c.(atk) c.(blk)) js in
  (* damage to the defending player *)
  let unblocked :=
    list_sum (map (fun '(i, bs, _) => match bs with [] => walker_power a i | _ => 0 end) fights)
    + (c.(atk_thop) - c.(trades)) in
  (* attacking Walkers that die *)
  let a_dead :=
    map (fun '(i, _, _) => i)
      (filter (fun '(i, bs, _) =>
                 match bs with
                 | [] => false
                 | _ => walker_power a i <=? list_sum (map (blocker_toughness d) bs)
                 end) fights) in
  (* blockers that die *)
  let killed := flat_map (fun '(_, bs, j) => if nw then masked j bs else firstn j bs) fights in
  let d_dead := flat_map (fun b => match b with BW i => [i] | BT => [] end) killed in
  let d_thop_dead := count_occ blocker_eq_dec killed BT + c.(trades) in
  let a := bury a_dead (set_thop_t (a.(thop_t) - c.(trades)) a) in
  let d := bury d_dead (set_thop_u (d.(thop_u) - d_thop_dead) d) in
  let s := set_cmb no_combat (set_side dp d (set_side ap a s)) in
  if d.(life) <=? unblocked then set_pend (Over ap) s
  else set_pend (Window DamageStep ap false)
         (map_side dp (fun d => set_life (d.(life) - unblocked) d) s).

(** ** The transition function

    [step_gen nw s m] is only meaningful when [In m (moves_gen nw s)]. *)

Definition step_gen (nw : bool) (s : state) (m : move) : state :=
  match s.(pend), m with
  | Window st p passed, Pass =>
      if passed then end_step st s else set_pend (Window st (opp p) true) s
  | Window st p _, Pump i => do_pump st p i s
  | Window st p _, ActElixir => do_elixir st p s
  | Window st p _, CastWalker x => do_cast_walker st p x s
  | Window st p _, CastElixir => do_cast_elixir st p s
  | ChooseAttack, Attack ws k => do_attack ws k s
  | ChooseBlock, Block wb tb tr => do_block nw wb tb tr s
  | ChooseOrder, Order os => do_order os s
  | ChooseDamage, Assign js => do_damage nw js s
  | ChooseShuffle st p _, Arrange lib =>
      set_pend (Window st p false) (map_side p (set_library lib) s)
  | _, _ => s
  end.

(** The authoritative rules are pre-Foundations (§3.6); [moves_gen true] and
    [step_gen true] give the post-Foundations comparison mode. *)
Definition moves : state -> list move := moves_gen false.
Definition step : state -> move -> state := step_gen false.
