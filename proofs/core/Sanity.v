(** * Sanity checks of the model against known lines of play *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
From TCB.Spec Require Import Model.

(** ** Replaying scripts of moves, checking that each move is legal *)

Fixpoint list_eqb {A} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: r1, y :: r2 => eqb x y && list_eqb eqb r1 r2
  | _, _ => false
  end.

Definition option_eqb {A} (eqb : A -> A -> bool) (o1 o2 : option A) : bool :=
  match o1, o2 with
  | None, None => true
  | Some x, Some y => eqb x y
  | _, _ => false
  end.

Definition blocker_eqb (b1 b2 : blocker) : bool :=
  match b1, b2 with
  | BW i, BW j => Nat.eqb i j
  | BT, BT => true
  | _, _ => false
  end.

Definition card_eqb (c1 c2 : card) : bool :=
  match c1, c2 with CWalker, CWalker | CElixir, CElixir => true | _, _ => false end.

Definition move_eqb (m1 m2 : move) : bool :=
  match m1, m2 with
  | Pass, Pass | ActElixir, ActElixir | CastElixir, CastElixir => true
  | Pump i, Pump j => Nat.eqb i j
  | CastWalker x, CastWalker y => Nat.eqb x y
  | Attack ws k, Attack ws' k' => list_eqb Nat.eqb ws ws' && Nat.eqb k k'
  | Block wb tb tr, Block wb' tb' tr' =>
      list_eqb (option_eqb Nat.eqb) wb wb' && list_eqb Nat.eqb tb tb' && Nat.eqb tr tr'
  | Order os, Order os' => list_eqb (list_eqb blocker_eqb) os os'
  | Assign js, Assign js' => list_eqb Nat.eqb js js'
  | Arrange l, Arrange l' => list_eqb card_eqb l l'
  | _, _ => false
  end.

Definition legal (s : state) (m : move) : bool := existsb (move_eqb m) (moves s).

Fixpoint play (s : state) (ms : list move) : option state :=
  match ms with
  | [] => Some s
  | m :: r => if legal s m then play (step s m) r else None
  end.

Definition passes (n : nat) : list move := repeat Pass n.

(** Both players pass through [n] priority windows. *)
Definition skip (n : nat) : list move := passes (2 * n).

Definition after (s : state) (ms : list move) (f : state -> bool) : bool :=
  match play s ms with Some s' => f s' | None => false end.

(** ** Opening turns *)

(** A on the play: City, Walker for X=1. No draw on the first turn. *)
Definition a_turn1 : list move :=
  skip 2 ++ [CastWalker 1] ++ skip 2 ++ [Attack [] 0] ++ skip 4.

Example a_turn1_legal :
  after (init PA) a_turn1 (fun s =>
    player_eqb s.(active) PB
    && Nat.eqb (length s.(sideA).(bf)) 1
    && Nat.eqb s.(sideA).(hand_w) 1
    && negb s.(sideA).(city)
    && s.(sideB).(city)) = true.
Proof. vm_compute. reflexivity. Qed.

(** The new Walker is summoning sick: it can't be pumped during B's turn. *)
Example sick_walker_cannot_pump_on_opponents_turn :
  after (init PA) (a_turn1 ++ [Pass]) (fun s =>
    negb (existsb (move_eqb (Pump 0)) (moves s))) = true.
Proof. vm_compute. reflexivity. Qed.

(** Walker X=1 needs both mana from City; X=2 is never offered. *)
Example walker_x_at_most_1 :
  after (init PA) (skip 2) (fun s =>
    list_eqb move_eqb (moves s) [Pass; CastWalker 0; CastWalker 1]) = true.
Proof. vm_compute. reflexivity. Qed.

(** B: cast Elixir in the first main phase; it can't be activated that turn,
    because only one mana is left. *)
Definition b_turn1_elixir : list move :=
  skip 2 ++ [CastElixir] ++ skip 2 ++ [Attack [] 0] ++ skip 4.

Example elixir_not_activated_same_turn :
  after (init PB) (skip 2 ++ [CastElixir]) (fun s =>
    negb (existsb (move_eqb ActElixir) (moves s))) = true.
Proof. vm_compute. reflexivity. Qed.

(** Next turn B can activate it: +5 life, and A chooses the library order. *)
Example elixir_activation :
  after (init PB)
    (b_turn1_elixir ++ skip 4 ++ [Attack [] 0] ++ skip 4  (* A's turn 1, no plays *)
     ++ skip 1 ++ [ActElixir; Arrange [CElixir]])
    (fun s => Nat.eqb s.(sideB).(life) 25
              && list_eqb card_eqb s.(sideB).(library) [CElixir]
              && negb s.(sideB).(elixir_bf)) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Combat *)

Definition mk_state (ap : player) (a b : side) (pd : pending) : state :=
  mkState ap false a b no_combat pd.

Definition w (n : nat) : walker := mkWalker n false false.

(** A attacks with a 3/3 Walker; B blocks with a 2/2 Walker and a Thopter. *)
Definition combat_a :=
  mk_state PA
    (mkSide 20 true 0 0 false [w 3] false 0 0 [] 0)
    (mkSide 20 true 0 0 false [w 2] false 1 0 [] 0)
    ChooseAttack.

Definition combat_a_blocked :=
  [Attack [0] 0] ++ skip 1 ++ [Block [Some 0] [1] 0].

Example combat_two_orders :
  after combat_a combat_a_blocked (fun s =>
    Nat.eqb (length (moves s)) 2) = true.
Proof. vm_compute. reflexivity. Qed.

(** Order Walker first: 3 damage can kill the Walker alone, or both. *)
Example combat_kill_choices :
  after combat_a (combat_a_blocked ++ [Order [[BW 0; BT]]] ++ skip 1) (fun s =>
    list_eqb move_eqb (moves s) [Assign [1]; Assign [2]]) = true.
Proof. vm_compute. reflexivity. Qed.

(** If B pumps the blocking Walker after the order is announced, it is 3/3:
    the attacker must put all 3 damage on it and can't reach the Thopter.
    The attacker takes 3 + 1 damage and dies, giving A 3 Thopters. *)
Example combat_pump_after_order' :
  after combat_a
    (combat_a_blocked ++ [Order [[BW 0; BT]]; Pass; Pump 0] ++ passes 2)
    (fun s => list_eqb move_eqb (moves s) [Assign [1]]) = true.
Proof. vm_compute. reflexivity. Qed.

Example combat_pump_after_order_result :
  after combat_a
    (combat_a_blocked ++ [Order [[BW 0; BT]]; Pass; Pump 0] ++ passes 2 ++ [Assign [1]])
    (fun s => Nat.eqb (length s.(sideA).(bf)) 0     (* A's Walker died *)
              && Nat.eqb s.(sideA).(thop_u) 3        (* A got 3 Thopters *)
              && Nat.eqb (length s.(sideB).(bf)) 0   (* B's 3/3 Walker died too *)
              && Nat.eqb s.(sideB).(thop_u) 4        (* B's Thopter + 3 new *)
              && Nat.eqb s.(sideB).(gy_w) 1
              && Nat.eqb s.(sideB).(life) 20) = true.
Proof. vm_compute. reflexivity. Qed.

(** Thopters: two attack, one is blocked by a Thopter, one gets through. *)
Example thopter_trade :
  after
    (mk_state PA (mkSide 20 true 0 0 false [] false 2 0 [] 0)
                 (mkSide 20 true 0 0 false [] false 1 0 [] 0) ChooseAttack)
    ([Attack [] 2] ++ skip 1 ++ [Block [] [] 1] ++ skip 1 ++ [Assign []])
    (fun s => Nat.eqb s.(sideB).(life) 19
              && Nat.eqb s.(sideB).(thop_u) 0
              && Nat.eqb s.(sideA).(thop_t) 1) = true.
Proof. vm_compute. reflexivity. Qed.

(** Lethal damage ends the game. *)
Example lethal :
  after
    (mk_state PA (mkSide 20 true 0 0 false [w 5] false 0 0 [] 0)
                 (mkSide 5 true 0 0 false [] false 0 0 [] 0) ChooseAttack)
    ([Attack [0] 0] ++ skip 1 ++ [Block [] [0] 0] ++ skip 1 ++ [Assign [0]])
    (fun s => match winner s with Some PA => true | _ => false end) = true.
Proof. vm_compute. reflexivity. Qed.

(** Walkers can't block Thopters: with only Thopters attacking, the only
    choices for B's Walker are not blocking. *)
Example walkers_cannot_block_thopters :
  after
    (mk_state PA (mkSide 20 true 0 0 false [] false 1 0 [] 0)
                 (mkSide 20 true 0 0 false [w 4] false 0 0 [] 0) ChooseAttack)
    ([Attack [] 1] ++ skip 1)
    (fun s => list_eqb move_eqb (moves s) [Block [None] [] 0]) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** More rules checks *)

(** Walker for X=0 enters with no counters and dies at once (CR 704.5f):
    it goes to the graveyard and makes no Thopters. *)
Example walker_x0_dies :
  after (init PA) (skip 2 ++ [CastWalker 0]) (fun s =>
    Nat.eqb (length s.(sideA).(bf)) 0
    && Nat.eqb s.(sideA).(gy_w) 1
    && Nat.eqb s.(sideA).(thop_u) 0
    && Nat.eqb s.(sideA).(hand_w) 1) = true.
Proof. vm_compute. reflexivity. Qed.

(** An attacking Walker is tapped, so it can't be pumped. *)
Example attacker_cannot_pump :
  after combat_a [Attack [0] 0] (fun s =>
    negb (existsb (move_eqb (Pump 0)) (moves s))) = true.
Proof. vm_compute. reflexivity. Qed.

(** B on 5 life, unblocked 5/5 attacker: activating Elixir after blocks
    (+5 life) keeps B alive; A orders the shuffled library. *)
Definition elixir_defence :=
  mk_state PA (mkSide 20 true 0 0 false [w 5] false 0 0 [] 0)
              (mkSide 5 true 0 0 false [] true 0 0 [] 0) ChooseAttack.

Example elixir_after_blocks_survives :
  after elixir_defence
    ([Attack [0] 0] ++ skip 1 ++ [Block [] [0] 0; Pass; ActElixir; Arrange [CElixir]]
     ++ passes 2 ++ [Assign [0]])
    (fun s => match winner s with
              | None => Nat.eqb s.(sideB).(life) 5
              | Some _ => false
              end) = true.
Proof. vm_compute. reflexivity. Qed.

(** Without the activation the same attack is lethal. *)
Example elixir_unused_lethal :
  after elixir_defence
    ([Attack [0] 0] ++ skip 1 ++ [Block [] [0] 0] ++ skip 1 ++ [Assign [0]])
    (fun s => match winner s with Some PA => true | _ => false end) = true.
Proof. vm_compute. reflexivity. Qed.

(** Elixir shuffles the graveyard too: with a dead Walker there, A may put
    either card on top. *)
Example elixir_shuffles_graveyard :
  after
    (mk_state PA (mkSide 20 true 0 0 false [] false 0 0 [] 0)
                 (mkSide 20 true 0 0 false [] true 0 0 [] 1) (Window EndStep PA false))
    [Pass; ActElixir]
    (fun s => Nat.eqb (length (moves s)) 2
              && existsb (move_eqb (Arrange [CWalker; CElixir])) (moves s)
              && existsb (move_eqb (Arrange [CElixir; CWalker])) (moves s)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Draw step: B draws the top card of its library. *)
Example draw_top_card :
  after
    (mk_state PB (mkSide 20 true 0 0 false [] false 0 0 [] 0)
                 (mkSide 20 true 0 0 false [] false 0 0 [CWalker; CElixir] 0)
                 (Window Upkeep PB false))
    (skip 1)
    (fun s => Nat.eqb s.(sideB).(hand_w) 1
              && list_eqb card_eqb s.(sideB).(library) [CElixir]) = true.
Proof. vm_compute. reflexivity. Qed.

(** Drawing from an empty library is harmless (3CB rule F2). *)
Example empty_library_draw :
  after
    (mk_state PB (mkSide 20 true 0 0 false [] false 0 0 [] 0)
                 (mkSide 20 true 0 0 false [] false 0 0 [] 0)
                 (Window Upkeep PB false))
    (skip 2)
    (fun s => match winner s with None => true | Some _ => false end) = true.
Proof. vm_compute. reflexivity. Qed.
