(* Unbounded-horizon solving on a finite abstraction of the game.

   Three reductions make the set of turn-start positions finite:

   - B's life is not part of the position. Every property computed here is
     monotone in B's life, so a position gets a threshold instead: for B's
     properties the least life B needs, for A's the most life B may have.
     Life only shifts along a turn (damage, Elixir), so thresholds compose
     exactly and this loses nothing.

   - The protagonist's own resources are capped: its Walkers stop pumping at
     [t] counters and Thopters above [tt] are discarded. Both only take
     options away from the protagonist (a Thopter is never a liability: its
     controller may ignore it), so results stay sound.

   - The opponent's resources saturate: a Walker pumped past [t] counters is
     "huge" (kept at t+1), and anything whose outcome would depend on its
     exact size counts as a loss for the protagonist: it dealing damage to the
     protagonist, it dying (its Thopters are unbounded), or being blocked by
     more toughness than t+1. More than [tt] opposing Thopters is also a loss.

   [safe] computes a greatest fixed point (the protagonist never loses), [win]
   a least one (it wins). Thresholds are cut to [lmax] on the pessimistic
   side: B needing more life than that counts as "never", and A's bound on B's
   life is lowered to it. *)
open Model
open Rules

let inf = max_int / 4
let ninf = min_int / 4
let big = 1000  (* B's life while a turn is searched, so the model never ends the game for B *)

type cfg = {
  prot : player;
  t : int;   (* the protagonist's Walkers stop at t counters *)
  ot : int;  (* the opponent's Walkers are huge above ot counters *)
  tt : int;
  lmax : int;
  full_a : bool;  (* B protagonist only: A's life is reset to 20 at each turn start *)
  mine : state -> move list;
  theirs : state -> move list;
}

(* B is the protagonist: values are least life needed, smaller is better.
   A is the protagonist: values are most life allowed, larger is better. *)
let up c = c.prot = PB
let best c a b = if up c then min a b else max a b
let worst c a b = if up c then max a b else min a b
let lose c = if up c then inf else ninf
let shift v d = if v >= inf || v <= ninf then v else v - d

(* Normalise a turn-start value: B's life is at least 1 there. *)
let norm c v =
  if up c then (if v > c.lmax then inf else if v <= 1 then 1 else v)
  else if v < 1 then ninf else if v >= inf then inf else min v c.lmax

let side_of p s = get_side p s
let huge c = c.ot + 1

(* Drop what the abstraction ignores: B's life (a threshold instead), A's
   graveyard (A has no Elixir), and with [full_a] A's life. *)
let normal full_a s =
  let s = Explore.canon s in
  let b = s.sideB and a = s.sideA in
  let a = { a with gy_w = 0; life = (if full_a then 20 else a.life) } in
  { s with sideA = a; sideB = { b with life = 0 } }

(* Key of any position, used inside a turn. *)
let key s = Marshal.to_string (normal false s) [ Marshal.No_sharing ]

(* Turn-start positions get a packed key, about a third of the marshalled
   size: a flags byte, then per side life, flags, pool, Walkers in hand,
   graveyard, Thopters (untapped, tapped), the Walkers (counters and flags
   each) and the library. *)
let pack_side buf sd =
  let byte n = assert (n >= 0 && n < 256); Buffer.add_char buf (Char.chr n) in
  let bit b k = if b then 1 lsl k else 0 in
  byte sd.life;
  byte (bit sd.city 0 lor bit sd.hand_e 1 lor bit sd.elixir_bf 2);
  byte sd.pool; byte sd.hand_w; byte sd.gy_w; byte sd.thop_u; byte sd.thop_t;
  byte (List.length sd.bf);
  List.iter (fun w -> byte w.counters; byte (bit w.wtapped 0 lor bit w.sick 1)) sd.bf;
  byte (List.length sd.library);
  List.iter (fun c -> byte (match c with CWalker -> 0 | CElixir -> 1)) sd.library

let key_gen full_a s =
  assert (Search.is_turn_start s && s.cmb = no_combat);
  let s = normal full_a s in
  let buf = Buffer.create 32 in
  Buffer.add_char buf (Char.chr ((if s.active = PA then 0 else 1) lor if s.first_turn then 2 else 0));
  pack_side buf s.sideA;
  pack_side buf s.sideB;
  Buffer.contents buf

let of_key k : state =
  let pos = ref 0 in
  let byte () = let n = Char.code k.[!pos] in incr pos; n in
  let side () =
    let life = byte () in
    let f = byte () in
    let pool = byte () in
    let hand_w = byte () in
    let gy_w = byte () in
    let thop_u = byte () in
    let thop_t = byte () in
    let bf = List.init (byte ()) (fun _ ->
        let counters = byte () in let g = byte () in
        { counters; wtapped = g land 1 <> 0; sick = g land 2 <> 0 }) in
    let library = List.init (byte ()) (fun _ -> if byte () = 0 then CWalker else CElixir) in
    { life; city = f land 1 <> 0; pool; hand_w; hand_e = f land 2 <> 0; bf; elixir_bf = f land 4 <> 0;
      thop_u; thop_t; library; gy_w }
  in
  let g = byte () in
  let active = if g land 1 = 0 then PA else PB in
  let sideA = side () in
  let sideB = side () in
  { active; first_turn = g land 2 <> 0; sideA; sideB = { sideB with life = big }; cmb = no_combat;
    pend = Window (Upkeep, active, false) }

(* Diagnostics only (unsound): TCB_LAX lists conservative rules to relax,
   so a failing check can be traced to the reduction responsible:
   dmg (a huge Walker's damage is its representative's), die (a huge Walker
   may die or be over-blocked; its Thopters are its representative's),
   many (extra opposing Thopters are discarded instead of losing). *)
let lax =
  match Sys.getenv_opt "TCB_LAX" with
  | None -> []
  | Some l -> String.split_on_char ',' l

(* Clamp after a step: the opponent's Walkers at most huge, the
   protagonist's Thopters at most tt (tapped ones go first). *)
let clamp c s =
  let o = opp c.prot in
  let os = side_of o s in
  let os = { os with bf = List.map (fun w -> if w.counters > huge c then { w with counters = huge c } else w) os.bf } in
  let cut sd =
    let extra = sd.thop_u + sd.thop_t - c.tt in
    if extra <= 0 then sd
    else
      let dt = min extra sd.thop_t in
      { sd with thop_t = sd.thop_t - dt; thop_u = sd.thop_u - (extra - dt) }
  in
  let os = if List.mem "many" lax then cut os else os in
  set_side c.prot (cut (side_of c.prot s)) (set_side o os s)

(* Does this move make an exact huge size matter (a loss for the protagonist)? *)
let huge_event c s m =
  let o = opp c.prot in
  let strict r = not (List.mem r lax) in
  match s.pend, m with
  | ChooseDamage, Assign _ ->
    let att = side_of s.active s and def = side_of (opp s.active) s in
    let is_huge sd i = (List.nth sd.bf i).counters >= huge c in
    let tough sd = function BW i -> (List.nth sd.bf i).counters | BT -> 1 in
    let total bs = List.fold_left (fun n b -> n + tough def b) 0 bs in
    let fights = List.combine s.cmb.atk s.cmb.blk in
    (* an attacking huge Walker of the opponent that is unblocked *)
    (strict "dmg" && s.active = o && List.exists (fun (i, bs) -> is_huge att i && bs = []) fights)
    (* ... or blocked by enough toughness to matter: it may die, or kill more than its representative *)
    || (strict "die" && s.active = o
        && List.exists (fun (i, bs) -> is_huge att i && bs <> [] && total bs >= huge c) fights)
    (* a huge blocking Walker of the opponent that its attacker could kill *)
    || (strict "die" && s.active <> o
        && List.exists (fun (i, bs) ->
            List.exists (function BW j -> is_huge def j && (List.nth att.bf i).counters >= huge c | BT -> false) bs)
          fights)
  | _ -> false

let too_many c s =
  (not (List.mem "many" lax)) && let os = side_of (opp c.prot) s in os.thop_u + os.thop_t > c.tt

let moves_for c s =
  if to_move s = c.prot then
    let ps = side_of c.prot s in
    List.filter (function Pump i -> (List.nth ps.bf i).counters < c.t | _ -> true) (c.mine s)
  else c.theirs s

(* Value from [s], given the table; [root] marks the turn start the search
   began at (turn starts after it are looked up). *)
let eval_from c (lookup : string -> int) s root =
  let local = Hashtbl.create 256 in
  let rec go s root =
    match winner s with
    | Some PB -> ninf  (* A died: a win for B, a loss for A *)
    | Some PA -> assert false
    | None ->
      if (not root) && Search.is_turn_start s then lookup (key_gen c.full_a s)
      else begin
        let k = key s in
        match Hashtbl.find_opt local k with
        | Some v -> v
        | None ->
          let ms = moves_for c s in
          let pick = if to_move s = c.prot then best c else worst c in
          let v =
            List.fold_left (fun acc m -> pick acc (edge s m))
              (if to_move s = c.prot then lose c else if up c then ninf else inf) ms
          in
          Hashtbl.replace local k v;
          v
      end
  and edge s m =
    if huge_event c s m then lose c
    else
      let s' = clamp c (step s m) in
      if too_many c s' then lose c
      else
        let d = s'.sideB.life - s.sideB.life in
        let v = shift (go s' false) d in
        if d < 0 then (if up c then max (1 - d) v else max (-d) v) else v
  in
  go s root

(* Value of the turn starting at [s] (a turn start). *)
let eval_turn c lookup s = eval_from c lookup s true

(* The same turn, compiled once into a straight-line program over the values
   of the turn starts it can end in, so re-evaluating it needs no model
   steps. Nodes come in post-order. A node is a header word (2n + pick, pick
   0 for the protagonist) and n children of two words each: x, then
   4d + kind, where d is the change in B's life on that edge and kind is
   0 for a constant (x = 0 for ninf, 1 for inf), 1 for node number x, 2 for
   turn start x (an index given by [id]). Single-child nodes are inlined and
   children that can never be picked are dropped. *)
type cref = Const of int | Ref of int * int * int  (* kind, x, d *)

let compile c (id : string -> int) s =
  let local = Hashtbl.create 256 in
  let buf = ref [] and nodes = ref 0 in
  let lost = if lose c = ninf then 0 else 1 in
  let won = 1 - lost in
  let rec go s root =
    match winner s with
    | Some PB -> Const 0
    | Some PA -> assert false
    | None ->
      if (not root) && Search.is_turn_start s then Ref (2, id (key_gen c.full_a s), 0)
      else begin
        let k = key s in
        match Hashtbl.find_opt local k with
        | Some r -> r
        | None ->
          let mine = to_move s = c.prot in
          (* the constant the chooser can never prefer, and the one that decides the node *)
          let useless = if mine then lost else won and decisive = if mine then won else lost in
          let kids = List.map (fun m -> edge s m) (moves_for c s) in
          let r =
            if List.mem (Const decisive) kids then Const decisive
            else
              match List.sort_uniq compare (List.filter (fun r -> r <> Const useless) kids) with
              | [] -> Const useless
              | [ r ] -> r
              | kids ->
                buf := ((2 * List.length kids) + if mine then 0 else 1) :: !buf;
                List.iter (function
                    | Ref (kind, x, d) -> buf := ((4 * d) + kind) :: x :: !buf
                    | Const v -> buf := 0 :: v :: !buf) kids;
                incr nodes;
                Ref (1, !nodes - 1, 0)
          in
          Hashtbl.replace local k r;
          r
      end
  and edge s m =
    if huge_event c s m then Const lost
    else
      let s' = clamp c (step s m) in
      if too_many c s' then Const lost
      else
        let d = s'.sideB.life - s.sideB.life in
        let wrap kind x d' = buf := ((4 * d') + kind) :: x :: 2 :: !buf; incr nodes; Ref (1, !nodes - 1, d) in
        match go s' false with
        | Const v when d >= 0 -> Const v  (* constants are sentinels: shifts don't move them *)
        | Const v -> wrap 0 v 0  (* but B may die on this edge *)
        | Ref (kind, x, 0) -> Ref (kind, x, d)
        | Ref (kind, x, d') when d = 0 -> Ref (kind, x, d')
        | Ref (kind, x, d') -> wrap kind x d'  (* two life changes on one path: the inner one gets its own node *)
  in
  let root = go s true in
  (* make sure the program ends with the root node *)
  (match root with
   | Ref (1, n, 0) when n = !nodes - 1 -> ()
   | Ref (kind, x, d) -> buf := ((4 * d) + kind) :: x :: 2 :: !buf; incr nodes
   | Const v -> buf := 0 :: v :: 2 :: !buf; incr nodes);
  let l = List.rev !buf in
  let a = Bigarray.(Array1.create int32 c_layout (List.length l)) in
  List.iteri (fun i x -> a.{i} <- Int32.of_int x) l;
  (a, !nodes)

let run c (vals : int array) ((prog : (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t), nodes) =
  let get i = Int32.to_int prog.{i} in
  let nv = Array.make nodes 0 in
  let pc = ref 0 in
  for n = 0 to nodes - 1 do
    let h = get !pc in
    let mine = h land 1 = 0 in
    let pick = if mine then best c else worst c in
    let cnt = h lsr 1 in
    incr pc;
    let acc = ref (if mine then lose c else if up c then ninf else inf) in
    for _ = 1 to cnt do
      let x = get !pc and kd = get (!pc + 1) in
      pc := !pc + 2;
      let kind = kd land 3 and d = kd asr 2 in
      let v = match kind with 0 -> if x = 0 then ninf else inf | 1 -> nv.(x) | _ -> vals.(x) in
      let v = shift v d in
      let v = if d < 0 then (if up c then max (1 - d) v else max (-d) v) else v in
      acc := pick !acc v
    done;
    nv.(n) <- !acc
  done;
  nv.(nodes - 1)

type solver = {
  ids : (int, int) Hashtbl.t;  (* position digest -> index *)
  keys : string array;  (* index -> position *)
  n : int;
  vals : int array;
  mutable hist : (int * int) list array;
    (* with ranks: (round, value) changes per position, latest first; rounds
       are synchronous within an A-life level *)
}

(* Turn-start positions reachable from [s0] in the abstraction. *)
let reach c s0 =
  let ids = Hashtbl.create 100_000 in
  let keys = ref [] and n = ref 0 and done_ = ref 0 in
  let queue = Queue.create () in
  let add k =
    let h = Tsearch.digest_key k in
    if not (Hashtbl.mem ids h) then (Hashtbl.add ids h !n; incr n; keys := k :: !keys; Queue.add k queue)
  in
  add (key_gen c.full_a s0);
  while not (Queue.is_empty queue) do
    let k = Queue.pop queue in
    let s = of_key k in
    assert (key_gen c.full_a s = k);  (* the packing round-trips *)
    ignore (eval_turn c (fun k -> add k; 0) s);
    incr done_;
    if !done_ mod 100_000 = 0 then Printf.printf "  reach: %d done, %d found\n%!" !done_ !n
  done;
  { ids; keys = Array.of_list (List.rev !keys); n = !n; vals = Array.make !n 0; hist = [||] }

(* Iterate to the fixed point from [start] (optimistic for [safe],
   pessimistic for [win]). A never gains life, so positions are solved one
   A-life level at a time, lowest first: a level's turns only end in its own
   level or in lower, already solved ones. Each level's turns are compiled,
   solved with a worklist that re-evaluates only positions with a changed
   successor, and then dropped. *)
let solve ?(ranks = false) c sv ~start =
  let n = sv.n in
  Array.fill sv.vals 0 n start;
  if ranks then sv.hist <- Array.make n [];
  let id k = Hashtbl.find sv.ids (Tsearch.digest_key k) in
  let level = Array.make 21 [] in
  for i = n - 1 downto 0 do
    let l = (of_key sv.keys.(i)).sideA.life in
    level.(l) <- i :: level.(l)
  done;
  let evals = ref 0 and t0 = Sys.time () in
  Array.iteri (fun l members ->
      if members <> [] then begin
        let members = Array.of_list members in
        let m = Array.length members in
        let local = Hashtbl.create m in
        Array.iteri (fun j i -> Hashtbl.add local i j) members;
        let progs = Array.map (fun i -> compile c id (of_key sv.keys.(i))) members in
        (* predecessors within the level *)
        let preds = Array.make m [] in
        Array.iteri (fun j (prog, _) ->
            let get x = Int32.to_int prog.{x} in
            let len = Bigarray.Array1.dim prog and p = ref 0 in
            while !p < len do
              let cnt = get !p lsr 1 in
              for e = 0 to cnt - 1 do
                let b = !p + 1 + (2 * e) in
                if get (b + 1) land 3 = 2 then
                  match Hashtbl.find_opt local (get b) with
                  | Some j' -> preds.(j') <- j :: preds.(j')
                  | None -> ()
              done;
              p := !p + 1 + (2 * cnt)
            done)
          progs;
        let preds = Array.map (fun l -> Array.of_list (List.sort_uniq compare l)) preds in
        let words = Array.fold_left (fun a (p, _) -> a + Bigarray.Array1.dim p) 0 progs in
        if ranks then begin
          (* synchronous rounds, so each value change gets a round number *)
          let round = ref 0 and changed = ref true in
          while !changed do
            incr round;
            changed := false;
            let nv = Array.map (fun p -> incr evals; norm c (run c sv.vals p)) progs in
            Array.iteri (fun j v ->
                let i = members.(j) in
                if v <> sv.vals.(i) then (changed := true; sv.hist.(i) <- (!round, v) :: sv.hist.(i)))
              nv;
            Array.iteri (fun j v -> sv.vals.(members.(j)) <- v) nv
          done
        end;
        let queued = Array.make m true and work = Queue.create () in
        for j = 0 to m - 1 do Queue.add j work done;
        while not (Queue.is_empty work) do
          let j = Queue.pop work in
          queued.(j) <- false;
          incr evals;
          let v = norm c (run c sv.vals progs.(j)) in
          if v <> sv.vals.(members.(j)) then begin
            sv.vals.(members.(j)) <- v;
            Array.iter (fun j' -> if not queued.(j') then (queued.(j') <- true; Queue.add j' work)) preds.(j)
          end
        done;
        Printf.printf "  A life %d: %d positions, %d program words, %d evaluations so far (%.1fs)\n%!"
          l m words !evals (Sys.time () -. t0)
      end)
    level;
  (* spot check: the compiled turns agree with direct evaluation through the model *)
  let lookup k = sv.vals.(id k) in
  let bad = ref 0 in
  for i = 0 to n - 1 do
    if i mod 500 = 0 && norm c (eval_turn c lookup (of_key sv.keys.(i))) <> sv.vals.(i) then incr bad
  done;
  if !bad > 0 then Printf.printf "  SPOT CHECK FAILED at %d positions\n%!" !bad
  else Printf.printf "  spot check passed\n%!"

let value c sv s = sv.vals.(Hashtbl.find sv.ids (Tsearch.digest_key (key_gen c.full_a s)))

let safe c s0 =
  let sv = reach c s0 in
  Printf.printf "%d positions\n%!" sv.n;
  solve c sv ~start:(if up c then 1 else inf);
  sv

let win ?ranks c s0 =
  let sv = reach c s0 in
  Printf.printf "%d positions\n%!" sv.n;
  solve ?ranks c sv ~start:(lose c);
  sv

let show c v =
  if up c then (if v >= inf then "never" else Printf.sprintf "B life >= %d" v)
  else if v <= ninf then "never" else if v >= inf then "any B life" else Printf.sprintf "B life <= %d" v

(* A line of play from [s0] with B on [life], following the solved values
   (needs [ranks]). The protagonist plays a move that keeps its value as of
   the previous round of the current position's level (so the line makes
   progress); the opponent plays a worst move for it. *)
let line c sv s0 life turns =
  let id k = Hashtbl.find sv.ids (Tsearch.digest_key k) in
  let level k = (of_key k).sideA.life in
  let at_round i r =
    match List.find_opt (fun (r', _) -> r' <= r) sv.hist.(i) with Some (_, v) -> v | None -> lose c
  in
  let at_big s = { s with sideB = { s.sideB with life = big } } in
  let rec walk s t =
    match winner s with
    | Some w -> Printf.printf "*** %s wins\n" (Show.player w)
    | None ->
      if Search.is_turn_start s then begin
        let k = key_gen c.full_a s in
        let i = id k in
        let l = s.sideB.life in
        (* the first round at which this position was won with this life *)
        let r = List.fold_left (fun acc (r', v) -> if v <= l then r' else acc) max_int sv.hist.(i) in
        Printf.printf "--- turn %d (round %d of A-life level %d) ---\n%s\n" t r (level k) (Show.state s);
        let lk k' = let j = id k' in if level k' < level k then sv.vals.(j) else at_round j (r - 1) in
        if t < turns then go lk s (t + 1)
      end else go (fun k' -> sv.vals.(id k')) s t
  and go lk s t =
    let scored = List.map (fun m ->
        let s' = clamp c (step s m) in
        let v = if huge_event c s m || too_many c s' then lose c else
            match winner s' with Some _ -> ninf | None ->
              let d = s'.sideB.life - s.sideB.life in
              let v = shift (eval_from c lk (at_big s') false) d in
              if d < 0 then max (1 - d) v else v in
        (m, s', v)) (moves_for c s) in
    let pick = if to_move s = c.prot then best c else worst c in
    let m, s', _ = List.fold_left (fun ((_, _, bv) as acc) ((_, _, v) as x) -> if pick v bv <> bv then x else acc)
        (List.hd scored) (List.tl scored) in
    if m <> Pass then Printf.printf "  %s: %s\n" (Show.player (to_move s)) (Show.move m);
    walk_in lk s' t
  and walk_in lk s t =
    match winner s with
    | Some _ -> walk s t
    | None -> if Search.is_turn_start s then walk s t else go lk s t
  in
  walk { s0 with sideB = { s0.sideB with life } } 0
