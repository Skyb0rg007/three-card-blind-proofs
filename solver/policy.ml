(* Simple deterministic strategies, used to probe the game: a policy is
   tested by searching all of the opponent's replies against it. *)
open Model
open Rules

type policy = state -> move

let side_of s p = get_side p s
let mine s = side_of s (to_move s)
let theirs s = side_of s (opp (to_move s))

let has m s = List.mem m (Reduce.moves s)
let first_of ms s = match List.find_opt (fun m -> has m s) ms with Some m -> m | None -> Pass

let walker_size sd i = (List.nth sd.bf i).counters

(* Pump every walker we can, at the end of the opponent's turn. *)
let pump_any s =
  let sd = mine s in
  let rec go i = function
    | [] -> None
    | _ :: r -> if has (Pump i) s then Some (Pump i) else go (i + 1) r
  in
  go 0 sd.bf

(* Never attack; grow; cast in main 2; [elixir] decides when to prefer
   activating Elixir over pumping at the opponent's end step. *)
let turtle ~elixir : policy = fun s ->
  match s.pend with
  | Window (Main2, p, _) when p = s.active -> first_of [ CastWalker 1; CastElixir ] s
  | Window (EndStep, p, _) when p <> s.active ->
    if elixir s && has ActElixir s then ActElixir
    else (match pump_any s with Some m -> m | None -> Pass)
  | Window (DeclBlk, p, _) when p <> s.active ->
    (* gain life before lethal damage *)
    if has ActElixir s then ActElixir else Pass
  | ChooseAttack -> Attack ([], 0)
  | ChooseShuffle _ -> List.hd (Reduce.moves s)
  | _ -> List.hd (Reduce.moves s)

(* Single-agent search: can [p] beat the fixed [pol] of the opponent within
   [d] turns? Returns the line if so. *)
let beat ?(mine = Reduce.moves) p (pol : policy) =
  let tbl = Hashtbl.create 100_000 in
  let rec go s d =
    match winner s with
    | Some w -> if w = p then Some [] else None
    | None ->
      if d < 0 then None
      else
        let k = Csearch.key s in
        let known = try Hashtbl.find tbl k with Not_found -> -1 in
        if d <= known then None
        else if to_move s = p then begin
          let r =
            List.fold_left (fun acc m ->
                match acc with
                | Some _ -> acc
                | None -> (let s' = step s m in Option.map (fun l -> (s, m) :: l) (go s' (Search.tick s s' d))))
              None (mine s)
          in
          if r = None then Hashtbl.replace tbl k d;
          r
        end else begin
          let m = pol s in
          let r = (let s' = step s m in Option.map (fun l -> (s, m) :: l) (go s' (Search.tick s s' d))) in
          if r = None then Hashtbl.replace tbl k d;
          r
        end
  in
  go

(* Does the fixed policy [pol] for [p] win within [d] turns against every
   opponent reply from [theirs]? On failure, returns a surviving opponent line. *)
let check ?(theirs = Reduce.moves) p (pol : policy) =
  let tbl = Hashtbl.create 1_000_000 in
  let rec go s d : (state * move) list option =
    (* None = policy wins; Some line = opponent survives along line *)
    match winner s with
    | Some w -> if w = p then None else Some []
    | None ->
      if d < 0 then Some []
      else
        let k = Csearch.key s in
        let won = try Hashtbl.find tbl k with Not_found -> max_int in
        if d >= won then None
        else begin
          let r =
            if to_move s = p then
              let m = pol s in (let s' = step s m in Option.map (fun l -> (s, m) :: l) (go s' (Search.tick s s' d)))
            else
              List.fold_left (fun acc m ->
                  match acc with
                  | Some _ -> acc
                  | None -> (let s' = step s m in Option.map (fun l -> (s, m) :: l) (go s' (Search.tick s s' d))))
                None (theirs s)
          in
          if r = None then Hashtbl.replace tbl k d;
          r
        end
  in
  go

(* ---- A strategies ---- *)

let b_side s = get_side PB s
let a_side s = get_side PA s

(* largest effective block size of B's untapped Walker (+1 if it can pump) *)
let b_blocker s =
  let b = b_side s in
  List.fold_left (fun acc w ->
      if w.wtapped then acc
      else
        let pump = if (not w.sick) && (b.city || b.pool > 0) then 1 else 0 in
        max acc (w.counters + pump))
    0 b.bf

(* A's damage-assignment order: Thopters first, Walkers last; kill only the
   Thopters at the front. *)
let a_order s =
  Order (List.map (fun bs ->
      List.filter (fun b -> b = BT) bs @ List.filter (fun b -> b <> BT) bs) s.cmb.blk)

let a_assign s =
  let ms = Reduce.moves s in
  (* prefer the assignment killing the most blockers that are Thopters only *)
  let thopters_only js =
    List.for_all2 (fun j bs -> List.for_all (fun b -> b = BT) (List.filteri (fun i _ -> i < j) bs)) js s.cmb.blk in
  let cands = List.filter (function Assign js -> thopters_only js | _ -> false) ms in
  let score = function Assign js -> List.fold_left ( + ) 0 js | _ -> -1 in
  match List.sort (fun a b -> compare (score b) (score a)) cands with
  | m :: _ -> m
  | [] -> List.hd ms


(* Attack with everything if the damage B can't block is lethal even after
   an Elixir activation. B blocks one attacker per untapped creature, so the
   damage that surely gets through is the total minus the biggest attackers. *)
let lethal_attack s =
  let a = a_side s and b = b_side s in
  let ready = List.concat (List.mapi (fun i w -> if (not w.wtapped) && not w.sick then [ (i, w.counters) ] else []) a.bf) in
  let b_walkers = List.length (List.filter (fun w -> not w.wtapped) b.bf) in
  let ground = List.sort (fun x y -> compare y x) (List.map snd ready) in
  (* B's untapped thopters block the biggest threats: walkers first *)
  let blockers = b_walkers + b.thop_u in
  let rec drop n l = if n = 0 then l else match l with [] -> [] | _ :: r -> drop (n - 1) r in
  let all = ground @ List.init a.thop_u (fun _ -> 1) in
  let through = List.fold_left ( + ) 0 (drop blockers all) in
  let gain = if b.elixir_bf && (b.city || b.pool >= 2) then 5 else 0 in
  if through >= b.life + gain then Some (Attack (List.map fst ready, a.thop_u)) else None

(* A: grow both Walkers; attack with every Walker that B cannot profitably
   chump-convert (size <= B's blocker), and with all Thopters when B has no
   untapped Thopters. [chip] = minimum size before attacking. *)
let a_chip ~chip : policy = fun s ->
  let a = a_side s and b = b_side s in
  match s.pend with
  | Window (Main2, PA, _) when s.active = PA -> first_of [ CastWalker 1 ] s
  | Window (EndStep, PA, _) when s.active = PB -> (match pump_any s with Some m -> m | None -> Pass)
  | Window (DeclBlk, PA, _) when s.active = PB -> (match pump_any s with Some m -> m | None -> Pass)
  | ChooseAttack when lethal_attack s <> None ->
    (match lethal_attack s with Some m -> m | None -> assert false)
  | ChooseAttack ->
    let bb = b_blocker s in
    let ws = a.bf in
    let idx = List.concat (List.mapi (fun i w ->
        if (not w.wtapped) && (not w.sick) && w.counters >= chip && (w.counters <= bb || bb = 0) then [ i ] else []) ws) in
    let k = if b.thop_u = 0 then a.thop_u else 0 in
    if has (Attack (idx, k)) s then Attack (idx, k) else Attack ([], 0)
  | ChooseBlock ->
    (* B attacks: trade Thopters with B's attacking Thopters; chump-convert a
       Walker into B's Walker only if ours is smaller; otherwise no block,
       unless the damage is lethal, then block as much as possible. *)
    let ms = Reduce.moves s in
    let blocks_dmg = function
      | Block (wb, tb, tr) ->
        let atk_sizes = List.map (fun i -> (List.nth b.bf i).counters) s.cmb.atk in
        let unblocked = List.fold_left ( + ) 0 (List.mapi (fun j sz ->
            if List.nth tb j > 0 || List.exists (fun o -> o = Some j) wb then 0 else sz) atk_sizes) in
        unblocked + (s.cmb.atk_thop - tr)
      | _ -> max_int in
    let kills_b = function
      | Block (wb, _, _) ->
        List.exists2 (fun o w -> match o with
            | Some j -> w.counters >= (List.nth b.bf (List.nth s.cmb.atk j)).counters
            | None -> false) wb a.bf
      | _ -> false in
    let cost = function
      | Block (_, tb, tr) as m -> (if kills_b m then 1000 else 0) + List.fold_left ( + ) 0 tb - tr
      | _ -> max_int in
    let lethal m = blocks_dmg m >= a.life in
    let ok = List.filter (fun m -> not (lethal m)) ms in
    let pick l = List.hd (List.sort (fun x y -> compare (cost x, blocks_dmg x) (cost y, blocks_dmg y)) l) in
    if ok <> [] then pick ok else List.hd ms
  | ChooseOrder -> a_order s
  | ChooseDamage -> a_assign s
  | ChooseShuffle _ ->
    (* put Elixir as deep as possible *)
    let ms = Reduce.moves s in
    let depth = function Arrange l -> (let rec idx i = function [] -> 0 | c :: r -> if c = CElixir then i else idx (i + 1) r in idx 0 l) | _ -> 0 in
    List.hd (List.sort (fun x y -> compare (depth y) (depth x)) ms)
  | _ -> Pass

(* A: like [a_chip], but once every Walker is cast and at least [k], attack
   with all Walkers and Thopters every turn. *)
let a_all ~k : policy = fun s ->
  let a = a_side s in
  match s.pend with
  | ChooseAttack ->
    let ready = List.concat (List.mapi (fun i w -> if (not w.wtapped) && not w.sick then [ (i, w.counters) ] else []) a.bf) in
    let all_big = a.hand_w = 0 && a.bf <> [] && List.for_all (fun w -> w.counters >= k || w.wtapped) a.bf in
    if all_big || lethal_attack s <> None then Attack (List.map fst ready, a.thop_u)
    else Attack ([], 0)
  | _ -> a_chip ~chip:1000 s

(* A: grow; attack with each Walker of size >= k that is strictly bigger than
   anything B's untapped Walker can become (so B can only chump it). *)
let a_over ~k : policy = fun s ->
  let a = a_side s and b = b_side s in
  match s.pend with
  | ChooseAttack ->
    (match lethal_attack s with
     | Some m -> m
     | None ->
       let bb = b_blocker s in
       let idx = List.concat (List.mapi (fun i w ->
           if (not w.wtapped) && (not w.sick) && w.counters >= k && w.counters > bb then [ i ] else []) a.bf) in
       let k = if b.thop_u = 0 then a.thop_u else 0 in
       Attack (idx, k))
  | _ -> a_chip ~chip:1000 s

(* A: keep the first Walker at size [x] and attack with it every turn; grow
   the second; the second attacks only when B has no untapped creature or the
   attack is lethal. *)
let a_chipsmall ~x : policy = fun s ->
  let a = a_side s and b = b_side s in
  let idx_sorted () =
    (* indices of A's walkers, smallest first *)
    List.sort (fun i j -> compare (List.nth a.bf i).counters (List.nth a.bf j).counters)
      (List.init (List.length a.bf) (fun i -> i)) in
  match s.pend with
  | Window (EndStep, PA, _) when s.active = PB ->
    let cands = List.filter (fun i -> has (Pump i) s) (idx_sorted ()) in
    let ok i =
      let w = List.nth a.bf i in
      let strictly_smallest = List.length a.bf = 2 && List.for_all (fun v -> v == w || v.counters > w.counters) a.bf in
      not (strictly_smallest && w.counters >= x) in
    (match List.filter ok cands with i :: _ -> Pump i | [] -> Pass)
  | ChooseAttack ->
    (match lethal_attack s with
     | Some m -> m
     | None ->
       let b_open = List.exists (fun w -> not w.wtapped) b.bf || b.thop_u > 0 in
       let ready i = let w = List.nth a.bf i in (not w.wtapped) && not w.sick in
       let order = idx_sorted () in
       let chip = match order with i :: _ when ready i && (List.nth a.bf i).counters >= x -> [ i ] | _ -> [] in
       let rest = if b_open then [] else List.filter (fun i -> ready i && not (List.mem i chip)) order in
       let ws = List.sort compare (chip @ rest) in
       Attack (ws, if b.thop_u = 0 then a.thop_u else 0))
  | _ -> a_chip ~chip:1000 s

(* ---- B strategies ---- *)

let power_of_attack s =
  (* damage that would be dealt by A's ready creatures if nothing blocks *)
  let a = a_side s in
  List.fold_left (fun acc w -> if (not w.wtapped) && not w.sick then acc + w.counters else acc) 0 a.bf
  + a.thop_u

(* B: develop, grow the Walker, keep life up with Elixir when threatened,
   block to convert when an attacker is bigger than the Walker, chump only
   to survive, race with Thopters only when it is safe. *)
let b_smart : policy = fun s ->
  let a = a_side s and b = b_side s in
  let elixir_ready = b.elixir_bf && (b.city || b.pool >= 2) in
  match s.pend with
  | Window (Main2, PB, _) when s.active = PB -> first_of [ CastWalker 1; CastElixir ] s
  | Window (EndStep, PB, _) when s.active = PA ->
    (* prefer life when A threatens a lot next turn; otherwise grow *)
    let threat = List.fold_left (fun acc w -> acc + w.counters) 0 a.bf + a.thop_u + a.thop_t in
    if has ActElixir s && (threat >= b.life || pump_any s = None) then ActElixir
    else (match pump_any s with Some m -> m | None -> if has ActElixir s then ActElixir else Pass)
  | Window (DeclBlk, PB, _) when s.active = PA ->
    (* survive: gain life if the unblocked damage is lethal; pump a converting blocker *)
    let c = s.cmb in
    let atk_size i = (List.nth a.bf i).counters in
    let unblocked =
      List.fold_left ( + ) 0 (List.map2 (fun i bs -> if bs = [] then atk_size i else 0) c.atk c.blk)
      + (c.atk_thop - c.trades) in
    if unblocked >= b.life && has ActElixir s then ActElixir
    else begin
      (* pump our blocking walker if it then still dies (one more Thopter) or survives and kills *)
      let pumps = List.filter (fun m -> has m s)
          (List.concat_map (fun bs -> List.filter_map (function BW i -> Some (Pump i) | BT -> None) bs) c.blk) in
      match pumps with m :: _ -> m | [] -> Pass
    end
  | ChooseAttack ->
    (* race with Thopters only if A has nothing to block them and we survive A's crack-back *)
    let crack = power_of_attack { s with sideA = { a with thop_u = a.thop_u + a.thop_t } } in
    let home_blockers = List.length (List.filter (fun w -> not w.wtapped) b.bf) in
    let k = if a.thop_u = 0 && b.thop_u > 0 then
        (* keep enough Thopters home to chump A's two biggest attackers if needed *)
        let keep = if crack - 0 >= b.life + (if elixir_ready then 5 else 0) then min b.thop_u (max 0 (2 - home_blockers)) else 0 in
        b.thop_u - keep
      else 0 in
    if has (Attack ([], k)) s then Attack ([], k) else Attack ([], 0)
  | ChooseBlock ->
    let ms = Reduce.moves s in
    let c = s.cmb in
    let atk_sizes = List.map (fun i -> (List.nth a.bf i).counters) c.atk in
    let eval = function
      | Block (wb, tb, tr) ->
        let walker_on j = List.exists (fun o -> o = Some j) wb in
        let unblocked = List.fold_left ( + ) 0 (List.mapi (fun j sz -> if List.nth tb j > 0 || walker_on j then 0 else sz) atk_sizes)
                        + (c.atk_thop - tr) in
        let gain = if elixir_ready then 5 else 0 in
        let dead = unblocked >= b.life + gain in
        (* does our walker kill an A walker (bad: gives A flyers)? *)
        let kills_a = List.exists2 (fun o w -> match o with
            | Some j -> let pump = if (not w.sick) && (b.city || b.pool > 0) then 1 else 0 in
              w.counters + pump + List.nth tb j >= List.nth atk_sizes j
            | None -> false) wb b.bf in
        let converts = List.exists (fun o -> o <> None) wb && not kills_a in
        let chumps = List.fold_left ( + ) 0 tb in
        (* lexicographic: survive; avoid killing A walkers; convert; few chumps; trade thopters; little damage *)
        ((if dead then 1 else 0), (if kills_a then 1 else 0), (if converts then 0 else 1), chumps, - tr, unblocked)
      | _ -> (2, 0, 0, 0, 0, 0) in
    List.hd (List.sort (fun x y -> compare (eval x) (eval y)) ms)
  | ChooseOrder | ChooseDamage -> List.hd (Reduce.moves s)
  | _ -> List.hd (Reduce.moves s)

(* A: grow; attack every turn with every Walker of size >= k and with all
   Thopters. Below size k a Walker stays home and grows. *)
let a_grind ~k : policy = fun s ->
  let a = a_side s in
  match s.pend with
  | ChooseAttack ->
    (match lethal_attack s with
     | Some m -> m
     | None ->
       let ws = List.concat (List.mapi (fun i w ->
           if (not w.wtapped) && (not w.sick) && w.counters >= k then [ i ] else []) a.bf) in
       Attack (ws, a.thop_u))
  | _ -> a_chip ~chip:1000 s

(* B: keep the Walker exactly as big as A's biggest Walker, never kill an
   A Walker without dying too (that would hand A flyers for free), trade
   evenly, and spend spare mana on Elixir. Thopters trade with A's Thopters. *)
let b_mirror : policy = fun s ->
  let a = a_side s and b = b_side s in
  let a_max = List.fold_left (fun acc w -> max acc w.counters) 0 a.bf in
  let b_size = match b.bf with w :: _ -> w.counters | [] -> 0 in
  let elixir_ready = b.elixir_bf && (b.city || b.pool >= 2) in
  match s.pend with
  | Window (Main2, PB, _) when s.active = PB -> first_of [ CastWalker 1; CastElixir ] s
  | Window (EndStep, PB, _) when s.active = PA ->
    if b_size < a_max then (match pump_any s with Some m -> m | None -> if has ActElixir s then ActElixir else Pass)
    else if has ActElixir s then ActElixir
    else Pass
  | Window (DeclBlk, PB, _) when s.active = PA ->
    let c = s.cmb in
    let atk_size i = (List.nth a.bf i).counters in
    let unblocked =
      List.fold_left ( + ) 0 (List.map2 (fun i bs -> if bs = [] then atk_size i else 0) c.atk c.blk)
      + (c.atk_thop - c.trades) in
    if unblocked >= b.life && has ActElixir s then ActElixir
    else begin
      (* pump a blocking Walker only when the attacker is exactly one bigger:
         the pump turns "B's Walker dies" into an even trade *)
      let pumps = List.concat (List.map2 (fun i bs ->
          List.filter_map (function
              | BW j when atk_size i = (List.nth b.bf j).counters + 1 && has (Pump j) s -> Some (Pump j)
              | _ -> None) bs) c.atk c.blk) in
      match pumps with m :: _ -> m | [] -> Pass
    end
  | ChooseAttack ->
    (* everything of A's untaps before A attacks back; keep home enough
       Thopters to chump the biggest attackers so the rest is not lethal *)
    let threats = List.sort (fun x y -> compare y x)
        (List.map (fun w -> w.counters) a.bf @ List.init (a.thop_u + a.thop_t) (fun _ -> 1)) in
    let rec drop n l = if n = 0 then l else match l with [] -> [] | _ :: r -> drop (n - 1) r in
    let homew = List.length b.bf in
    let safe keep = List.fold_left ( + ) 0 (drop (keep + homew) threats) < b.life + (if b.elixir_bf || b.hand_e then 5 else 0) in
    let rec need keep = if keep >= b.thop_u || safe keep then keep else need (keep + 1) in
    let k = if a.thop_u = 0 && b.thop_u > 0 then b.thop_u - need 0 else 0 in
    if has (Attack ([], k)) s then Attack ([], k) else Attack ([], 0)
  | ChooseBlock ->
    let ms = Reduce.moves s in
    let c = s.cmb in
    let atk_sizes = List.map (fun i -> (List.nth a.bf i).counters) c.atk in
    let eval = function
      | Block (wb, tb, tr) ->
        let walker_on j = List.exists (fun o -> o = Some j) wb in
        let unblocked = List.fold_left ( + ) 0 (List.mapi (fun j sz -> if List.nth tb j > 0 || walker_on j then 0 else sz) atk_sizes)
                        + (c.atk_thop - tr) in
        let gain = if elixir_ready then 5 else 0 in
        let dead = unblocked >= b.life + gain in
        (* our Walker may only block an attacker it trades with or dies to *)
        let bad_walker = List.exists2 (fun o w -> match o with
            | Some j -> List.nth atk_sizes j < w.counters || List.nth tb j > 0
            | None -> false) wb b.bf in
        let trades_walker = List.exists2 (fun o w -> match o with
            | Some j -> List.nth atk_sizes j <= w.counters + 1
            | None -> false) wb b.bf in
        let chumps = List.fold_left ( + ) 0 tb in
        ((if dead then 1 else 0), (if bad_walker then 1 else 0), (if trades_walker then 0 else 1), chumps, - tr, unblocked)
      | _ -> (2, 0, 0, 0, 0, 0) in
    List.hd (List.sort (fun x y -> compare (eval x) (eval y)) ms)
  | _ -> List.hd (Reduce.moves s)

(* A: never hand B flyers for free. Two regimes, by B's Walker size:
   - big (>= 4): a small Walker, kept below B's Walker and at most [x],
     attacks every turn. B can only take it or kill it, which gives A
     unblockable flyers. The other Walker grows and stays home.
   - small (<= 3) or none: grow both Walkers, and attack only with Walkers of
     size >= [g]. B's chump-and-Elixir loop absorbs small attackers.
   Free hits (B has nothing untapped) and lethal attacks are always taken. *)
let a_deter ~g ~x : policy = fun s ->
  let a = a_side s and b = b_side s in
  let bsz = match b.bf with w :: _ -> w.counters | [] -> 0 in
  let b_untapped_walker = List.exists (fun w -> not w.wtapped) b.bf in
  let big_b = bsz >= 4 in
  let sorted = List.sort (fun i j -> compare (List.nth a.bf i).counters (List.nth a.bf j).counters)
      (List.init (List.length a.bf) (fun i -> i)) in
  let size i = (List.nth a.bf i).counters in
  match s.pend with
  | Window (EndStep, PA, _) when s.active = PB ->
    (* biggest first; while B's Walker is big, the smaller of two stays below it *)
    let small_ok i = match sorted with
      | [ j; _ ] when i = j -> size i < x && ((not big_b) || size i + 1 < bsz || size i >= bsz)
      | _ -> true in
    let cands = List.filter (fun i -> has (Pump i) s && small_ok i) (List.rev sorted) in
    (match cands with i :: _ -> Pump i | [] -> Pass)
  | Window (DeclBlk, PA, _) when s.active = PB -> Pass  (* a pumped blocker could kill B's Walker *)
  | ChooseAttack ->
    (match lethal_attack s with
     | Some m -> m
     | None ->
       let ready i = let w = List.nth a.bf i in (not w.wtapped) && not w.sick in
       let rdy = List.filter ready sorted in
       let free = (not b_untapped_walker) && b.thop_u = 0 in
       let ws =
         (* free hits must outpace Elixir (2.5 life a round), or growing is better *)
         if free then (if List.fold_left (fun acc i -> acc + size i) 0 rdy >= 3 then rdy else [])
         else if b_untapped_walker && big_b then
           (match rdy with
            | [ i; _ ] when size i < bsz -> if size i >= 2 then [ i ] else []
            | [ i; j ] when (size i >= bsz + 1 && size i >= 5)
                            || size j > b.life + (if b.elixir_bf then 5 else 0) ->
              (* B converts at most one Walker's worth of flyers and must
                 take or chump the other attacker every turn; or the big one
                 alone would be lethal *)
              rdy
            | _ -> [])
         else
           (* B's Elixir loop makes about one chump blocker a round, so a
               lone Walker needs Thopters attacking alongside it *)
           let g = if List.length a.bf = 1 && a.thop_u = 0 then max g 10 else g in
           (* B's loop makes under two chump blockers a round, so attack
              with every Walker B can't trade with (pumped, it is bsz + 1) *)
           List.filter (fun i -> size i >= g && size i >= bsz + 2) rdy in
       (* Thopters only meet B's Thopters, which can at most trade with them,
          and every trade costs B a chump blocker *)
       let thop = if Sys.getenv_opt "TCB_THOP" = Some "trade" || a.thop_u > b.thop_u then a.thop_u
         else if b.thop_u = 0 then a.thop_u else 0 in
       Attack (List.sort compare ws, thop))
  | _ -> a_chip ~chip:1000 s

(* [base] with a lookahead: whenever A can force a win within [d] turns (full
   minimax over B's replies), play a winning move instead. The transposition
   table is shared across calls. *)
let with_lookahead ?(mine = Reduce.moves) ~d (base : policy) : policy =
  let _, wins = Csearch.make ~mine ~theirs:Reduce.moves ~limit:5_000_000 PA in
  fun s ->
    if to_move s <> PA || not (wins s d) then base s
    else
      (* the shortest win, so that the line makes progress *)
      let rec least k = if wins s k then k else least (k + 1) in
      let k = least 0 in
      match List.find_opt (fun m -> let s' = step s m in wins s' (Search.tick s s' k)) (mine s) with
      | Some m -> m
      | None -> base s

(* B in the endgame where A has one Walker: never attack; trade Thopters with
   attacking Thopters; chump the Walker (with B's own Walker first); keep the
   Elixir loop going; gain life whenever the damage would be lethal. *)
let b_fortress : policy = fun s ->
  let b = b_side s in
  match s.pend with
  | Window (Main2, PB, _) when s.active = PB -> first_of [ CastWalker 1; CastElixir ] s
  | Window (Upkeep, PB, _) when s.active = PB -> if has ActElixir s then ActElixir else Pass
  | Window (EndStep, PB, _) when s.active = PA ->
    if has ActElixir s then ActElixir else (match pump_any s with Some m -> m | None -> Pass)
  | Window (DeclBlk, PB, _) when s.active = PA ->
    let a = a_side s in
    let c = s.cmb in
    let atk_size i = (List.nth a.bf i).counters in
    let unblocked =
      List.fold_left ( + ) 0 (List.map2 (fun i bs -> if bs = [] then atk_size i else 0) c.atk c.blk)
      + (c.atk_thop - c.trades) in
    if unblocked >= b.life && has ActElixir s then ActElixir
    else (match pump_any s with Some m -> m | None -> Pass)
  | ChooseAttack -> Attack ([], 0)
  | ChooseBlock ->
    let a = a_side s in
    let c = s.cmb in
    let atk_sizes = List.map (fun i -> (List.nth a.bf i).counters) c.atk in
    let eval = function
      | Block (wb, tb, tr) ->
        let walker_on j = List.exists (fun o -> o = Some j) wb in
        let unblocked = List.fold_left ( + ) 0 (List.mapi (fun j sz -> if List.nth tb j > 0 || walker_on j then 0 else sz) atk_sizes)
                        + (c.atk_thop - tr) in
        let chumps = List.fold_left ( + ) 0 tb in
        let gain = if b.elixir_bf && (b.city || b.pool >= 2) then 5 else 0 in
        (* survive; trade with every attacking Thopter (they are A's only
           lasting threat); chump only what life can't absorb *)
        ((if unblocked >= b.life + gain then 1 else 0), - tr, chumps, unblocked)
      | _ -> (2, 0, 0, 0) in
    List.hd (List.sort (fun x y -> compare (eval x) (eval y)) (Reduce.moves s))
  | _ -> List.hd (Reduce.moves s)
