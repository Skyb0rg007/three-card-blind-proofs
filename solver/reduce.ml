(* Heuristic move filter used only for exploration: it keeps the moves with
   sensible timing (see RULES.md for why the others are usually dominated).
   Results found with it must be re-checked against the full model. *)
open Model
open Rules

let blocking_walkers s =
  List.concat_map (List.filter_map (function BW i -> Some i | BT -> None)) s.cmb.blk

let keep s m =
  match s.pend with
  | Window (st, p, _) ->
    let ap = p = s.active in
    let pool = (get_side p s).pool in
    (match m with
     | Pass -> true
     | CastWalker x -> x = 1 && st = Main2
     | CastElixir -> st = Main2
     | Pump i ->
       if ap then st = Main2 && pool > 0
       else st = EndStep || (st = DeclBlk && List.mem i (blocking_walkers s))
     | ActElixir ->
       if ap then st = Upkeep else st = EndStep || st = DeclBlk
     | _ -> true)
  | _ -> true

let moves s = List.filter (keep s) (Rules.moves s)

(* A smaller move set for player A, for deeper win searches. *)
let a_macro s =
  let ms = moves s in
  if to_move s <> PA then ms
  else
    let a = get_side PA s in
    let sizes = List.map (fun w -> w.counters) a.bf in
    let ready = List.concat (List.mapi (fun i w -> if (not w.wtapped) && not w.sick then [ i ] else []) a.bf) in
    let by_size l = List.sort (fun i j -> compare (List.nth sizes i) (List.nth sizes j)) l in
    match s.pend with
    | ChooseAttack ->
      let sorted = by_size ready in
      let sets =
        [ []; ready ]
        @ (match sorted with i :: _ :: _ -> [ [ i ] ] | _ -> [])
        @ (match List.rev sorted with i :: _ :: _ -> [ [ i ] ] | _ -> [])
      in
      let sets = List.sort_uniq compare (List.map (List.sort compare) sets) in
      List.concat_map (fun ws -> List.sort_uniq compare [ Attack (ws, 0); Attack (ws, a.thop_u) ]) sets
      |> List.filter (fun m -> List.mem m ms)
    | Window (EndStep, PA, _) when s.active = PB ->
      (* pump the biggest pumpable walker first; or stop *)
      let pumps = List.filter_map (function Pump i -> Some i | _ -> None) ms in
      (match List.rev (by_size pumps) with
       | i :: _ -> [ Pump i; Pass ]
       | [] -> [ Pass ])
    | ChooseOrder ->
      let front_t = Order (List.map (fun bs -> List.filter (( = ) BT) bs @ List.filter (( <> ) BT) bs) s.cmb.blk) in
      let front_w = Order (List.map (fun bs -> List.filter (( <> ) BT) bs @ List.filter (( = ) BT) bs) s.cmb.blk) in
      List.sort_uniq compare [ front_t; front_w ]
    | ChooseDamage ->
      (match ms with [] -> [] | [ m ] -> [ m ] | m :: r -> List.sort_uniq compare [ m; List.nth r (List.length r - 1) ])
    | _ -> ms

(* A smaller move set for player B, for deeper searches of A's wins. Blocks:
   per attacking Walker, no block / B's Walker / one chump Thopter / enough
   Thopters to kill it; Thopter trades: none or as many as possible. *)
let b_macro s =
  let ms = moves s in
  if to_move s <> PB then ms
  else
    match s.pend with
    | ChooseBlock ->
      let a = get_side PA s and b = get_side PB s in
      let c = s.cmb in
      let sizes = List.map (fun i -> (List.nth a.bf i).counters) c.atk in
      let keep = function
        | Block (wb, tb, tr) ->
          let n_t = List.fold_left ( + ) 0 tb in
          let max_tr = min c.atk_thop (b.thop_u - n_t) in
          List.for_all2 (fun sz k -> k = 0 || k = 1 || k = sz) sizes tb
          && (tr = 0 || tr = max_tr)
          && List.length (List.filter (fun o -> o <> None) wb) <= 1
        | _ -> true
      in
      List.filter keep ms
    | ChooseAttack ->
      let b = get_side PB s in
      List.filter (function Attack (_, k) -> k = 0 || k = b.thop_u | _ -> true) ms
    | ChooseDamage ->
      (match ms with [] -> [] | [ m ] -> [ m ] | m :: r -> List.sort_uniq compare [ m; List.nth r (List.length r - 1) ])
    | _ -> ms
