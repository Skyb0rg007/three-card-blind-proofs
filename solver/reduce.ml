(* Heuristic move filter used only for exploration: it keeps the moves with
   sensible timing (see spec/RULES.md for why the others are usually dominated).
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
       else
         (* after blocks: a blocking Walker, or any Walker with mana left
            over (it would empty before the end step) *)
         st = EndStep || (st = DeclBlk && (List.mem i (blocking_walkers s) || pool > 0))
     | ActElixir ->
       if ap then st = Upkeep else st = EndStep || st = DeclBlk
     | _ -> true)
  | _ -> true

let moves s = List.filter (keep s) (Rules.moves s)

(* The most Thopters a player may hold back from an attack under macro
   rule [r], if it is an attack rule: atk holds none back (no Thopters or
   all of them), atkN at most N. *)
let held_of r =
  if r = "atk" then Some 0
  else if String.length r > 3 && String.sub r 0 3 = "atk" then int_of_string_opt (String.sub r 3 (String.length r - 3))
  else None

let rules_of var default =
  match Sys.getenv_opt var with
  | None -> default
  | Some l -> List.filter (( <> ) "") (String.split_on_char ',' l)

(* A smaller move set for player A, for deeper win searches. TCB_AMACRO
   lists the restrictions that apply (default all): atk or atkN (attacking
   Thopters), pump (at B's end step only the biggest Walker), order and dmg
   (two damage orders, two damage assignments). *)
let a_macro_rules = rules_of "TCB_AMACRO" [ "atk"; "pump"; "order"; "dmg" ]
let a_held_back = List.find_map held_of a_macro_rules

let a_macro s =
  let ms = moves s in
  let on r = List.mem r a_macro_rules in
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
      let ks = match a_held_back with
        | Some n -> List.sort_uniq compare (0 :: List.init (n + 1) (fun j -> max 0 (a.thop_u - j)))
        | None -> List.init (a.thop_u + 1) Fun.id in
      List.concat_map (fun ws -> List.map (fun k -> Attack (ws, k)) ks) sets
      |> List.filter (fun m -> List.mem m ms)
    | Window (EndStep, PA, _) when s.active = PB && on "pump" ->
      (* pump the biggest pumpable walker first; or stop *)
      let pumps = List.filter_map (function Pump i -> Some i | _ -> None) ms in
      (match List.rev (by_size pumps) with
       | i :: _ -> [ Pump i; Pass ]
       | [] -> [ Pass ])
    | ChooseOrder when on "order" ->
      let front_t = Order (List.map (fun bs -> List.filter (( = ) BT) bs @ List.filter (( <> ) BT) bs) s.cmb.blk) in
      let front_w = Order (List.map (fun bs -> List.filter (( <> ) BT) bs @ List.filter (( = ) BT) bs) s.cmb.blk) in
      List.sort_uniq compare [ front_t; front_w ]
    | ChooseDamage when on "dmg" ->
      (match ms with [] -> [] | [ m ] -> [ m ] | m :: r -> List.sort_uniq compare [ m; List.nth r (List.length r - 1) ])
    | _ -> ms

(* A smaller move set for player B, for deeper searches of A's wins. Blocks:
   per attacking Walker, no block / B's Walker / one chump Thopter / enough
   Thopters to kill it; Thopter trades: none or as many as possible.
   TCB_BMACRO lists the restrictions that apply (default all): blk (blocks),
   tr (Thopter trades), atk or atkN (attacking Thopters), dmg (damage
   assignment). *)
let b_macro_rules = rules_of "TCB_BMACRO" [ "blk"; "tr"; "atk"; "dmg" ]
let held_back = List.find_map held_of b_macro_rules

let b_macro s =
  let ms = moves s in
  let on r = List.mem r b_macro_rules in
  if to_move s <> PB then ms
  else
    match s.pend with
    | ChooseBlock when on "blk" || on "tr" ->
      let a = get_side PA s and b = get_side PB s in
      let c = s.cmb in
      let sizes = List.map (fun i -> (List.nth a.bf i).counters) c.atk in
      let keep = function
        | Block (wb, tb, tr) ->
          let n_t = List.fold_left ( + ) 0 tb in
          let max_tr = min c.atk_thop (b.thop_u - n_t) in
          ((not (on "blk"))
           || (List.for_all2 (fun sz k -> k = 0 || k = 1 || k = sz) sizes tb
               && List.length (List.filter (fun o -> o <> None) wb) <= 1))
          && ((not (on "tr")) || tr = 0 || tr = max_tr)
        | _ -> true
      in
      List.filter keep ms
    | ChooseAttack when held_back <> None ->
      let b = get_side PB s and n = Option.get held_back in
      List.filter (function Attack (_, k) -> k = 0 || k >= b.thop_u - n | _ -> true) ms
    | ChooseDamage when on "dmg" ->
      (match ms with [] -> [] | [ m ] -> [ m ] | m :: r -> List.sort_uniq compare [ m; List.nth r (List.length r - 1) ])
    | _ -> ms
