(* Human-readable strategies (STRATEGY.md): rule strategies for the three
   results, and the tools that check them. Analysis only; nothing here is
   trusted or used by the proofs.

   - [strat-closure MODE RULE OUT] follows the check of the opening through
     a solver table, as the exports do, with the protagonist playing RULE:
     at each of its nodes it takes RULE's move if that move works by the
     table, and otherwise logs the node as an exception and takes the first
     move that works. The opponent plays every legal move. OUT gets one line
     per protagonist decision node (features, RULE's moves, the moves that
     work). MODE is bfirst (B's ranked win, B first), bsafe (B safe, A
     first) or asafe (A safe, A first, lines c + b n). Only nodes where
     some move fails are logged; TCB_DUMP=all logs every node (slow), and
     TCB_DUMP_PEND=attack (say) only nodes of that kind. TCB_TABLES is
     the tables directory (default tables), TCB_LIFE B's starting life
     for bfirst (default 20).
   - [strat-fix MODE RULE DIR] solves the game with B restricted to
     RULE's moves (Fix, every legal A move, or the exploration filter with
     TCB_AFILTER=1; B's Walker cap TCB_T): the rule's own value at the
     opening, independent of the tables.
   - [strat-pv asafe RULE LIFE TURNS] prints a principal variation of the
     A-safe table, A playing RULE where it keeps the slack.

   The rules themselves are below ([rules]). *)
open Model

let tables = try Sys.getenv "TCB_TABLES" with Not_found -> "tables"
let tbl name = Filename.concat tables name

(* ** Compact printing *)

let ints l = String.concat "," (List.map string_of_int l)

let mv = function
  | Pass -> "P"
  | Pump i -> Printf.sprintf "U%d" i
  | ActElixir -> "EA"
  | CastWalker x -> Printf.sprintf "W%d" x
  | CastElixir -> "EC"
  | Attack (ws, k) -> Printf.sprintf "A[%s]+%d" (ints ws) k
  | Block (wb, tb, tr) ->
    Printf.sprintf "B[%s][%s]%d" (String.concat "," (List.map (function None -> "-" | Some i -> string_of_int i) wb))
      (ints tb) tr
  | Order os -> "O" ^ String.concat "|" (List.map (fun bs -> String.concat "" (List.map Show.blocker bs)) os)
  | Assign js -> Printf.sprintf "D[%s]" (ints js)
  | Arrange l -> "R" ^ String.concat "" (List.map Show.card l)

let wk w = Printf.sprintf "%d%s%s" w.counters (if w.wtapped then "t" else "") (if w.sick then "s" else "")

let sd_str s =
  Printf.sprintf "l%d c%s p%d h%d%s w[%s]%s t%d+%d lib%s g%d" s.life (if s.city then "U" else "T") s.pool s.hand_w
    (if s.hand_e then "E" else "") (String.concat "," (List.map wk s.bf)) (if s.elixir_bf then "E" else "")
    s.thop_u s.thop_t (String.concat "" (List.map Show.card s.library)) s.gy_w

let pend_str = function
  | Window (st, p, passed) -> Printf.sprintf "%s/%s%s" (Show.stepk st) (Show.player p) (if passed then "*" else "")
  | ChooseAttack -> "attack"
  | ChooseBlock -> "block"
  | ChooseOrder -> "order"
  | ChooseDamage -> "damage"
  | ChooseShuffle (st, p, _) -> Printf.sprintf "shuffle/%s/%s" (Show.stepk st) (Show.player p)
  | Over w -> "over" ^ Show.player w

let st_str s =
  Printf.sprintf "act=%s %s | A %s | B %s%s" (Show.player s.active) (pend_str s.pend) (sd_str s.sideA) (sd_str s.sideB)
    (if s.cmb.atk = [] && s.cmb.atk_thop = 0 then ""
     else Printf.sprintf " | cmb atk[%s]+%d blk[%s] tr%d" (ints s.cmb.atk) s.cmb.atk_thop
         (String.concat "|" (List.map (fun bs -> String.concat "" (List.map Show.blocker bs)) s.cmb.blk)) s.cmb.trades)

(* ** Rules

   A rule is a list of filters, each one plain-language rule: given the
   state and the moves still allowed, the moves the rule allows. A filter
   that allows none of them doesn't apply, and leaves the moves as they
   were. A rule is named by its filters, joined with "+". *)

type filter = state -> move list -> move list

let side p s = get_side p s
let walker sd = match sd.bf with [ w ] -> Some w | _ -> None
let ready w = (not w.wtapped) && not w.sick
let mana sd = sd.pool + if sd.city then 2 else 0
let only m ms = if List.mem m ms then [ m ] else []
let first_in l ms = match List.filter (fun m -> List.mem m ms) l with m :: _ -> [ m ] | [] -> []

let no_block s =
  let d = side (opp s.active) s in
  Block (List.map (fun _ -> None) d.bf, List.map (fun _ -> 0) s.cmb.atk, 0)

let own p s = s.active = p
let prio p s = match s.pend with Window (_, q, _) -> q = p | _ -> false
let step_is st s = match s.pend with Window (st', _, _) -> st' = st | _ -> false
let is_main_now s = match s.pend with Window ((Main1 | Main2), _, _) -> true | _ -> false

let filters : (string * filter) list ref = ref []
let def name f = filters := (name, f) :: !filters

(* B: cast the Walker (X = 1) whenever you can. *)
let () = def "cw" (fun s ms -> if prio PB s && own PB s then only (CastWalker 1) ms else [])
(* B: cast Elixir whenever you can. *)
let () = def "ce" (fun s ms -> if prio PB s && own PB s then only CastElixir ms else [])
(* B: in main phase 2, mana left over and an untapped Walker: pump it. *)
let () = def "pm" (fun s ms -> if prio PB s && own PB s && step_is Main2 s && (side PB s).pool > 0 then only (Pump 0) ms else [])
(* B: attack with every untapped Thopter or none. *)
let () = def "ta" (fun s ms ->
    match s.pend with
    | ChooseAttack when own PB s -> List.filter (function Attack (_, k) -> k = 0 || k = (side PB s).thop_u | _ -> false) ms
    | _ -> [])
(* B: attack with every untapped Thopter. *)
let () = def "tall" (fun s ms ->
    match s.pend with
    | ChooseAttack when own PB s -> List.filter (function Attack (_, k) -> k = (side PB s).thop_u | _ -> false) ms
    | _ -> [])
(* B: attack with the Walker whenever it can. *)
let () = def "wall" (fun s ms ->
    match s.pend with
    | ChooseAttack when own PB s -> List.filter (function Attack (ws, _) -> ws <> [] | _ -> false) ms
    | _ -> [])
(* B: on A's turn, at the end step: activate Elixir if you can, else pump. *)
let () = def "eot" (fun s ms -> if prio PB s && (not (own PB s)) && step_is EndStep s then first_in [ ActElixir; Pump 0 ] ms else [])
(* B: on A's turn, do nothing before the end step except after blocks. *)
let () = def "quiet" (fun s ms ->
    match s.pend with
    | Window ((Upkeep | DrawStep | Main1 | BeginCombat | DeclAtk | EndCombat | Main2), PB, _) when own PA s -> only Pass ms
    | _ -> [])
(* B: on your own turn, activate Elixir only in your upkeep. *)
let () = def "ne" (fun s ms -> if prio PB s && own PB s && not (step_is Upkeep s) then List.filter (( <> ) ActElixir) ms else [])
(* B: never activate Elixir in your upkeep. *)
let () = def "nu" (fun s ms -> if prio PB s && own PB s && step_is Upkeep s then List.filter (( <> ) ActElixir) ms else [])
(* B: never block. *)
let () = def "nb" (fun s ms -> match s.pend with ChooseBlock when own PA s -> only (no_block s) ms | _ -> [])

(* B first, a whole strategy (version 2). *)
let () = def "b2" (fun s ms ->
    let b = side PB s in
    let wk = walker b in
    match s.pend with
    | Window (st, PB, _) when own PB s ->
      (match st with
       | Main2 ->
         if b.hand_w > 0 && List.mem (CastWalker 1) ms then [ CastWalker 1 ]
         else if b.hand_e && List.mem CastElixir ms then
           (match wk with Some w when ready w && b.city -> only (Pump 0) ms | _ -> [ CastElixir ])
         else if b.pool > 0 then first_in [ Pump 0; Pass ] ms
         else only Pass ms
       | _ -> only Pass ms)
    | Window (EndStep, PB, _) -> first_in [ ActElixir; Pump 0; Pass ] ms
    | Window (_, PB, _) -> only Pass ms
    | ChooseAttack when own PB s ->
      let wa = match wk with Some w -> ready w && not b.hand_e | None -> false in
      only (Attack ((if wa then [ 0 ] else []), b.thop_u)) ms
    | ChooseBlock when own PA s -> only (no_block s) ms
    | _ -> [])

(* B's Walker cap: B never pumps its Walker above [bcap] counters
   (TCB_BCAP, default 4, the B-first certificate's cap). *)
let bcap = try int_of_string (Sys.getenv "TCB_BCAP") with Not_found -> 4
let can_pump_b s = match walker (side PB s) with Some w -> ready w && w.counters < bcap | None -> false

(* B's main phase: cast the Walker (X = 1) if it is in hand; else cast
   Elixir if it is in hand, pumping the Walker first if it is untapped and
   City is too; else spend mana left over on a pump. Pass otherwise. *)
let () = def "bmain" (fun s ms ->
    let b = side PB s in
    match s.pend with
    | Window (Main2, PB, _) when own PB s ->
      if b.hand_w > 0 && List.mem (CastWalker 1) ms then [ CastWalker 1 ]
      else if b.hand_e && List.mem CastElixir ms then
        (if can_pump_b s && b.city then only (Pump 0) ms else [ CastElixir ])
      else if b.pool > 0 && can_pump_b s then first_in [ Pump 0; Pass ] ms
      else only Pass ms
    | Window (Main1, PB, _) when own PB s -> only Pass ms
    | _ -> [])

(* B on A's turn: at the end step activate Elixir if you can, else pump
   the Walker (up to the cap). *)
let () = def "beot" (fun s ms ->
    match s.pend with
    | Window (EndStep, PB, _) when own PA s ->
      if List.mem ActElixir ms then [ ActElixir ] else if can_pump_b s then first_in [ Pump 0; Pass ] ms else only Pass ms
    | _ -> [])

(* As [beot], but an untapped Walker (one that stayed home) is pumped
   rather than Elixir activated. *)
let () = def "beot2" (fun s ms ->
    match s.pend with
    | Window (EndStep, PB, _) when own PA s ->
      if can_pump_b s then first_in [ Pump 0; Pass ] ms
      else if List.mem ActElixir ms then [ ActElixir ] else only Pass ms
    | _ -> [])

(* B passes at every other window (no Elixir in upkeep, no pumps before
   blocks, no instant-speed tricks in combat). *)
let () = def "bquiet" (fun s ms ->
    match s.pend with
    | Window (st, PB, _) when not (st = EndStep && own PA s) && not (st = Main2 && own PB s) -> only Pass ms
    | _ -> [])

(* B attacks with every untapped Thopter, and with the Walker unless
   Elixir is in hand (then it stays home to be pumped). *)
let () = def "batk_he" (fun s ms ->
    match s.pend with
    | ChooseAttack when own PB s ->
      let b = side PB s in
      let wa = match walker b with Some w -> ready w && not b.hand_e | None -> false in
      only (Attack ((if wa then [ 0 ] else []), b.thop_u)) ms
    | _ -> [])

(* B's blocks: the Walker, if untapped, blocks A's biggest attacking
   Walker; Thopters block attacking Thopters one for one; and while the
   damage still coming is lethal, a Thopter chump-blocks the biggest
   unblocked attacking Walker. *)
let b_block s =
  let a = side PA s and b = side PB s in
  let c = s.cmb in
  let pw = List.map (fun i -> (List.nth a.bf i).counters) c.atk in
  let n = List.length pw in
  let order = List.sort (fun (_, x) (_, y) -> compare y x) (List.mapi (fun j p -> (j, p)) pw) in
  let wblk = match walker b, order with Some w, (j, _) :: _ when not w.wtapped -> Some j | _ -> None in
  let tb = Array.make n 0 in
  let thops = ref b.thop_u in
  let tr = min c.atk_thop !thops in
  thops := !thops - tr;
  let dmg () =
    List.fold_left (fun acc (j, p) -> if Some j = wblk || tb.(j) > 0 then acc else acc + p) 0 order + (c.atk_thop - tr) in
  List.iter (fun (j, _) -> if Some j <> wblk && !thops > 0 && dmg () >= b.life then (tb.(j) <- 1; decr thops)) order;
  Block ((match b.bf with [] -> [] | _ -> [ wblk ]), Array.to_list tb, tr)

let () = def "bblock" (fun s ms -> match s.pend with ChooseBlock when own PA s -> only (b_block s) ms | _ -> [])

(* As [bblock], but when the attack is lethal, Thopters chump-block A's
   biggest unblocked Walkers first (a chump stops more than a trade), and
   only the Thopters left trade with A's Thopters. *)
let b_block2 s =
  let a = side PA s and b = side PB s in
  let c = s.cmb in
  let pw = List.map (fun i -> (List.nth a.bf i).counters) c.atk in
  let n = List.length pw in
  let order = List.sort (fun (_, x) (_, y) -> compare y x) (List.mapi (fun j p -> (j, p)) pw) in
  let wblk = match walker b, order with Some w, (j, _) :: _ when not w.wtapped -> Some j | _ -> None in
  let tb = Array.make n 0 in
  let thops = ref b.thop_u in
  let tr = ref 0 in
  let dmg () =
    List.fold_left (fun acc (j, p) -> if Some j = wblk || tb.(j) > 0 then acc else acc + p) 0 order + (c.atk_thop - !tr) in
  List.iter (fun (j, p) -> if Some j <> wblk && !thops > 0 && p > 1 && dmg () >= b.life then (tb.(j) <- 1; decr thops)) order;
  tr := min c.atk_thop !thops;
  Block ((match b.bf with [] -> [] | _ -> [ wblk ]), Array.to_list tb, !tr)

let () = def "bblock2" (fun s ms -> match s.pend with ChooseBlock when own PA s -> only (b_block2 s) ms | _ -> [])

(* B attacks with every untapped Thopter, and with the Walker unless
   Elixir is in hand and A has an untapped Walker to block with (then it
   stays home to be pumped). *)
let a_untapped s = List.exists (fun w -> not w.wtapped) (side PA s).bf
let () = def "batk3" (fun s ms ->
    match s.pend with
    | ChooseAttack when own PB s ->
      let b = side PB s in
      let wa = match walker b with Some w -> ready w && not (b.hand_e && a_untapped s) | None -> false in
      only (Attack ((if wa then [ 0 ] else []), b.thop_u)) ms
    | _ -> [])

(* B attacks with the Walker whenever it can, and with every untapped
   Thopter except the fewest that must stay home: enough to chump-block
   A's biggest Walkers so that an all-out attack by A next turn (every
   Walker and Thopter A has) is not lethal. *)
let keep_home s =
  let a = side PA s and b = side PB s in
  let ws = List.sort (fun x y -> compare y x) (List.map (fun w -> w.counters) a.bf) in
  let total = List.fold_left ( + ) 0 ws + a.thop_u + a.thop_t in
  let rec go k dmg ws = if dmg < b.life || k >= b.thop_u then k else
      match ws with x :: r -> go (k + 1) (dmg - x) r | [] -> go (k + 1) (dmg - 1) [] in
  go 0 total ws

let () = def "batk4" (fun s ms ->
    match s.pend with
    | ChooseAttack when own PB s ->
      let b = side PB s in
      let wa = match walker b with Some w -> ready w | None -> false in
      only (Attack ((if wa then [ 0 ] else []), b.thop_u - keep_home s)) ms
    | _ -> [])

(* As [batk4], but a 1/1 Walker stays home while Elixir is in hand and
   A has a Walker (B pumps it and casts Elixir instead). *)
let () = def "batk5" (fun s ms ->
    match s.pend with
    | ChooseAttack when own PB s ->
      let b = side PB s in
      let wa = match walker b with
        | Some w -> ready w && not (b.hand_e && w.counters = 1 && (side PA s).bf <> [])
        | None -> false in
      only (Attack ((if wa then [ 0 ] else []), b.thop_u - keep_home s)) ms
    | _ -> [])

(* B in A's combat, after blocks: if B's Walker blocks an attacker that
   will kill it, pump it (one more Thopter when it dies); if the
   unblocked damage would kill B, activate Elixir. *)
let unblocked_dmg s =
  let a = side PA s in
  let c = s.cmb in
  let ws = List.mapi (fun j i -> (j, (List.nth a.bf i).counters)) c.atk in
  List.fold_left (fun acc (j, p) -> if List.nth c.blk j = [] then acc + p else acc) 0 ws + (c.atk_thop - c.trades)

let () = def "bcombat" (fun s ms ->
    match s.pend with
    | Window (DeclBlk, PB, _) when own PA s ->
      let a = side PA s and b = side PB s in
      let c = s.cmb in
      let doomed = match walker b with
        | Some w when not w.wtapped ->
          List.exists (fun (j, i) -> List.mem (BW 0) (List.nth c.blk j) && (List.nth a.bf i).counters >= w.counters)
            (List.mapi (fun j i -> (j, i)) c.atk)
        | _ -> false in
      if unblocked_dmg s >= b.life && List.mem ActElixir ms then [ ActElixir ]
      else if doomed then only (Pump 0) ms
      else []
    | _ -> [])

(* B in A's combat, after blocks: if the unblocked damage would kill B,
   activate Elixir. *)
let () = def "bsave" (fun s ms ->
    match s.pend with
    | Window (DeclBlk, PB, _) when own PA s && unblocked_dmg s >= (side PB s).life -> only ActElixir ms
    | _ -> [])

(* As [batk5], with two changes: the Thopters kept home count Elixir's
   5 life when Elixir is on the battlefield, and the 1/1 stays home only
   if A has an untapped Walker. *)
let keep_home2 s =
  let a = side PA s and b = side PB s in
  let life = b.life + if b.elixir_bf then 5 else 0 in
  let ws = List.sort (fun x y -> compare y x) (List.map (fun w -> w.counters) a.bf) in
  let total = List.fold_left ( + ) 0 ws + a.thop_u + a.thop_t in
  let rec go k dmg ws = if dmg < life || k >= b.thop_u then k else
      match ws with x :: r -> go (k + 1) (dmg - x) r | [] -> go (k + 1) (dmg - 1) [] in
  go 0 total ws

let () = def "batk6" (fun s ms ->
    match s.pend with
    | ChooseAttack when own PB s ->
      let b = side PB s in
      let wa = match walker b with
        | Some w -> ready w && not (b.hand_e && w.counters = 1 && a_untapped s)
        | None -> false in
      only (Attack ((if wa then [ 0 ] else []), b.thop_u - keep_home2 s)) ms
    | _ -> [])

(* Every untapped Thopter attacks; the Walker too, except a 1/1 with
   Elixir in hand while A has an untapped Walker. *)
let () = def "batk7" (fun s ms ->
    match s.pend with
    | ChooseAttack when own PB s ->
      let b = side PB s in
      let wa = match walker b with
        | Some w -> ready w && not (b.hand_e && w.counters = 1 && a_untapped s)
        | None -> false in
      only (Attack ((if wa then [ 0 ] else []), b.thop_u)) ms
    | _ -> [])

(* As [batk_he], but the Thopters keep home enough chump blockers that
   A's all-out attack next turn is not lethal (counting Elixir's 5 life
   when Elixir is on the battlefield). *)
let () = def "batk8" (fun s ms ->
    match s.pend with
    | ChooseAttack when own PB s ->
      let b = side PB s in
      let wa = match walker b with Some w -> ready w && not b.hand_e | None -> false in
      only (Attack ((if wa then [ 0 ] else []), b.thop_u - keep_home2 s)) ms
    | _ -> [])

(* As [bmain], but Elixir is cast first, and leftover mana then pumps. *)
let () = def "bmain2" (fun s ms ->
    let b = side PB s in
    match s.pend with
    | Window (Main2, PB, _) when own PB s ->
      if b.hand_w > 0 && List.mem (CastWalker 1) ms then [ CastWalker 1 ]
      else if b.hand_e && List.mem CastElixir ms then [ CastElixir ]
      else if b.pool > 0 && can_pump_b s then first_in [ Pump 0; Pass ] ms
      else only Pass ms
    | Window (Main1, PB, _) when own PB s -> only Pass ms
    | _ -> [])

(* As [bmain2], but leftover mana is not spent on a pump: the Walker
   stays untapped for A's turn and grows in A's end step instead. *)
let () = def "bmain3" (fun s ms ->
    let b = side PB s in
    match s.pend with
    | Window (Main2, PB, _) when own PB s ->
      if b.hand_w > 0 && List.mem (CastWalker 1) ms then [ CastWalker 1 ]
      else if b.hand_e && List.mem CastElixir ms then [ CastElixir ]
      else only Pass ms
    | Window (Main1, PB, _) when own PB s -> only Pass ms
    | _ -> [])

(* B's upkeep, when A has no Walkers: with B's Walker in the graveyard,
   activate Elixir. *)
let () = def "bup2" (fun s ms ->
    let b = side PB s in
    match s.pend with
    | Window (Upkeep, PB, _) when own PB s && b.gy_w > 0 && b.bf = [] && (side PA s).bf = [] -> only ActElixir ms
    | _ -> [])

(* B's upkeep: with the Walker in the graveyard and Elixir on the
   battlefield, activate Elixir (the Walker comes back into the library
   before the draw). *)
let () = def "bup" (fun s ms ->
    let b = side PB s in
    match s.pend with
    | Window (Upkeep, PB, _) when own PB s && b.gy_w > 0 && b.bf = [] -> only ActElixir ms
    | _ -> [])

(* Counterfactual: B never casts or activates Elixir. *)
let () = def "noel" (fun _ ms -> List.filter (fun m -> m <> CastElixir && m <> ActElixir) ms)

(* ** A's rules (A first, A safe) *)

(* A's own turn: cast a Walker (X = 1) in main phase 2 if one is in
   hand; pass at every other window of A's own turn. *)
let () = def "amain" (fun s ms ->
    match s.pend with
    | Window (Main2, PA, _) when own PA s -> first_in [ CastWalker 1; Pass ] ms
    | Window (_, PA, _) when own PA s -> only Pass ms
    | _ -> [])

(* A on B's turn: pass until B's end step; there pump untapped Walkers,
   the biggest first, while mana lasts. *)
let biggest_ready sd =
  let best = ref None in
  List.iteri (fun i w -> if ready w then match !best with
      | Some (_, c) when c >= w.counters -> ()
      | _ -> best := Some (i, w.counters)) sd.bf;
  Option.map fst !best

let () = def "apump" (fun s ms ->
    match s.pend with
    | Window (EndStep, PA, _) when own PB s ->
      (match biggest_ready (side PA s) with Some i -> first_in [ Pump i; Pass ] ms | None -> only Pass ms)
    | Window (_, PA, _) when own PB s -> only Pass ms
    | _ -> [])

(* A on B's turn: pump the biggest untapped Walker as soon as B's combat
   is over (end of combat, B's main 2 or end step). *)
let () = def "apump2" (fun s ms ->
    match s.pend with
    | Window ((EndCombat | Main2 | EndStep), PA, _) when own PB s ->
      (match biggest_ready (side PA s) with Some i -> first_in [ Pump i; Pass ] ms | None -> only Pass ms)
    | Window (_, PA, _) when own PB s -> only Pass ms
    | _ -> [])

(* A never blocks. *)
let () = def "anb" (fun s ms -> match s.pend with ChooseBlock when own PB s -> only (no_block s) ms | _ -> [])

(* A attacks with every untapped Walker and Thopter when B has no
   untapped Walker (nothing that can block a Walker); else with
   Thopters only. *)
let b_can_block s = let b = side PB s in List.exists (fun w -> not w.wtapped) b.bf
let ready_idx sd = List.concat (List.mapi (fun i w -> if ready w then [ i ] else []) sd.bf)

let () = def "aatk" (fun s ms ->
    match s.pend with
    | ChooseAttack when own PA s ->
      let a = side PA s in
      only (Attack ((if b_can_block s then [] else ready_idx a), a.thop_u)) ms
    | _ -> [])

(* As [aatk], but keep the biggest Walker home unless every other
   Walker is tapped or B is within reach of all of them together. *)
let () = def "aatk1" (fun s ms ->
    match s.pend with
    | ChooseAttack when own PA s ->
      let a = side PA s and b = side PB s in
      let rd = ready_idx a in
      let ws =
        if b_can_block s then []
        else
          let tot = List.fold_left (fun acc i -> acc + (List.nth a.bf i).counters) 0 rd + a.thop_u in
          match rd with
          | [] | [ _ ] -> rd
          | _ when tot >= b.life -> rd
          | _ -> (match biggest_ready a with Some j -> List.filter (( <> ) j) rd | None -> rd) in
      only (Attack (ws, a.thop_u)) ms
    | _ -> [])

(* A attacks only when B has no untapped Walker, and then with its
   smallest untapped Walker if that one has 3+ counters (the other
   stays home to be pumped on B's turn), plus every untapped Thopter. *)
let () = def "aatk2" (fun s ms ->
    match s.pend with
    | ChooseAttack when own PA s ->
      let a = side PA s in
      let small = List.fold_left (fun acc i -> match acc with
          | Some j when (List.nth a.bf j).counters <= (List.nth a.bf i).counters -> acc
          | _ -> Some i) None (ready_idx a) in
      let ws = match small with
        | Some i when (not (b_can_block s)) && (List.nth a.bf i).counters >= 3 -> [ i ]
        | _ -> [] in
      only (Attack (ws, a.thop_u)) ms
    | _ -> [])

(* A's blocks: when B attacks with a Walker of 4+ counters, bigger than
   each of A's untapped Walkers, A's smallest untapped Walker blocks it;
   otherwise no Walker blocks. A's Thopters block attacking Thopters one
   for one. *)
let a_block s =
  let a = side PA s and b = side PB s in
  let c = s.cmb in
  let unt = List.concat (List.mapi (fun i w -> if w.wtapped then [] else [ (i, w.counters) ]) a.bf) in
  let wb = List.map (fun _ -> None) a.bf in
  let wb = match c.atk, unt with
    | [ j ], _ :: _ ->
      let p = (List.nth b.bf j).counters in
      if p >= 4 && List.for_all (fun (_, x) -> x < p) unt then
        let i, _ = List.fold_left (fun (bi, bx) (i, x) -> if x < bx then (i, x) else (bi, bx)) (List.hd unt) unt in
        List.mapi (fun k o -> if k = i then Some 0 else o) wb
      else wb
    | _ -> wb in
  Block (wb, List.map (fun _ -> 0) c.atk, min c.atk_thop a.thop_u)

let () = def "ablk" (fun s ms -> match s.pend with ChooseBlock when own PB s -> only (a_block s) ms | _ -> [])

(* A in B's combat, after blocks: pump a blocking Walker that will die
   (one more Thopter). *)
let () = def "apblk" (fun s ms ->
    match s.pend with
    | Window (DeclBlk, PA, _) when own PB s ->
      let a = side PA s in
      let blockers = List.concat_map (List.filter_map (function BW i -> Some i | BT -> None)) s.cmb.blk in
      (match List.filter (fun i -> not (List.nth a.bf i).wtapped) blockers with
       | i :: _ -> only (Pump i) ms
       | [] -> [])
    | _ -> [])

(* A's attacks: if every untapped Walker of A's is bigger than B's
   Walker (or B has none), all of them attack; else, with two untapped
   Walkers the bigger of which has 3+ counters, the smaller one attacks;
   else none. Every untapped Thopter attacks. *)
let () = def "aatk3" (fun s ms ->
    match s.pend with
    | ChooseAttack when own PA s ->
      let a = side PA s in
      let bw = match walker (side PB s) with Some w -> w.counters | None -> 0 in
      let rd = ready_idx a in
      let c i = (List.nth a.bf i).counters in
      let ws =
        if rd <> [] && List.for_all (fun i -> c i > bw) rd then rd
        else match rd with
          | [ i; j ] when max (c i) (c j) >= 3 -> [ (if c i <= c j then i else j) ]
          | _ -> [] in
      only (Attack (ws, a.thop_u)) ms
    | _ -> [])

(* As [aatk3], but the smaller Walker attacks alone only while B's
   Walker is tapped (or B has none). *)
let () = def "aatk4" (fun s ms ->
    match s.pend with
    | ChooseAttack when own PA s ->
      let a = side PA s in
      let bw = match walker (side PB s) with Some w -> w.counters | None -> 0 in
      let rd = ready_idx a in
      let c i = (List.nth a.bf i).counters in
      let ws =
        if rd <> [] && List.for_all (fun i -> c i > bw) rd then rd
        else match rd with
          | [ i; j ] when max (c i) (c j) >= 3 && not (b_can_block s) -> [ (if c i <= c j then i else j) ]
          | _ -> [] in
      only (Attack (ws, a.thop_u)) ms
    | _ -> [])

(* A on B's turn: pass until B's end step; there pump the biggest
   untapped Walker if it is A's biggest Walker or has under 3 counters
   (both Walkers grow to 3/3, then only the biggest grows). *)
let () = def "apump3" (fun s ms ->
    match s.pend with
    | Window (EndStep, PA, _) when own PB s ->
      let a = side PA s in
      let top = List.fold_left (fun m w -> max m w.counters) 0 a.bf in
      (match biggest_ready a with
       | Some i when (List.nth a.bf i).counters >= top || (List.nth a.bf i).counters < 3 -> first_in [ Pump i; Pass ] ms
       | _ -> only Pass ms)
    | Window (_, PA, _) when own PB s -> only Pass ms
    | _ -> [])

(* A orders B's library after an Elixir shuffle: Elixir on top, the
   Walker under it. *)
let () = def "ashuf" (fun s ms ->
    match s.pend with
    | ChooseShuffle _ -> (match List.filter (function Arrange (CElixir :: _) -> true | _ -> false) ms with m :: _ -> [ m ] | [] -> [])
    | _ -> [])

let compose (fs : filter list) : filter = fun s ms ->
  List.fold_left (fun ms f -> match f s ms with [] -> ms | l -> l) ms fs

(* A rule's moves at [s], from the base moves [ms]. *)
type rule = state -> move list

let get_filter name =
  if name = "none" then compose []
  else
    compose (List.map (fun n -> match List.assoc_opt n !filters with
        | Some f -> f
        | None -> failwith ("strat: no filter " ^ n)) (String.split_on_char '+' name))

(* The rule as the closures use it: its moves out of every legal move, or
   none if it allows them all (no opinion). *)
let get_rule name : rule =
  let f = get_filter name in
  fun s -> let ms = moves s in let l = f s ms in if List.length l = List.length ms then [] else l
