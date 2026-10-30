(* Pretty-printing for extracted model states and moves. *)
open Model
open Rules

let player = function PA -> "A" | PB -> "B"

let stepk = function
  | Upkeep -> "upkeep" | DrawStep -> "draw" | Main1 -> "main1"
  | BeginCombat -> "begin-combat" | DeclAtk -> "attackers" | DeclBlk -> "blockers"
  | DamageStep -> "damage" | EndCombat -> "end-combat" | Main2 -> "main2"
  | EndStep -> "end"

let card = function CWalker -> "W" | CElixir -> "E"

let walker w =
  Printf.sprintf "%d%s%s" w.counters (if w.wtapped then "T" else "") (if w.sick then "s" else "")

let list f l = "[" ^ String.concat "," (List.map f l) ^ "]"

let side s =
  Printf.sprintf "life=%d city=%s pool=%d hand=W%d%s bf=%s%s thop=%d+%dT lib=%s gy=W%d"
    s.life (if s.city then "U" else "T") s.pool s.hand_w (if s.hand_e then "+E" else "")
    (list walker s.bf) (if s.elixir_bf then "+E" else "")
    s.thop_u s.thop_t (list card s.library) s.gy_w

let blocker = function BW i -> Printf.sprintf "W%d" i | BT -> "T"

let pending = function
  | Window (st, p, passed) -> Printf.sprintf "%s: %s has priority%s" (stepk st) (player p) (if passed then " (passed)" else "")
  | ChooseAttack -> "choose attackers"
  | ChooseBlock -> "choose blockers"
  | ChooseOrder -> "choose damage order"
  | ChooseDamage -> "assign damage"
  | ChooseShuffle (st, p, cs) -> Printf.sprintf "%s: shuffle %s for %s" (stepk st) (list card cs) (player p)
  | Over w -> Printf.sprintf "%s wins" (player w)

let state s =
  Printf.sprintf "active=%s%s | %s\n  A: %s\n  B: %s%s" (player s.active)
    (if s.first_turn then " (first turn)" else "") (pending s.pend) (side s.sideA) (side s.sideB)
    (if s.cmb.atk = [] && s.cmb.atk_thop = 0 then ""
     else Printf.sprintf "\n  combat: atk=%s thop=%d blk=%s trades=%d"
         (list string_of_int s.cmb.atk) s.cmb.atk_thop (list (list blocker) s.cmb.blk) s.cmb.trades)

let opt_int = function None -> "-" | Some i -> string_of_int i

let move = function
  | Pass -> "pass"
  | Pump i -> Printf.sprintf "pump W%d" i
  | ActElixir -> "activate Elixir"
  | CastWalker x -> Printf.sprintf "cast Walker X=%d" x
  | CastElixir -> "cast Elixir"
  | Attack (ws, k) -> Printf.sprintf "attack walkers=%s thopters=%d" (list string_of_int ws) k
  | Block (wb, tb, tr) -> Printf.sprintf "block walkers=%s thopters=%s trades=%d" (list opt_int wb) (list string_of_int tb) tr
  | Order os -> Printf.sprintf "order %s" (list (list blocker) os)
  | Assign js -> Printf.sprintf "assign kills=%s" (list string_of_int js)
  | Arrange l -> Printf.sprintf "arrange library %s" (list card l)
