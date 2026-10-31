(* Differential testing against the Rust solver (rsolver): a seeded random
   walk through the model that prints every state, its move lists (full,
   filter, both macros) and, at turn starts, the packed key and its digest,
   in a text format that rsolver's walk command reproduces exactly. *)
open Model

let b x = if x then "1" else "0"
let step_i = function
  | Upkeep -> 0 | DrawStep -> 1 | Main1 -> 2 | BeginCombat -> 3 | DeclAtk -> 4
  | DeclBlk -> 5 | DamageStep -> 6 | EndCombat -> 7 | Main2 -> 8 | EndStep -> 9
let pl = function PA -> "A" | PB -> "B"
let list f l = "[" ^ String.concat ";" (List.map f l) ^ "]"
let card = function CWalker -> "W" | CElixir -> "E"
let blocker = function BT -> "T" | BW i -> "W" ^ string_of_int i

let side sd =
  Printf.sprintf "%d,%s,%d,%d,%s,%s,%s,%d,%d,%s,%d" sd.life (b sd.city) sd.pool sd.hand_w (b sd.hand_e)
    (list (fun w -> Printf.sprintf "%d:%s:%s" w.counters (b w.wtapped) (b w.sick)) sd.bf)
    (b sd.elixir_bf) sd.thop_u sd.thop_t (list card sd.library) sd.gy_w

let pend = function
  | Window (st, p, x) -> Printf.sprintf "W%d,%s,%s" (step_i st) (pl p) (b x)
  | ChooseAttack -> "CA" | ChooseBlock -> "CB" | ChooseOrder -> "CO" | ChooseDamage -> "CD"
  | ChooseShuffle (st, p, cs) -> Printf.sprintf "CS%d,%s,%s" (step_i st) (pl p) (list card cs)
  | Over p -> "O" ^ pl p

let state s =
  Printf.sprintf "S act=%s ft=%s pend=%s cmb=%s/%d/%s/%d A=%s B=%s" (pl s.active) (b s.first_turn) (pend s.pend)
    (list string_of_int s.cmb.atk) s.cmb.atk_thop (list (list blocker) s.cmb.blk) s.cmb.trades
    (side s.sideA) (side s.sideB)

let move = function
  | Pass -> "P" | Pump i -> "U" ^ string_of_int i | ActElixir -> "X" | CastWalker x -> "C" ^ string_of_int x
  | CastElixir -> "E"
  | Attack (ws, k) -> "A" ^ list string_of_int ws ^ string_of_int k
  | Block (wb, tb, tr) ->
    "B" ^ list (function None -> "-" | Some i -> string_of_int i) wb ^ list string_of_int tb ^ string_of_int tr
  | Order os -> "O" ^ list (list blocker) os
  | Assign js -> "S" ^ list string_of_int js
  | Arrange l -> "R" ^ list card l

let next x = Int64.add (Int64.mul x 6364136223846793005L) 1442695040888963407L
let pick x n = Int64.to_int (Int64.rem (Int64.shift_right_logical x 33) (Int64.of_int n))

(* With [bias], two draws in three avoid Pass and pumps when there is
   another move, so that walks reach combat and Thopters. A walk restarts
   when a Walker passes 40 counters. *)
let run ?(bias = false) seed steps =
  let x = ref (Int64.of_int seed) in
  let start () = init (if seed land 1 = 0 then PA else PB) in
  let s = ref (start ()) in
  for _ = 1 to steps do
    print_endline (state !s);
    let ms = Rules.moves !s in
    List.iter (fun (tag, l) -> print_endline (tag ^ " " ^ String.concat " " (List.map move l)))
      [ ("M", ms); ("F", Reduce.moves !s); ("AM", Reduce.a_macro !s); ("BM", Reduce.b_macro !s) ];
    if Search.is_turn_start !s then begin
      let k = Fix.key_gen false !s in
      Printf.printf "K %s %d\n" (Fix.hex k) (Tsearch.digest_key k)
    end;
    let big sd = List.exists (fun w -> w.counters > 40) sd.bf in
    if winner !s <> None || ms = [] || big !s.sideA || big !s.sideB then s := start ()
    else begin
      x := next !x;
      let others = List.filter (function Pass | Pump _ -> false | _ -> true) ms in
      let ms = if bias && others <> [] && pick !x 3 <> 0 then (x := next !x; others) else ms in
      s := Rules.step !s (List.nth ms (pick !x (List.length ms)))
    end
  done
