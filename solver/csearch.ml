(* Like Search, but with compact keys (marshalled bytes) so deeper searches
   fit in memory, and with move ordering for the searching player. *)
open Model
open Rules

let key s = Marshal.to_string (Explore.canon s) [ Marshal.No_sharing ]

let nodes = ref 0

(* Prefer aggressive moves for the searching player: attacks with more, casts, pumps. *)
let score_mine m =
  match m with
  | Attack (ws, k) -> 100 + (10 * List.length ws) + k
  | CastWalker 1 -> 90
  | CastElixir -> 80
  | Pump _ -> 70
  | ActElixir -> 60
  | Pass -> 0
  | _ -> 50

let order_mine ms = List.stable_sort (fun a b -> compare (score_mine b) (score_mine a)) ms

let make ?(mine = Rules.moves) ?(theirs = Rules.moves) ?(limit = 40_000_000) p =
  let tbl : (string, int * int) Hashtbl.t = Hashtbl.create 1_000_000 in
  let rec wins s d =
    incr nodes;
    match winner s with
    | Some w -> w = p
    | None ->
      if d < 0 then false
      else begin
        let k = key s in
        let lost, won = try Hashtbl.find tbl k with Not_found -> (-1, max_int) in
        if d <= lost then false
        else if d >= won then true
        else begin
          let r =
            if to_move s = p then
              List.exists (fun m -> let s' = step s m in wins s' (Search.tick s s' d)) (order_mine (mine s))
            else List.for_all (fun m -> let s' = step s m in wins s' (Search.tick s s' d)) (theirs s)
          in
          if Hashtbl.length tbl > limit then Hashtbl.reset tbl;
          let lost, won = try Hashtbl.find tbl k with Not_found -> (-1, max_int) in
          Hashtbl.replace tbl k (if r then (lost, min won d) else (max lost d, won));
          r
        end
      end
  in
  (tbl, wins)
