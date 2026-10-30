(* Depth-bounded search: can player [p] force a win within [d] more turn
   starts? Moves for [p] come from [mine], moves for the opponent from
   [theirs]; both default to the full model. *)
open Model
open Rules

let is_turn_start s =
  match s.pend with Window (Upkeep, _, false) -> true | _ -> false

(* Depth counts turns: it drops by one each time the active player changes. *)
let tick s s' d = if s'.active <> s.active then d - 1 else d

module H = Hashtbl.Make (struct
  type t = state
  let equal = ( = )
  let hash s = Hashtbl.hash_param 200 400 s
end)

type table = (int * int) H.t  (* state -> (max depth known lost, min depth known won) *)

let nodes = ref 0

let make ?(mine = Rules.moves) ?(theirs = Rules.moves) p =
  let tbl : table = H.create 1_000_000 in
  let rec wins s d =
    incr nodes;
    match winner s with
    | Some w -> w = p
    | None ->
      if d < 0 then false
      else
        let s = Explore.canon s in
        let lost, won = try H.find tbl s with Not_found -> (-1, max_int) in
        if d <= lost then false
        else if d >= won then true
        else begin
          let r =
            if to_move s = p then List.exists (fun m -> let s' = step s m in wins s' (tick s s' d)) (mine s)
            else List.for_all (fun m -> let s' = step s m in wins s' (tick s s' d)) (theirs s)
          in
          let lost, won = try H.find tbl s with Not_found -> (-1, max_int) in
          H.replace tbl s (if r then (lost, min won d) else (max lost d, won));
          r
        end
  in
  (tbl, wins)
