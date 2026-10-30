(* Like Csearch, but the transposition table only holds turn-start states,
   keyed by a 63-bit digest of the state instead of the marshalled bytes.
   Positions inside a turn are cached only while that turn is being
   searched. This uses far less memory per remembered position, so searches
   go deeper before the table fills up. Digest collisions are possible in
   principle (about n^2 / 2^63 for n entries) and are ignored. *)
open Model
open Rules

(* first 8 bytes of the MD5 of a key, as an int (63 bits kept) *)
let digest_key k = Int64.to_int (String.get_int64_le (Digest.string k) 0)

let digest s = digest_key (Csearch.key s)

let nodes = ref 0

(* table values pack (max depth known lost + 1) and (min depth known won)
   into one int: lost in the low 16 bits, won in the next 16 *)
let pack lost won = (lost + 1) lor (won lsl 16)
let lost_of v = (v land 0xffff) - 1
let won_of v = v lsr 16
let never = 0xffff

let make ?(mine = Rules.moves) ?(theirs = Rules.moves) ?(limit = 400_000_000) p =
  let tbl : (int, int) Hashtbl.t = Hashtbl.create 1_000_000 in
  let rec wins s d =
    incr nodes;
    match winner s with
    | Some w -> w = p
    | None ->
      if d < 0 then false
      else if Search.is_turn_start s then begin
        let k = digest s in
        let v = try Hashtbl.find tbl k with Not_found -> pack (-1) never in
        if d <= lost_of v then false
        else if d >= won_of v then true
        else begin
          let r = turn s d in
          if Hashtbl.length tbl > limit then Hashtbl.reset tbl;
          let v = try Hashtbl.find tbl k with Not_found -> pack (-1) never in
          Hashtbl.replace tbl k
            (if r then pack (lost_of v) (min (won_of v) d) else pack (max (lost_of v) d) (won_of v));
          r
        end
      end else turn s d
  (* search inside one turn, with a cache local to this call *)
  and turn s d =
    let local = Hashtbl.create 64 in
    let rec go s d =
      match winner s with
      | Some w -> w = p
      | None ->
        if d < 0 then false
        else if Search.is_turn_start s then wins s d
        else begin
          let k = (Csearch.key s, d) in
          match Hashtbl.find_opt local k with
          | Some r -> r
          | None ->
            incr nodes;
            let r =
              if to_move s = p then
                List.exists (fun m -> let s' = step s m in next s s' d) (Csearch.order_mine (mine s))
              else List.for_all (fun m -> let s' = step s m in next s s' d) (theirs s)
            in
            Hashtbl.replace local k r;
            r
        end
    and next s s' d = let d' = Search.tick s s' d in if Search.is_turn_start s' then wins s' d' else go s' d' in
    (* expand the turn-start node itself *)
    if to_move s = p then
      List.exists (fun m -> let s' = step s m in next s s' d) (Csearch.order_mine (mine s))
    else List.for_all (fun m -> let s' = step s m in next s s' d) (theirs s)
  in
  (tbl, wins)
