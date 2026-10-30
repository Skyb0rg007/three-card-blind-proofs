(* Breadth-first enumeration of the distinct states at the start of each turn. *)
open Model
open Rules

(* Canonical form outside combat: order Walkers so permutations hash equally. *)
let canon s =
  if s.cmb.atk <> [] || s.cmb.atk_thop <> 0 then s
  else
    let sortw sd = { sd with bf = List.sort compare sd.bf } in
    { s with sideA = sortw s.sideA; sideB = sortw s.sideB }

let moves_fn = ref Rules.moves

let is_turn_start s =
  match s.pend with Window (Upkeep, _, false) -> true | _ -> false

(* All states at the start of the next turn (or game over) reachable from s. *)
let next_turn_starts s =
  let seen = Hashtbl.create 1024 in
  let out = Hashtbl.create 64 in
  let rec go s first =
    let s = canon s in
    if Hashtbl.mem seen s then ()
    else begin
      Hashtbl.add seen s ();
      if (not first) && (is_turn_start s || winner s <> None) then Hashtbl.replace out s ()
      else List.iter (fun m -> go (step s m) false) (!moves_fn s)
    end
  in
  go s true;
  (Hashtbl.length seen, Hashtbl.fold (fun k () acc -> k :: acc) out [])

let bfs starter turns =
  let layer = ref [ init starter ] in
  for t = 1 to turns do
    let next = Hashtbl.create 1024 in
    let inner = ref 0 in
    List.iter (fun s ->
      if winner s = None then begin
        let n, outs = next_turn_starts s in
        inner := !inner + n;
        List.iter (fun s' -> Hashtbl.replace next s' ()) outs
      end) !layer;
    layer := Hashtbl.fold (fun k () acc -> k :: acc) next [];
    let wins p = List.length (List.filter (fun s -> winner s = Some p) !layer) in
    Printf.printf "after turn %d: %d states (%d intermediate), A wins %d, B wins %d\n%!"
      t (List.length !layer) !inner (wins PA) (wins PB)
  done

(* Within caps (walker counters <= c, thopters <= t, B life <= l), count the
   distinct turn-start states reachable from the opening. *)
let within c t l s =
  let ok sd = List.for_all (fun w -> w.counters <= c) sd.bf && sd.thop_u + sd.thop_t <= t in
  ok s.sideA && ok s.sideB && s.sideB.life <= l

let reach starter c t l =
  let seen = Hashtbl.create 1_000_000 in
  let key s = Marshal.to_string (canon s) [ Marshal.No_sharing ] in
  let frontier = ref [ init starter ] in
  Hashtbl.replace seen (key (init starter)) ();
  let turn = ref 0 in
  while !frontier <> [] do
    incr turn;
    let next = ref [] in
    List.iter (fun s ->
        let _, outs = next_turn_starts s in
        List.iter (fun s' ->
            if winner s' = None && within c t l s' then begin
              let k = key s' in
              if not (Hashtbl.mem seen k) then (Hashtbl.add seen k (); next := s' :: !next)
            end) outs)
      !frontier;
    frontier := !next;
    Printf.printf "turn %d: %d new, %d total\n%!" !turn (List.length !next) (Hashtbl.length seen)
  done
