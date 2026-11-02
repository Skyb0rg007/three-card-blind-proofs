(* Experiments on the size of the B-safe certificate (closure of the
   opening): how much does it depend on which working move B is given at
   each of its nodes?

   [shrink-safe DIR STARTER ROUNDS] computes the closure the export would
   write (Certify.certify_safe_export, pass 1) with B's moves chosen as:
   - round 0: the first working move in model order (the export's choice);
   - round k > 0: at each B node, the working move whose turn's lookups
     add the least weight, a key in round k-1's closure weighing 1 / (1 +
     its use count there) and any other key 4. A's nodes add their
     children's weights (an over-count where children share keys).
   Each round's closure is collected with the extracted [check_node], B's
   hint allowing only the chosen move, so it is exactly what the check of
   the opening consults. Nothing here is trusted. *)
open Model

module H = Certify.H

let inf = infinity

(* A representative key for each turn-start lookup: SYM sorts A's Walkers;
   DOMK=1 takes the most dominant table key with the same value (A's life
   raised as far as it goes, then B's tapped and untapped Thopters
   lowered; sound for B by Mono.v), DOMK=2 only raises A's life. *)
let make_rep t sym domk =
  let lk = Certify.lookup t in
  let nl = t.Certify.sv.Fix.nl in
  let dom = domk > 0 and thop = domk = 1 in
  let setA f k = { k with sideA = f k.sideA } and setB f k = { k with sideB = f k.sideB } in
  let rep k =
    match lk k with
    | None -> None
    | Some v ->
      let k = if sym then setA (fun a -> { a with bf = List.sort compare a.bf }) k else k in
      if not dom then Some (k, v)
      else begin
        let ok k' = match lk k' with Some v' -> v' <= v | None -> false in
        let k = ref k in
        let continue = ref true in
        while !continue do
          let k' = setA (fun a -> { a with life = a.life + 1 }) !k in
          if k'.sideA.life <= nl && ok k' then k := k' else continue := false
        done;
        continue := thop;
        while !continue do
          let k' = setB (fun b -> { b with thop_t = b.thop_t - 1 }) !k in
          if k'.sideB.thop_t >= 0 && ok k' then k := k' else continue := false
        done;
        continue := thop;
        while !continue do
          let k' = setB (fun b -> { b with thop_u = b.thop_u - 1 }) !k in
          if k'.sideB.thop_u >= 0 && ok k' then k := k' else continue := false
        done;
        Some (!k, v)
      end
  in
  rep


(* One turn from the entry [s0]: B's chosen move at each of its nodes,
   minimising the summed weight [w] of the turn starts reached. *)
let chooser t rep w =
  let memo = H.create 1024 and pick = H.create 256 in
  let rec cost root s =
    match winner s with
    | Some PB -> 0.
    | Some PA -> inf
    | None ->
      if (not root) && is_turn_start s then
        match rep (key t.Certify.h t.Certify.tt s) with Some (k, v) when v <= s.sideB.life -> w k | _ -> inf
      else if huge_event t.Certify.h s then inf
      else
        match H.find_opt memo s with
        | Some c -> c
        | None ->
          let child m = let s' = step s m in if too_many t.Certify.ott s' then inf else cost false s' in
          let c =
            match to_move s with
            | PA -> List.fold_left (fun acc m -> if acc = inf then inf else acc +. child m) 0. (moves s)
            | PB ->
              let best = ref inf and bm = ref None in
              List.iter (fun m -> let c = child m in if c < !best then (best := c; bm := Some m)) (moves s);
              (match !bm with Some m -> H.replace pick s m | None -> ());
              !best
          in
          H.replace memo s c;
          c
  in
  let hint s m = match H.find_opt pick s with Some m' -> m = m' | None -> false in
  let reset () = H.reset memo; H.reset pick in
  (cost, hint, reset)

(* The closure from the opening; [hint_for] gives B's hint for an entry. *)
let closure t rep starter (prepare : state -> (state -> move -> bool)) =
  let s0 = init starter in
  let k0, v0 = match rep (key t.Certify.h t.Certify.tt s0) with Some e -> e | None -> failwith "shrink: the opening has no entry" in
  let used = Hashtbl.create 1_000_000 and uses = Hashtbl.create 1_000_000 and queue = Queue.create () in
  let add s v =
    let k = Certify.enc s in
    Hashtbl.replace uses k (1 + Option.value (Hashtbl.find_opt uses k) ~default:0);
    if not (Hashtbl.mem used k) then (Hashtbl.replace used k (s, v); Queue.push (s, v) queue)
  in
  add k0 v0;
  let logging s = match rep s with Some (k, v) -> add k v; Some v | None -> None in
  let bad = ref 0 in
  while not (Queue.is_empty queue) do
    let s, v = Queue.pop queue in
    let e = entry s v in
    let hint = prepare e in
    if not (check_node t.Certify.h t.Certify.ott t.Certify.tt logging hint Certify.fuel true e) then incr bad
  done;
  (used, uses, !bad)

let run dir starter rounds =
  let t = Certify.open_table dir in
  let lk = Certify.lookup t in
  let sym = Sys.getenv_opt "TCB_SYM" = Some "1" in
  let domk = match Sys.getenv_opt "TCB_DOMK" with Some d -> int_of_string d | None -> 0 in
  let rep = make_rep t sym domk in
  Printf.printf "shrink-safe sym=%b domk=%d\n%!" sym domk;
  let t0 = Unix.gettimeofday () in
  let report r (used, _, bad) =
    Printf.printf "round %d: %d entries, %d failed (%.0fs)\n%!" r (Hashtbl.length used) bad (Unix.gettimeofday () -. t0)
  in
  let res = ref (closure t rep starter (fun _ ->
      let memo, _, hint = Certify.oracle t lk in H.reset memo; hint)) in
  report 0 !res;
  for r = 1 to rounds do
    let used, uses, _ = !res in
    let w k =
      let e = Certify.enc k in
      if Hashtbl.mem used e then 1. /. (1. +. float (Option.value (Hashtbl.find_opt uses e) ~default:0)) else 4.
    in
    let cost, hint, reset = chooser t rep w in
    res := closure t rep starter (fun e -> reset (); ignore (cost true e); hint);
    report r !res
  done

(* [dom-safe DIR STARTER SYM DOM]: the export's closure (B's first working
   move), but each turn-start lookup is answered by a representative key:
   with DOM=1 the most dominant table key with the same value (A's life
   raised as far as it goes, then B's tapped and untapped Thopters lowered;
   sound for B by Mono.v's monotonicity), with SYM=1 A's Walkers sorted. *)
let dom_safe dir starter sym domk =
  let t = Certify.open_table dir in
  let lk = Certify.lookup t in
  let nl = t.Certify.sv.Fix.nl in
  let t0 = Unix.gettimeofday () in
  let rep = make_rep t sym domk in
  ignore nl;
  let s0 = init starter in
  let used = Hashtbl.create 1_000_000 and queue = Queue.create () in
  let add (s, v) =
    let k = Certify.enc s in
    if not (Hashtbl.mem used k) then (Hashtbl.replace used k (); Queue.push (s, v) queue)
  in
  (match rep (key t.Certify.h t.Certify.tt s0) with Some e -> add e | None -> failwith "dom-safe: no opening");
  let logging s = match rep s with Some (k, v) -> add (k, v); Some v | None -> None in
  let bad = ref 0 in
  while not (Queue.is_empty queue) do
    let s, v = Queue.pop queue in
    let memo, _, hint = Certify.oracle t lk in
    H.reset memo;
    if not (check_node t.Certify.h t.Certify.ott t.Certify.tt logging hint Certify.fuel true (entry s v)) then incr bad
  done;
  Printf.printf "dom-safe sym=%b dom=%d: %d entries, %d failed (%.0fs)\n%!" sym domk (Hashtbl.length used) !bad
    (Unix.gettimeofday () -. t0);
  let hist = Array.make 32 0 in
  Hashtbl.iter (fun (k1, _) () -> let l = k1 land 31 in hist.(l) <- hist.(l) + 1) used;
  Printf.printf "entries by A life:";
  Array.iteri (fun l n -> if n > 0 then Printf.printf " %d:%d" l n) hist;
  print_newline ()

(* [amono DIR] (experiment): in an A-safe BIG table, how a position's line
   (c, b) varies with A's life. Counts bases whose finite lines are
   componentwise non-decreasing in A's life, a chain in some other order,
   or neither. *)
let amono dir =
  let t = Certifya.open_table dir in
  let sv = t.Certifya.sv in
  let nb = sv.Fix.nb and nl = sv.Fix.nl in
  let mono = ref 0 and chain = ref 0 and neither = ref 0 and single = ref 0 and steps = ref 0 and bad = ref 0 in
  for b = 0 to nb - 1 do
    let ls = List.filter_map (fun slot ->
        let i = (slot * nb) + b in
        let c, be = Certifya.line t i in
        if c <= Fix.ninf || c >= Fix.inf then None else Some (Fix.life_of_slot sv slot, c, be))
        (List.init nl Fun.id) in
    let le (_, c, b) (_, c', b') = c <= c' && b <= b' in
    if List.length ls < 2 then incr single
    else begin
      let rec m = function x :: (y :: _ as r) -> incr steps; if not (le x y) then incr bad; le x y && m r | _ -> true in
      if m ls then incr mono
      else if List.for_all (fun x -> List.for_all (fun y -> le x y || le y x) ls) ls then incr chain
      else incr neither
    end
  done;
  Printf.printf "amono: %d bases: %d with < 2 lines, %d non-decreasing, %d chains otherwise, %d neither; %d of %d steps decrease\n"
    nb !single !mono !chain !neither !bad !steps
