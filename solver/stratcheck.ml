(* The checks of the rule strategies in [Strat] (see there). *)
open Model
open Strat

module H = Certify.H

type stats = {
  mutable entries : int;   (* turn-start entries in the closure *)
  mutable nodes : int;     (* distinct decision nodes (2+ moves) logged: the rule's move fails or there is none *)
  mutable followed : int;  (* visits of decision nodes where the rule's move works *)
  mutable unsure : int;    (* distinct nodes where the rule gave no move *)
  mutable exc : int;       (* distinct nodes where it doesn't work, but another move does *)
  mutable dead : int;      (* entries where no move works at all *)
  mutable distinct : int;  (* distinct decision nodes (2+ moves) visited *)
  all_seen : (int, unit) Hashtbl.t;
}

let new_stats () =
  { entries = 0; nodes = 0; followed = 0; unsure = 0; exc = 0; dead = 0; distinct = 0; all_seen = Hashtbl.create 1_000_000 }

let report st =
  Printf.printf "closure: %d entries; %d distinct decision nodes; rule's move works at %d decision visits; %d distinct nodes logged: no rule move at %d, exception at %d; %d dead entries\n%!"
    st.entries st.distinct st.followed st.nodes st.unsure st.exc st.dead

(* At a protagonist node with moves [ms]: the move to follow, logging the
   node. [works m] says whether [m] keeps the table's value. *)
let hash60 s = (Hashtbl.seeded_hash_param 100 400 1 s lsl 30) lxor Hashtbl.seeded_hash_param 100 400 2 s
let dump_all = Sys.getenv_opt "TCB_DUMP" = Some "all"
(* TCB_DUMP_PEND=attack (say): log only nodes at that kind of decision *)
let dump_pend = Sys.getenv_opt "TCB_DUMP_PEND"
let dump_ok s = match dump_pend with None -> true | Some p -> pend_str s.pend = p

let decide st (seen : (int, unit) Hashtbl.t) out rule s ms works =
  match ms with
  | [ m ] -> if works m then Some m else None
  | _ ->
    let h0 = hash60 s in
    if not (Hashtbl.mem st.all_seen h0) then (Hashtbl.replace st.all_seen h0 (); st.distinct <- st.distinct + 1);
    let rm = List.filter (fun m -> List.mem m ms) (rule s) in
    match List.find_opt works rm with
    | Some m when not dump_all -> st.followed <- st.followed + 1; Some m
    | found ->
      let good = List.filter works ms in
      let pick = match found with Some m -> Some m | None -> (match good with m :: _ -> Some m | [] -> None) in
      let h = hash60 s in
      if not (Hashtbl.mem seen h) then begin
        Hashtbl.replace seen h ();
        st.nodes <- st.nodes + 1;
        let tag =
          if good = [] then "none"
          else if rm = [] then (st.unsure <- st.unsure + 1; "unsure")
          else if found <> None then "ok"
          else (st.exc <- st.exc + 1; "EXC")
        in
        if (dump_all || List.length good < List.length ms) && dump_ok s then
          Option.iter (fun oc ->
              Printf.fprintf oc "%s\t%s\trule=%s\tgood=%s\tall=%s\n" tag (st_str s) (String.concat " " (List.map mv rm))
                (String.concat " " (List.map mv good)) (String.concat " " (List.map mv ms)))
            out
      end else if found <> None then st.followed <- st.followed + 1;
      pick

(* ** B first: B's ranked win (Certify.win_reach with a rule) *)

let closure_bfirst rule out =
  let dir = tbl "bwin-bfirst-12-full" in
  let w = Certify.open_win dir in
  let t = w.Certify.wt in
  let lk k r = match Certify.index t k with Some i -> Certify.record w i r | None -> None in
  let below k r = match Certify.index t k with Some i -> Certify.below_rec w i r | None -> None in
  let life = Certify.env_int "TCB_LIFE" 20 in
  let s0 = init PB in
  let i0 = Option.get (Certify.index t (key t.Certify.h t.Certify.tt s0)) in
  let a, b = Certify.recs w i0 in
  let rec first p =
    if p >= b then failwith "no opening record" else if Certify.rval w p <= life then Certify.rank w i0 p else first (p + 1) in
  (* entries: (position, rank) with the least real B life it was reached with *)
  let used = Hashtbl.create 100_000 and queue = Queue.create () in
  let add i r l =
    match Hashtbl.find_opt used (i, r) with
    | Some l' when l' <= l -> ()
    | _ -> Hashtbl.replace used (i, r) l; Queue.push (i, r, l) queue in
  add i0 (first a) life;
  let memo = H.create 1024 in
  let rec ok r root s =
    match winner s with
    | Some PB -> true
    | Some PA -> false
    | None ->
      if (not root) && is_turn_start s then
        let k = key t.Certify.h t.Certify.tt s in
        match below k r with
        | Some r' -> (match lk k r' with Some v -> v <= s.sideB.life | None -> false)
        | None -> false
      else if huge_event t.Certify.h s then false
      else
        match H.find_opt memo s with
        | Some x -> x
        | None ->
          let x = match to_move s with
            | PB -> List.exists (next r s) (moves s)
            | PA -> List.for_all (next r s) (moves s) in
          H.replace memo s x;
          x
  and next r s m = let s' = step s m in (not (too_many t.Certify.ott s')) && ok r false s' in
  let st = new_stats () and seen = Hashtbl.create 100_000 in
  let visited = H.create 1024 in
  let rec collect r root s =
    if winner s <> None then ()
    else if (not root) && is_turn_start s then begin
      let k = key t.Certify.h t.Certify.tt s in
      match below k r, Certify.index t k with
      | Some r', Some i -> add i r' s.sideB.life
      | _ -> failwith "a turn start without a record"
    end else if H.mem visited s then ()
    else begin
      H.replace visited s ();
      match to_move s with
      | PB ->
        (match decide st seen out rule s (moves s) (next r s) with
         | Some m -> collect r false (step s m)
         | None -> ())
      | PA -> List.iter (fun m -> collect r false (step s m)) (moves s)
    end
  in
  while not (Queue.is_empty queue) do
    let i, r, l = Queue.pop queue in
    if Hashtbl.find used (i, r) = l then
    match Certify.record w i r with
    | Some v when v <= l ->
      st.entries <- st.entries + 1;
      List.iter (fun s ->
          let s = { s with sideB = { s.sideB with life = l } } in
          H.reset memo; H.reset visited;
          if ok r true s then collect r true s else st.dead <- st.dead + 1)
        (Certify.record_states w i);
      if st.entries mod 100_000 = 0 then (Printf.printf "  %d entries, %d queued\n%!" st.entries (Queue.length queue))
    | _ -> st.dead <- st.dead + 1
  done;
  st

(* ** A first: B safe (Certify.oracle with a rule) *)

let closure_bsafe rule out =
  let t = Certify.open_table (tbl "bsafe-afirst-ot9") in
  let lk = Certify.lookup t in
  let s0 = init PA in
  let k0 = key t.Certify.h t.Certify.tt s0 in
  (* entries: keys with the least real B life they were reached with *)
  let used = Hashtbl.create 100_000 and queue = Queue.create () in
  let add k l =
    let e = Certify.enc k in
    match Hashtbl.find_opt used e with
    | Some l' when l' <= l -> ()
    | _ -> Hashtbl.replace used e l; Queue.push (e, l) queue in
  add k0 s0.sideB.life;
  let memo, ok, _ = Certify.oracle t lk in
  let next s m = let s' = step s m in (not (too_many t.Certify.ott s')) && ok false s' in
  let st = new_stats () and seen = Hashtbl.create 100_000 in
  let visited = H.create 1024 in
  let rec collect root s =
    if winner s <> None then ()
    else if (not root) && is_turn_start s then add (key t.Certify.h t.Certify.tt s) s.sideB.life
    else if H.mem visited s then ()
    else begin
      H.replace visited s ();
      match to_move s with
      | PB -> (match decide st seen out rule s (moves s) (next s) with Some m -> collect false (step s m) | None -> ())
      | PA -> List.iter (fun m -> collect false (step s m)) (moves s)
    end
  in
  while not (Queue.is_empty queue) do
    let e, v = Queue.pop queue in
    if Hashtbl.find used e = v then begin
      st.entries <- st.entries + 1;
      let s = entry (Certify.dec e) v in
      H.reset memo; H.reset visited;
      if ok true s then collect true s else st.dead <- st.dead + 1;
      if st.entries mod 100_000 = 0 then (Printf.printf "  %d entries, %d queued\n%!" st.entries (Queue.length queue))
    end
  done;
  st

(* ** A first: A safe (Certifya, lines c + b n) *)

module HL = Hashtbl.Make (struct
    type t = state * int * int * int
    let equal = ( = )
    let hash = Hashtbl.hash_param 100 400
  end)

let closure_asafe rule out =
  let p = Certifya.{ k = 21; hb = 6; ott = 5; tt = 8; m = 200; fuel = 1_000_000 } in
  let t = Certifya.open_table (tbl "asafe-afirst-big-o5") in
  let lk = Certifya.lookup t in
  let s0 = init PA in
  let k0 = Certify.canon (a_key p.hb p.tt s0) in
  (* entries: keys with the line B's life must stay under there (c + b n
     for n >= lo), as the check from the opening asks it; for a key, b and
     lo, the largest c explored *)
  let used = Hashtbl.create 100_000 and queue = Queue.create () in
  let add k c b lo =
    let e = Certify.enc (Certify.canon k) in
    match Hashtbl.find_opt used (e, b, lo) with
    | Some c' when c' >= c -> ()
    | _ -> Hashtbl.replace used (e, b, lo) c; Queue.push (e, c, b, lo) queue in
  (match lk k0 with Some (c, b) -> add k0 c b 0 | None -> failwith "no opening entry");
  let memo = HL.create 1024 in
  let rec ok root s c b lo =
    match winner s with
    | Some _ -> false
    | None ->
      if (not root) && is_turn_start s then
        match lk (a_key p.hb p.tt s) with
        | Some l -> Certifya.meets p s c b lo l
        | None -> false
      else if a_huge_event p.hb s || a_big_event p.k s then false
      else
        match HL.find_opt memo (s, c, b, lo) with
        | Some r when not root -> r
        | _ ->
          let r = match to_move s with
            | PA -> List.exists (next s c b lo) (moves s)
            | PB -> List.for_all (next s c b lo) (moves s) in
          if not root then HL.replace memo (s, c, b, lo) r;
          r
  and next s c b lo m =
    match Certifya.edge p s c b lo m with
    | `Fail -> false
    | `Dead -> true
    | `Go (s', c2, b2, lo2) -> ok false s' c2 b2 lo2
  in
  let st = new_stats () and seen = Hashtbl.create 100_000 in
  let visited = HL.create 1024 in
  let rec collect root s c b lo =
    if winner s <> None then ()
    else if (not root) && is_turn_start s then add (a_key p.hb p.tt s) c b lo
    else if HL.mem visited (s, c, b, lo) then ()
    else begin
      HL.replace visited (s, c, b, lo) ();
      let follow m = match Certifya.edge p s c b lo m with
        | `Go (s', c2, b2, lo2) -> collect false s' c2 b2 lo2
        | _ -> () in
      match to_move s with
      | PA -> Option.iter follow (decide st seen out rule s (moves s) (next s c b lo))
      | PB -> List.iter follow (moves s)
    end
  in
  while not (Queue.is_empty queue) do
    let e, c, b, lo = Queue.pop queue in
    if Hashtbl.find used (e, b, lo) = c then begin
      st.entries <- st.entries + 1;
      let s = a_entry p.m (Certify.dec e) in
      HL.reset memo; HL.reset visited;
      if ok true s c b lo then collect true s c b lo else st.dead <- st.dead + 1;
      if st.entries mod 100_000 = 0 then (Printf.printf "  %d entries, %d queued\n%!" st.entries (Queue.length queue))
    end
  done;
  st

let closure mode rname outf =
  let rule = get_rule rname in
  let out = if outf = "-" then None else Some (open_out outf) in
  let t0 = Unix.gettimeofday () in
  let st = match mode with
    | "bfirst" -> closure_bfirst rule out
    | "bsafe" -> closure_bsafe rule out
    | "asafe" -> closure_asafe rule out
    | _ -> failwith "strat-closure: MODE is bfirst, bsafe or asafe" in
  Option.iter close_out out;
  Printf.printf "%s, rule %s (%.0fs)\n" mode rname (Unix.gettimeofday () -. t0);
  report st

(* ** The rule's own value (Fix, the protagonist restricted to the rule)

   B's rules only (Fix has no BIG Walker for A). The caps are the
   certificates': B first B Walker <= t, A huge above ot, B's Thopters cut
   at tt, more than ott A Thopters a loss; every legal A move. A rule that
   returns no move leaves B every move there (counted by [strat-closure]). *)
let fix mode rname dir =
  (* B's base moves are the certificates' macro (TCB_BMACRO, default here
     blk,atk2,dmg), and the rule filters them *)
  let f = get_filter rname in
  let t = Certify.env_int "TCB_T" (if mode = "bfirst" then 12 else 10) in
  let capped s = List.filter (function Pump i -> (List.nth (get_side PB s).bf i).counters < t | _ -> true) in
  let mine s = f s (capped s (Reduce.b_macro s)) in
  let t0 = Unix.gettimeofday () in
  let base = { Fix.prot = PB; t = 12; ot = 12; tt = 12; ott = 12; lmax = 100; full_a = false; mine; theirs = (if Sys.getenv_opt "TCB_AFILTER" = Some "1" then Reduce.moves else moves) } in
  let c, s0, safe =
    match mode with
    | "bfirst" -> ({ base with t = Certify.env_int "TCB_T" 12 }, init PB, false)
    | "bsafe" -> ({ base with t = Certify.env_int "TCB_T" 10; ot = 9; tt = 10; ott = 20 }, init PA, true)
    | _ -> failwith "strat-fix: MODE is bfirst or bsafe" in
  let sv = if safe then Fix.safe c s0 dir else Fix.win c s0 dir in
  Printf.printf "%s, rule %s: from the opening %s; %d bases (%.0fs)\n%!" mode rname
    (Fix.show c (Fix.value c sv s0)) sv.Fix.nb (Unix.gettimeofday () -. t0);
  Fix.remove sv

(* ** A principal variation of the A-safe table

   From the A-first opening with B on [life] (A's line there is (20, 0)):
   B plays the move that leaves A the least slack, the table's line at the
   real n minus B's real life; A plays RULE's move if it keeps the slack
   at least 0, else the move with the most slack. The BIG Walker's real
   size K + n is tracked (n counts pumps on it). Prints [turns] turns. *)
let pv_asafe rname life turns =
  let p = Certifya.{ k = 21; hb = 6; ott = 5; tt = 8; m = 200; fuel = 1_000_000 } in
  let t = Certifya.open_table (tbl "asafe-afirst-big-o5") in
  let lk = Certifya.lookup t in
  let rule = get_rule rname in
  let _, edge = Certifya.solver_line p lk 20 in
  let slack s n l m = match edge s m with Some (c, b) -> c + (b * n) - l | None -> min_int in
  let show_side sd n big =
    Printf.sprintf "life %d, city %s, hand W%d%s, Walkers [%s]%s, Thopters %d+%dt, library [%s], gy W%d" sd.life
      (if sd.city then "U" else "T") sd.hand_w (if sd.hand_e then "+E" else "")
      (String.concat "," (List.map (fun w ->
           (if big && w.counters = p.k then Printf.sprintf "BIG(%d)" (p.k + n) else string_of_int w.counters)
           ^ (if w.wtapped then "t" else "") ^ if w.sick then "s" else "") sd.bf))
      (if sd.elixir_bf then " +Elixir" else "") sd.thop_u sd.thop_t
      (String.concat "" (List.map Show.card sd.library)) sd.gy_w in
  let rec go s l n turn =
    if turn > turns then ()
    else
      match winner s with
      | Some w -> Printf.printf "%s wins\n" (Show.player w)
      | None ->
        if is_turn_start s then begin
          let k = a_key p.hb p.tt s in
          let line = match lk k with Some (c, b) -> Printf.sprintf "table line (%d, %d): slack %d" c b (c + (b * n) - l) | None -> "no entry" in
          Printf.printf "--- turn %d, %s active; %s\n  A: %s\n  B: %s\n" turn (Show.player s.active) line
            (show_side s.sideA n true) (show_side { s.sideB with life = l } n false)
        end;
        let ms = moves s in
        let scored = List.map (fun m -> (m, slack s n l m)) ms in
        let best f = List.fold_left (fun acc (m, v) -> match acc with Some (_, v') when not (f v v') -> acc | _ -> Some (m, v)) None scored in
        let m =
          match to_move s with
          | PB -> fst (Option.get (best ( < )))
          | PA ->
            (match List.find_opt (fun (m, v) -> v >= 0 && List.mem m (rule s)) scored with
             | Some (m, _) -> m
             | None -> fst (Option.get (best ( > ))))
        in
        if m <> Pass && List.length ms > 1 then
          Printf.printf "  %s: %s\n" (Show.player (to_move s)) (Show.move m);
        let s' = a_stepA p.k p.hb p.tt s m in
        let l' = l + (Certifya.blife s' - Certifya.blife s) in
        let l' = if a_is_hit p.k s then l' - n else l' in
        let n' = if a_is_pump_big p.k s m then n + 1 else if a_is_create p.k s m then 0 else n in
        if l' <= 0 then Printf.printf "B is dead (life %d)\n" l'
        else go s' l' n' (if is_turn_start s' then turn + 1 else turn)
  in
  go (a_entry p.m (init PA)) life 0 0
