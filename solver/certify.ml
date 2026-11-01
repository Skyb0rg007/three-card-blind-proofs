(* Driver for the extracted certificate checker (theories/Checker.v).

   [Saturation.certified_opening] says: if [lookup s = Some v] implies
   [check_node h ott tt lookup hint fuel true (entry s v) = true] for every
   [s] and [v], and the opening's key has an entry of at most 20, then B does
   not lose from the opening. Nothing is assumed about [lookup] and [hint].

   Here [lookup] reads a solved B-safe table and answers only for states
   exactly in the table's form, up to the order of the Walkers on each
   battlefield, so its domain can be enumerated: every base, every A-life
   level with a finite value, every order of the Walkers. Each is checked
   with the extracted [check_node]. [hint] is an untrusted oracle: a memoised
   search that mirrors [check_node], so the checker only follows B's moves
   that work. *)
open Model

let fuel = 1_000_000

(* Distinct orders of a list. *)
let rec perms = function
  | [] -> [ [] ]
  | l ->
    List.sort_uniq compare l
    |> List.concat_map (fun x ->
        let rec drop = function [] -> [] | y :: r -> if y = x then r else y :: drop r in
        List.map (fun p -> x :: p) (perms (drop l)))

type table = { sv : Fix.solver; h : int; ott : int; tt : int; lmax : int }

let open_table dir =
  let meta = Fix.read_meta dir in
  let get k = try List.assoc k meta with Not_found -> failwith (dir ^ ": meta has no " ^ k) in
  let geti k = int_of_string (get k) in
  if get "who" <> "B" then failwith "certify: needs a table for B";
  if geti "fulla" <> 0 then failwith "certify: needs A's life in the keys (fulla=0)";
  let nb = geti "nb" and nl = geti "nl" in
  { sv = Fix.open_dir dir ~nb ~nl ~write:false; h = geti "ot" + 1; ott = geti "ott"; tt = geti "tt";
    lmax = geti "lmax" }

(* The table position of [s], if [s] is a turn start in key form: B on 0
   life, A's graveyard empty, A's life one of the table's levels. *)
let index t s =
  let sv = t.sv in
  if s.pend <> Window (Upkeep, s.active, false) || s.cmb <> no_combat || s.sideB.life <> 0
     || s.sideA.gy_w <> 0 || s.sideA.life < 1 || s.sideA.life > sv.Fix.nl then None
  else
    match Fix.key_gen false s with
    | exception _ -> None
    | k ->
      match Fix.id sv k with
      | exception Not_found -> None
      | i -> if Fix.base_key_at sv (i mod sv.Fix.nb) <> Fix.base_of k then None else Some i

let finite t v = v < Fix.inf && v <= t.lmax

(* The table's entry for [s]. *)
let lookup t s =
  match index t s with
  | Some i -> let v = Fix.get t.sv i in if finite t v then Some (max v 0) else None
  | None -> None

(* The oracle: [check_node]'s search, memoised. *)
module H = Hashtbl.Make (struct
    type t = state
    let equal = ( = )
    let hash = Hashtbl.hash_param 100 400
  end)

let oracle t lk =
  let memo = H.create 1024 in
  let rec ok root s =
    match winner s with
    | Some PB -> true
    | Some PA -> false
    | None ->
      if (not root) && is_turn_start s then
        (match lk (key t.h t.tt s) with Some v -> v <= s.sideB.life | None -> false)
      else if huge_event t.h s then false
      else
        match H.find_opt memo s with
        | Some r -> r
        | None ->
          let r =
            match to_move s with
            | PB -> List.exists (next s) (moves s)
            | PA -> List.for_all (next s) (moves s)
          in
          H.replace memo s r;
          r
  and next s m =
    let s' = step s m in
    (not (too_many t.ott s')) && ok false s'
  in
  let hint s m = next s m in
  (memo, ok, hint)

(* The certificate's domain: every state [lookup] answers for. *)
let entries t b f =
  let sv = t.sv in
  let k = Fix.base_key_at sv b in
  for slot = 0 to sv.Fix.nl - 1 do
    let i = (slot * sv.Fix.nb) + b in
    let v = Fix.get sv i in
    if v < Fix.inf && v <= t.lmax then begin
      let s0 = Fix.of_key (Fix.with_life k (Fix.life_of_slot sv slot)) in
      let s0 = { s0 with sideB = { s0.sideB with life = 0 } } in
      List.iter (fun abf ->
          List.iter (fun bbf ->
              let s = { s0 with sideA = { s0.sideA with bf = abf }; sideB = { s0.sideB with bf = bbf } } in
              match lookup t s with
              | Some v -> f s v
              | None -> failwith "certify: an enumerated state has no entry")
            (perms s0.sideB.bf))
        (perms s0.sideA.bf)
    end
  done

(* Check bases [lo, hi): (entries, failures). Failures go to [out]. *)
let check_range t lo hi out =
  let lk = lookup t in
  let n = ref 0 and bad = ref 0 in
  for b = lo to hi - 1 do
    entries t b (fun s v ->
        incr n;
        let memo, _, hint = oracle t lk in
        if not (check_node t.h t.ott t.tt lk hint fuel true (entry s v)) then begin
          incr bad;
          Printf.fprintf out "%s %d\n" (Fix.hex (Fix.key_gen false s)) v
        end;
        H.reset memo)
  done;
  (!n, !bad)

let run dir starter =
  let t = open_table dir in
  let nb = t.sv.Fix.nb in
  let lo, hi =
    match Sys.getenv_opt "TCB_RANGE" with
    | Some r -> Scanf.sscanf r "%d:%d" (fun a b -> (a, min b nb))
    | None -> (0, nb)
  in
  let w = Par.workers (hi - lo) 1000 in
  Printf.printf "certify %s: bases %d..%d, h=%d ott=%d tt=%d, %d workers\n%!" dir lo hi t.h t.ott t.tt w;
  let t0 = Unix.gettimeofday () in
  let res =
    Par.map ~dir w (fun k ->
        let a, b = Par.chunk (hi - lo) w k in
        let out = open_out (Filename.concat dir (Printf.sprintf "certify-fail-%d" k)) in
        let n, bad = check_range t (lo + a) (lo + b) out in
        close_out out;
        (n lsl 24) lor bad)
  in
  let n = Array.fold_left (fun acc r -> acc + (r lsr 24)) 0 res in
  let bad = Array.fold_left (fun acc r -> acc + (r land 0xffffff)) 0 res in
  Printf.printf "checked %d entries, %d failed (%.1fs)\n" n bad (Unix.gettimeofday () -. t0);
  let s0 = init starter in
  (match lookup t (key t.h t.tt s0) with
   | Some v -> Printf.printf "opening entry: B needs %d life (has %d)\n" v s0.sideB.life
   | None -> print_endline "opening: no entry");
  if bad = 0 && lo = 0 && hi = nb then
    match lookup t (key t.h t.tt s0) with
    | Some v when v <= 20 -> print_endline "certified: B does not lose from the opening"
    | _ -> print_endline "not certified"

(* Trace why the entry [hex] (a key as printed in a failure file) fails:
   B's first working move at each node, or every move when none works. *)
let debug dir hex v =
  let t = open_table dir in
  let lk = lookup t in
  let s = Fix.of_key (Fix.unhex hex) in
  let s = entry { s with sideB = { s.sideB with life = 0 } } v in
  let _, ok, _ = oracle t lk in
  Printf.printf "oracle at root: %b\n%s\n" (ok true s) (Show.state s);
  let rec go depth s =
    if depth < 60 && winner s = None && (depth = 0 || not (is_turn_start s)) then begin
      let ms = moves s in
      let res = List.map (fun m ->
          let s' = step s m in
          let r = if huge_event t.h s then "huge" else if too_many t.ott s' then "many"
            else string_of_bool (ok false s') in
          (m, s', r)) ms in
      Printf.printf "%s%s to move: %s\n" (String.make depth ' ') (Show.player (to_move s))
        (String.concat ", " (List.map (fun (m, _, r) -> Show.move m ^ "=" ^ r) res));
      let pick =
        match to_move s with
        | PB -> (match List.find_opt (fun (_, _, r) -> r = "true") res with Some x -> Some x | None -> List.nth_opt res 0)
        | PA -> (match List.find_opt (fun (_, _, r) -> r <> "true") res with Some x -> Some x | None -> List.nth_opt res 0)
      in
      match pick with Some (_, s', _) -> go (depth + 1) s' | None -> ()
    end
    else if is_turn_start s then
      Printf.printf "%sturn start: lookup %s, B life %d\n%s\n" (String.make depth ' ')
        (match lk (key t.h t.tt s) with Some v -> string_of_int v | None -> "none") s.sideB.life (Show.state s)
  in
  go 0 s

(* ** Win certificates (WinCert.v)

   A B-win table solved with TCB_RANKS=1 logs every value change: position
   [i] has records (round, value) in [hrec] from offset [hidx.{i}]. Record
   ranks are lexicographic, A's life level first: [slot * level + round].
   Only the records B's strategy from the opening uses are checked: an
   untrusted pass collects them by running [check_win] with a logging
   lookup, then every collected record is checked again with [lookup]
   restricted to exactly that set. *)

let level = 1_000_000

type wtable = {
  wt : table;
  hidx : (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array1.t;
  hrec : (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t;
}

let open_win dir =
  let t = open_table dir in
  let meta = Fix.read_meta dir in
  if List.assoc "mode" meta <> "win" then failwith "certify-win: needs a win table";
  let n = t.sv.Fix.n in
  let hidx = Fix.(Disk.map Bigarray.int64 (Filename.concat dir "hidx") (n + 1) ~write:false) in
  let nrec = Int64.to_int hidx.{n} in
  { wt = t; hidx; hrec = Disk.map Bigarray.int32 (Filename.concat dir "hrec") (2 * nrec) ~write:false }

let recs w i = (Int64.to_int w.hidx.{i}, Int64.to_int w.hidx.{i + 1})
let rank w i p = ((i / w.wt.sv.Fix.nb) * level) + Int32.to_int w.hrec.{2 * p}
let rval w p = Fix.of32 (Int32.to_int w.hrec.{(2 * p) + 1})

(* The value of position [i]'s record of rank [r]. *)
let record w i r =
  let a, b = recs w i in
  let rec go p = if p >= b then None else if rank w i p = r then Some (rval w p) else go (p + 1) in
  match go a with Some v when finite w.wt v -> Some (max v 0) | _ -> None

(* The latest record of [i] below rank [r]. *)
let below_rec w i r =
  let a, b = recs w i in
  let best = ref None in
  for p = a to b - 1 do
    if rank w i p < r && finite w.wt (rval w p) then best := Some (rank w i p)
  done;
  !best

let win_oracle w lk below =
  let t = w.wt in
  let memo = H.create 1024 in
  let rec ok r root s =
    match winner s with
    | Some PB -> true
    | Some PA -> false
    | None ->
      if (not root) && is_turn_start s then
        let k = key t.h t.tt s in
        (match below k r with
         | Some r' -> r' < r && (match lk k r' with Some v -> v <= s.sideB.life | None -> false)
         | None -> false)
      else if huge_event t.h s then false
      else
        match H.find_opt memo s with
        | Some x -> x
        | None ->
          let x =
            match to_move s with
            | PB -> List.exists (next r s) (moves s)
            | PA -> moves s <> [] && List.for_all (next r s) (moves s)
          in
          H.replace memo s x;
          x
  and next r s m =
    let s' = step s m in
    (not (too_many t.ott s')) && ok r false s'
  in
  (memo, ok)

(* The states a record stands for: every order of the Walkers. *)
let record_states w i =
  let t = w.wt in
  let s0 = Fix.of_key (Fix.key_at t.sv i) in
  let s0 = { s0 with sideB = { s0.sideB with life = 0 } } in
  List.concat_map (fun abf ->
      List.map (fun bbf -> { s0 with sideA = { s0.sideA with bf = abf }; sideB = { s0.sideB with bf = bbf } })
        (perms s0.sideB.bf))
    (perms s0.sideA.bf)

let certify_win dir starter =
  let w = open_win dir in
  let t = w.wt in
  let t0 = Unix.gettimeofday () in
  let below s r = match index t s with Some i -> below_rec w i r | None -> None in
  let full s r = match index t s with Some i -> record w i r | None -> None in
  (* the opening's lowest-rank record on at most 20 life *)
  let s0 = init starter in
  let k0 = key t.h t.tt s0 in
  let i0 = match index t k0 with Some i -> i | None -> failwith "certify-win: the opening has no position" in
  let a, b = recs w i0 in
  let r0 =
    let rec go p = if p >= b then failwith "certify-win: no opening record on 20 life"
      else if rval w p <= s0.sideB.life then rank w i0 p else go (p + 1) in
    go a
  in
  (* pass 1: collect the records the check uses *)
  let used = Hashtbl.create 100_000 in
  let queue = Queue.create () in
  let add i r = if not (Hashtbl.mem used (i, r)) then (Hashtbl.replace used (i, r) (); Queue.push (i, r) queue) in
  add i0 r0;
  let logging s r =
    match full s r with
    | Some v -> (match index t s with Some i -> add i r | None -> ()); Some v
    | None -> None
  in
  let check lk (i, r) =
    let memo, ok = win_oracle w full below in
    let hint s m = let s' = step s m in (not (too_many t.ott s')) && ok r false s' in
    let res =
      List.for_all (fun s ->
          match lk s r with
          | Some v -> check_win t.h t.ott t.tt lk below hint r fuel true (entry s v)
          | None -> false)
        (record_states w i)
    in
    H.reset memo;
    res
  in
  let bad1 = ref 0 in
  while not (Queue.is_empty queue) do
    if not (check logging (Queue.pop queue)) then incr bad1
  done;
  let d = Hashtbl.length used in
  Printf.printf "pass 1: %d records collected, %d failed (%.1fs)\n%!" d !bad1 (Unix.gettimeofday () -. t0);
  (* pass 2: the same check with lookup restricted to the collected set *)
  let restricted s r =
    match index t s with
    | Some i when Hashtbl.mem used (i, r) -> record w i r
    | _ -> None
  in
  let bad = Hashtbl.fold (fun ir () acc -> if check restricted ir then acc else acc + 1) used 0 in
  let states = Hashtbl.fold (fun (i, _) () acc -> acc + List.length (record_states w i)) used 0 in
  Printf.printf "pass 2: %d records (%d states) checked, %d failed (%.1fs)\n" d states bad (Unix.gettimeofday () -. t0);
  match restricted k0 r0 with
  | Some v ->
    Printf.printf "opening record: rank %d, B needs %d life (has %d)\n" r0 v s0.sideB.life;
    if bad = 0 && v <= 20 then print_endline "certified: B wins from the opening"
    else print_endline "not certified"
  | None -> print_endline "not certified: the opening record is missing"
