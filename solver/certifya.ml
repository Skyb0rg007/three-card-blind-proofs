(* Driver for the extracted A-safe checker with a growing Walker
   (proofs/core/CheckerA.v).

   [CheckerA.cert_safe] says: if [lookup k = Some (c, b)] implies
   [check_node K Hb ott tt lookup hint fuel true (entry M k) c b = true] for
   every [k], then A is safe from every real state an entry abstracts, at a
   B life on or below the entry's line. Nothing is assumed about [lookup]
   and [hint].

   The table is a BIG A-safe table saved by rsolver ([TCB_BIG=1
   TCB_SAVE=DIR rsolver fix safe A T TT LMAX A]): [dig] and [keys] (bases in
   digest order), [vals] (c per position, int32, A-life level major) and
   [beta] (b per position, one byte). [lookup] reads it for states in key
   form, up to the order of the Walkers (the solver's keys are sorted), so
   it answers for every real order.

   As in [Certify.certify_safe_export], only the entries the check of the
   opening consults are kept: pass 1 runs [check_node] from the opening's
   entry with a logging lookup and a memoised oracle for A's moves, and
   collects the closure; pass 2 checks every collected entry again with
   [lookup] restricted to the closure, as Rocq will. *)
open Model

type params = { k : int; hb : int; ott : int; tt : int; m : int; fuel : int }

type table = { sv : Fix.solver; beta : (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t }

let open_table dir =
  let nb = Disk.count (Filename.concat dir "dig") 8 in
  let n = Disk.count (Filename.concat dir "vals") 4 in
  if nb = 0 || n mod nb <> 0 || Disk.count (Filename.concat dir "beta") 1 <> n then
    failwith "certify-a: dig, vals and beta don't match";
  let nl = n / nb in
  let sv = Fix.open_dir dir ~nb ~nl ~write:false in
  { sv; beta = Disk.map Bigarray.char (Filename.concat dir "beta") n ~write:false }

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

let line t i =
  let c = Fix.get t.sv i and b = Char.code t.beta.{i} in
  if b > 127 then failwith "certify-a: negative beta";
  (c, b)

(* The table's line for [s]. A lost position has no entry. A position safe
   at every B life (c = inf) would need an unbounded c; there are none in
   the tables seen so far, so it is refused loudly. *)
let lookup t s =
  match index t s with
  | None -> None
  | Some i ->
    let c, b = line t i in
    if c <= Fix.ninf then None
    else if c >= Fix.inf then failwith "certify-a: a line with c = inf"
    else Some (c, b)

let blife s = s.sideB.life

(* The oracle: [check_node]'s search, memoised on (state, line, root). For
   each A node it records the moves that work, under any line; the hint
   allows exactly those, so the checker only follows A's working moves. *)
module H = Hashtbl.Make (struct
    type t = state * int * int * int * bool
    let equal = ( = )
    let hash = Hashtbl.hash_param 100 400
  end)

module S = Hashtbl.Make (struct
    type t = state
    let equal = ( = )
    let hash = Hashtbl.hash_param 100 400
  end)

let oracle p lk =
  let memo = H.create 1024 and good = S.create 256 in
  let rec ok root s c b lo =
    match winner s with
    | Some _ -> false
    | None ->
      if (not root) && is_turn_start s then
        match lk (a_key p.hb p.tt s) with
        | Some (c', b') -> c + (b * lo) <= c' + (b' * lo) && ((not (a_has_big p.k s)) || b <= b')
        | None -> false
      else if a_huge_event p.hb s || a_big_event p.k s then false
      else
        match H.find_opt memo (s, c, b, lo, root) with
        | Some r -> r
        | None ->
          let r =
            match to_move s with
            | PA ->
              (match List.find_opt (fun m -> next s c b lo m) (moves s) with
               | Some m ->
                 let l = Option.value (S.find_opt good s) ~default:[] in
                 if not (List.mem m l) then S.replace good s (m :: l);
                 true
               | None -> false)
            | PB -> List.for_all (next s c b lo) (moves s)
          in
          H.replace memo (s, c, b, lo, root) r;
          r
  and next s c b lo m =
    if a_is_create p.k s m && a_has_big p.k s then false
    else
      let s' = a_stepA p.k p.hb p.tt s m in
      if a_too_many p.ott s' then false
      else
        match winner s' with
        | Some _ -> false
        | None ->
          let c1 = if a_is_pump_big p.k s m then c - b else c in
          let b1 = if a_is_create p.k s m then 0 else b in
          let c2 = c1 + (blife s' - blife s) in
          let b2 = if a_is_hit p.k s then b1 - 1 else b1 in
          let lo2 = if a_is_pump_big p.k s m then lo + 1 else if a_is_create p.k s m then 0 else lo in
          if c2 + (b2 * lo2) <= 0 && b2 <= 0 then true else ok false s' c2 b2 lo2
  in
  let hint s m = match S.find_opt good s with Some l -> List.mem m l | None -> false in
  let reset () = H.reset memo; S.reset good in
  (ok, hint, reset)

let check p lk hint s c b = a_check_node p.k p.hb p.ott p.tt lk hint p.fuel true (a_entry p.m s) c b 0

(* The solver's line for a node (rsolver's [eval_go_big] for A-safe, over
   every legal move): A's nodes pick the line larger at n = [r], B's take
   the componentwise min, edges apply [ltrans]. [None] is lost for A. *)
let solver_line p lk r =
  let memo = S.create 1024 in
  let pick a b =
    match a, b with
    | None, x | x, None -> x
    | Some (c, b), Some (c', b') -> if (c + (b * r), c, b) >= (c' + (b' * r), c', b') then a else Some (c', b')
  in
  let lmin a b = match a, b with Some (c, b), Some (c', b') -> Some (min c c', min b b') | _ -> None in
  let rec node root s =
    match winner s with
    | Some _ -> None
    | None ->
      if (not root) && is_turn_start s then lk (a_key p.hb p.tt s)
      else if a_huge_event p.hb s || a_big_event p.k s then None
      else
        match S.find_opt memo s with
        | Some v when not root -> v
        | _ ->
          let vs = List.map (edge s) (moves s) in
          let v =
            match to_move s with
            | PA -> List.fold_left pick None vs
            | PB -> (match vs with [] -> None | x :: l -> List.fold_left lmin x l)
          in
          if not root then S.replace memo s v;
          v
  and edge s m =
    if a_is_create p.k s m && a_has_big p.k s then None
    else
      let s' = a_stepA p.k p.hb p.tt s m in
      if a_too_many p.ott s' then None
      else
        match winner s' with
        | Some _ -> None
        | None ->
          let d = blife s' - blife s and hit = if a_is_hit p.k s then 1 else 0 in
          let v =
            match node false s' with
            | None -> None
            | Some (c, b) ->
              let b = if a_is_create p.k s m then 0 else b in
              let c = if a_is_pump_big p.k s m then c + b else c in
              Some (c - d, b + hit)
          in
          if d < 0 then pick (Some (-d, hit)) v else v
  in
  (node, edge)

(* Why [check_node] fails from the entry [s] with line (c, b). At each node
   every move is shown with the line it asks of the child (CheckerA) and
   the child's solver line seen from here; A follows the solver's choice,
   B its first move whose child fails. *)
let explain p lk s0 c0 b0 =
  let ok, _, _ = oracle p lk in
  let node, sedge = solver_line p lk 20 in
  let s0 = a_entry p.m s0 in
  let sl = function None -> "lost" | Some (c, b) -> Printf.sprintf "(%d,%d)" c b in
  Printf.printf "entry line (%d, %d), oracle %b, solver %s\n%s\n" c0 b0 (ok true s0 c0 b0 0) (sl (node true s0))
    (Show.state s0);
  let edge s c b lo m =
    if a_is_create p.k s m && a_has_big p.k s then (None, "second BIG")
    else
      let s' = a_stepA p.k p.hb p.tt s m in
      if a_too_many p.ott s' then (None, "too many B Thopters")
      else
        match winner s' with
        | Some w -> (None, Show.player w ^ " wins")
        | None ->
          let c1 = if a_is_pump_big p.k s m then c - b else c in
          let b1 = if a_is_create p.k s m then 0 else b in
          let c2 = c1 + (blife s' - blife s) in
          let b2 = if a_is_hit p.k s then b1 - 1 else b1 in
          let flags = String.concat "" [ (if a_is_pump_big p.k s m then " pump-BIG" else "");
                                         (if a_is_create p.k s m then " create" else "");
                                         (if a_is_hit p.k s then " hit" else "");
                                         (Printf.sprintf " d=%d" (blife s' - blife s)) ] in
          let lo2 = if a_is_pump_big p.k s m then lo + 1 else if a_is_create p.k s m then 0 else lo in
          if c2 + (b2 * lo2) <= 0 && b2 <= 0 then (None, "B dead" ^ flags)
          else (Some (s', c2, b2, lo2), Printf.sprintf "(%d,%d)%s %b" c2 b2 flags (ok false s' c2 b2 lo2))
  in
  let rec go depth root s c b lo =
    let ind = String.make (2 * depth) ' ' in
    match winner s with
    | Some w -> Printf.printf "%s%s wins\n" ind (Show.player w)
    | None ->
      if (not root) && is_turn_start s then begin
        let k = a_key p.hb p.tt s in
        Printf.printf "%sturn start, needs (%d, %d) for n >= %d%s, table %s, packed key %d %d\n%s%s\n" ind c b lo
          (if a_has_big p.k s then " BIG" else "")
          (match lk k with Some (c', b') -> Printf.sprintf "(%d, %d)" c' b' | None -> "none")
          (fst (Certify.enc k)) (snd (Certify.enc k)) ind (Show.state s)
      end
      else if a_huge_event p.hb s then Printf.printf "%shuge event\n%s\n" ind (Show.state s)
      else if a_big_event p.k s then Printf.printf "%sBIG could die\n%s\n" ind (Show.state s)
      else if depth > 80 then print_endline "too deep"
      else begin
        let res = List.map (fun m -> (m, edge s c b lo m, sedge s m)) (moves s) in
        Printf.printf "%s%s to move, line (%d, %d), solver %s: %s\n" ind (Show.player (to_move s)) c b
          (sl (node true s))
          (String.concat "; " (List.map (fun (m, (_, r), v) -> Show.move m ^ " -> " ^ r ^ " solver " ^ sl v) res));
        let failing (_, (nx, r), _) =
          match nx with
          | Some (s', c', b', lo') -> not (ok false s' c' b' lo')
          | None -> not (String.length r >= 6 && String.sub r 0 6 = "B dead")
        in
        let pick =
          match to_move s with
          | PB -> List.find_opt failing res
          | PA ->
            let best = node true s in
            List.find_opt (fun (_, _, v) -> v = best) res
        in
        match pick with
        | Some (m, (Some (s', c', b', lo'), _), _) ->
          Printf.printf "%s> %s %s\n" ind (Show.player (to_move s)) (Show.move m);
          go (depth + 1) false s' c' b' lo'
        | Some (m, (None, r), _) -> Printf.printf "%s> %s %s: %s\n" ind (Show.player (to_move s)) (Show.move m) r
        | None -> ()
      end
  in
  go 0 true s0 c0 b0 0

(* The collected entries, outside the OCaml heap so that the forked workers
   share them (a heap would be copied page by page as their GC marks it):
   an open-addressing table over memory-mapped files, keyed by the packed
   key (stored + 1, so 0 is empty). The files outlive the process, so a run
   that is stopped can resume. *)
module Tbl = struct
  open Bigarray

  type t = {
    cap : int;
    a : (int, int_elt, c_layout) Array1.t;
    b : (int, int_elt, c_layout) Array1.t;
    v : (int, int_elt, c_layout) Array1.t;
    mutable n : int;
  }

  let rec probe t k1 k2 i =
    let x = Array1.unsafe_get t.a i in
    if x = 0 || (x = k1 + 1 && Array1.unsafe_get t.b i = k2) then i else probe t k1 k2 ((i + 1) land (t.cap - 1))

  let slot t (k1, k2) = probe t k1 k2 (Hashtbl.hash (k1, k2) land (t.cap - 1))
  let find t e = let i = slot t e in if t.a.{i} = 0 then None else Some t.v.{i}
  let mem t e = find t e <> None

  let add t ((k1, k2) as e) v =
    let i = slot t e in
    if t.a.{i} = 0 then begin
      if 2 * (t.n + 1) > t.cap then failwith "certify-a: the entry table is full (raise TCB_CAP)";
      t.a.{i} <- k1 + 1; t.b.{i} <- k2; t.v.{i} <- v; t.n <- t.n + 1;
      true
    end
    else false

  (* Slots [lo, hi) that hold entries. *)
  let iter_range t lo hi f = for i = lo to hi - 1 do if t.a.{i} <> 0 then f (t.a.{i} - 1, t.b.{i}) t.v.{i} done

  (* A new table at [base], or the one there when [keep]. *)
  let create ~keep base cap =
    if cap land (cap - 1) <> 0 then failwith "certify-a: TCB_CAP must be a power of 2";
    let m s =
      let p = base ^ s in
      if not keep then Disk.remove p;
      Disk.map int p cap ~write:true
    in
    let t = { cap; a = m ".a"; b = m ".b"; v = m ".v"; n = 0 } in
    iter_range t 0 cap (fun _ _ -> t.n <- t.n + 1);
    t
end

(* Entries are packed as [Certify.enc] does (Packed.v's layout; [dec] below
   inverts it). *)
let enc = Certify.enc

let field x off w = (x lsr off) land ((1 lsl w) - 1)
let bit x off = field x off 1 = 1

let dec_side x =
  let dw o = { counters = field x o 5; wtapped = bit x (o + 5); sick = bit x (o + 6) } in
  let card o = if bit x o then CElixir else CWalker in
  { life = field x 0 5; city = bit x 5; pool = field x 6 3; hand_w = field x 9 2; hand_e = bit x 11;
    bf = List.filteri (fun j _ -> j < field x 25 2) [ dw 27; dw 34; dw 41 ]; elixir_bf = bit x 12;
    thop_u = field x 13 5; thop_t = field x 18 5;
    library = List.filteri (fun j _ -> j < field x 48 2) [ card 50; card 51; card 52 ]; gy_w = field x 23 2 }

let dec (k1, k2) =
  let p = if bit k1 53 then PB else PA in
  { active = p; first_turn = bit k1 54; sideA = dec_side k1; sideB = dec_side k2; cmb = no_combat;
    pend = Window (Upkeep, p, false) }

(* An entry's value: its line, and the layer of pass 1 that found it. *)
let venc (c, b) layer = (((c + 4096) lsl 4) lor b) lsl 12 lor layer
let vline v = (((v lsr 12) lsr 4) - 4096, (v lsr 12) land 15)
let vlayer v = v land 4095

let read_lines path f =
  let ic = open_in path in
  (try while true do f (input_line ic) done with End_of_file -> ());
  close_in ic;
  Sys.remove path

let write_file path s =
  let oc = open_out (path ^ ".tmp") in
  output_string oc s;
  close_out oc;
  Sys.rename (path ^ ".tmp") path

(* [certify-a]. Progress is kept in OUT.state*: the entry table, and a line
   saying how far the passes got, so TCB_RESUME=1 continues a stopped run.
   Pass 1 layer L checks the entries found by layer L - 1 (the opening is
   layer 0); the state line "pass1 L F" means layers up to L are done (F
   failures), "pass2 K F" that K of pass 2's slices are. *)
let run dir starter outfile p =
  let t = open_table dir in
  let lk = lookup t in
  let wdir = Filename.dirname outfile in
  let st = outfile ^ ".state" in
  let resume = Sys.getenv_opt "TCB_RESUME" = Some "1" && Sys.file_exists st in
  let t0 = Unix.gettimeofday () in
  let cap = 1 lsl (match Sys.getenv_opt "TCB_CAP" with Some c -> int_of_string c | None -> 24) in
  Printf.printf "certify-a %s: %d bases, %d levels; K=%d Hb=%d ott=%d tt=%d M=%d fuel=%d\n%!" dir t.sv.Fix.nb
    t.sv.Fix.nl p.k p.hb p.ott p.tt p.m p.fuel;
  let s0 = init starter in
  let k0 = a_key p.hb p.tt s0 in
  let c0, b0 = match lk k0 with Some v -> v | None -> failwith "certify-a: the opening has no entry" in
  Printf.printf "opening: line (%d, %d), B has %d life, BIG %b\n%!" c0 b0 s0.sideB.life (a_has_big p.k s0);
  let key_of s =
    let e = enc s in
    if dec e <> s then failwith ("certify-a: a state the packing doesn't keep: " ^ Show.state s);
    e
  in
  let used = Tbl.create ~keep:resume (st ^ "-used") cap in
  let phase, done_, fails =
    if resume then (
      let ic = open_in st in
      let r = Scanf.sscanf (input_line ic) "%s %d %d" (fun a b c -> (a, b, c)) in
      close_in ic;
      let a, b, c = r in
      Printf.printf "resuming: %s %d (%d failed), %d entries\n%!" a b c used.Tbl.n;
      r)
    else (
      ignore (Tbl.add used (key_of k0) (venc (c0, b0) 0));
      write_file st "pass1 -1 0\n";
      ("pass1", -1, 0))
  in
  let fails = ref fails in
  (* pass 1, a layer at a time: the workers check a slice of the layer each
     and write the entries their checks consult that aren't known yet *)
  if phase = "pass1" then begin
    let failf = open_out_gen [ Open_append; Open_creat ] 0o644 (outfile ^ ".fail") in
    let shown = ref 0 and layer = ref (done_ + 1) and continue = ref true in
    while !continue do
      let l = !layer in
      let fr = ref [] in
      Tbl.iter_range used 0 cap (fun e v -> if vlayer v = l then fr := e :: !fr);
      let fr = Array.of_list !fr in
      let nf = Array.length fr in
      if nf = 0 then continue := false
      else begin
        let w = Par.workers nf 2000 in
        let pid = Unix.getpid () in
        let name k = Filename.concat wdir (Printf.sprintf "certa-%d-layer-%d" pid k) in
        let bad =
          Par.map ~dir:wdir w (fun k ->
              let a, b = Par.chunk nf w k in
              let oc = open_out (name k) in
              let seen = Hashtbl.create 1024 in
              let logging s =
                match lk s with
                | Some v ->
                  let e = key_of s in
                  if not (Tbl.mem used e || Hashtbl.mem seen e) then begin
                    Hashtbl.replace seen e ();
                    let k1, k2 = e in
                    Printf.fprintf oc "+ %d %d %d\n" k1 k2 (venc v (l + 1))
                  end;
                  Some v
                | None -> None
              in
              let ok, hint, reset = oracle p lk in
              let bad = ref 0 in
              for j = a to b - 1 do
                let s = dec fr.(j) and c, b = vline (Option.get (Tbl.find used fr.(j))) in
                reset ();
                let o = ok true (a_entry p.m s) c b 0 in
                let r = check p logging hint s c b in
                if r <> o then Printf.fprintf oc "! %d %d disagree\n" (fst fr.(j)) (snd fr.(j));
                if not r then begin
                  incr bad;
                  Printf.fprintf oc "- %d %d\n" (fst fr.(j)) (snd fr.(j))
                end
              done;
              close_out oc;
              !bad)
        in
        let nnew = ref 0 in
        for k = 0 to w - 1 do
          read_lines (name k) (fun line ->
              match String.split_on_char ' ' line with
              | [ "+"; k1; k2; v ] -> if Tbl.add used (int_of_string k1, int_of_string k2) (int_of_string v) then incr nnew
              | [ "-"; k1; k2 ] ->
                let e = (int_of_string k1, int_of_string k2) in
                let c, b = vline (Option.get (Tbl.find used e)) in
                incr fails;
                Printf.fprintf failf "%s %s %d %d\n%!" k1 k2 c b;
                if !shown < 3 then (incr shown; explain p lk (dec e) c b)
              | _ -> print_endline line)
        done;
        write_file st (Printf.sprintf "pass1 %d %d\n" l !fails);
        Printf.printf "  pass 1, layer %d: %d checked (%d failed), %d new, %d collected (%.0fs)\n%!" l nf
          (Array.fold_left ( + ) 0 bad) !nnew used.Tbl.n (Unix.gettimeofday () -. t0);
        incr layer
      end
    done;
    close_out failf;
    write_file st (Printf.sprintf "pass2 0 %d\n" !fails)
  end;
  let n = used.Tbl.n in
  Printf.printf "pass 1: %d entries collected, %d failed so far (%.1fs)\n%!" n !fails (Unix.gettimeofday () -. t0);
  (* pass 2: lookup restricted to the closure, as Rocq will; A's moves from
     the oracle, or every move with TCB_HINT=all (as Rocq's hint), in
     slices of the table *)
  let restricted s =
    let e = enc s in
    match Tbl.find used e with Some v when dec e = s -> Some (vline v) | _ -> None
  in
  let all = Sys.getenv_opt "TCB_HINT" = Some "all" in
  let slices = 32 in
  let bad2 = ref 0 in
  for sl = (if phase = "pass2" then done_ else 0) to slices - 1 do
    let lo, hi = Par.chunk cap slices sl in
    let w = Par.workers n 2000 in
    let bad =
      Par.map ~dir:wdir w (fun k ->
          let a, b = Par.chunk (hi - lo) w k in
          let ok2, hint2, reset2 = oracle p restricted in
          let bad = ref 0 in
          Tbl.iter_range used (lo + a) (lo + b) (fun e v ->
              let s = dec e and c, b = vline v in
              let h = if all then (fun _ _ -> true) else (reset2 (); ignore (ok2 true (a_entry p.m s) c b 0); hint2) in
              if not (check p restricted h s c b) then incr bad);
          !bad)
      |> Array.fold_left ( + ) 0
    in
    bad2 := !bad2 + bad;
    fails := !fails + bad;
    write_file st (Printf.sprintf "pass2 %d %d\n" (sl + 1) !fails);
    Printf.printf "  pass 2: slice %d of %d, %d failed in this run (%.0fs)\n%!" (sl + 1) slices !bad2 (Unix.gettimeofday () -. t0)
  done;
  Printf.printf "pass 2 (closure only, hint %s): %d of %d failed in this run; %d failures in all (%.1fs)\n%!"
    (if all then "all" else "oracle") !bad2 n !fails
    (Unix.gettimeofday () -. t0);
  (* the entries, sorted by packed key *)
  let raw = st ^ "-entries" in
  let oc = open_out raw in
  let minc = ref max_int and maxc = ref min_int and maxb = ref 0 in
  Tbl.iter_range used 0 cap (fun (k1, k2) v ->
      let c, b = vline v in
      minc := min !minc c; maxc := max !maxc c; maxb := max !maxb b;
      Printf.fprintf oc "%d %d %d %d\n" k1 k2 c b);
  close_out oc;
  let oc = open_out outfile in
  Printf.fprintf oc "# certify-a %s K=%d Hb=%d ott=%d tt=%d M=%d: %d entries; k1 k2 c b (Packed.enc keys, sorted)\n" dir
    p.k p.hb p.ott p.tt p.m n;
  close_out oc;
  if Sys.command (Printf.sprintf "LC_ALL=C sort -n -k1,1 -k2,2 %s >> %s" (Filename.quote raw) (Filename.quote outfile)) <> 0
  then failwith "certify-a: sort failed";
  Sys.remove raw;
  Printf.printf "wrote %d entries to %s (c in %d..%d, b up to %d)\n" n outfile !minc !maxc !maxb;
  if !fails = 0 && b0 = 0 && c0 >= s0.sideB.life then begin
    print_endline "certified: A is safe from the opening";
    List.iter (fun s -> Disk.remove (st ^ "-used" ^ s)) [ ".a"; ".b"; ".v" ];
    Disk.remove st
  end
  else print_endline "not certified"

(* [explain] for an entry given by its packed key. *)
let debug_packed dir k1 k2 c b p =
  let t = open_table dir in
  explain p (lookup t) (dec (k1, k2)) c b

let debug dir hex c b p =
  let t = open_table dir in
  let s = Fix.of_key (Fix.unhex hex) in
  let s = { s with sideB = { s.sideB with life = 0 } } in
  explain p (lookup t) s c b

(* The table's line for the position packed as (k1, k2) at every A life. *)
let levels dir k1 k2 =
  let t = open_table dir in
  let s = dec (k1, k2) in
  Printf.printf "%s\n" (Show.state s);
  for l = 1 to t.sv.Fix.nl do
    let s = { s with sideA = { s.sideA with life = l } } in
    Printf.printf "A life %2d: %s\n" l
      (match index t s with
       | None -> "no position"
       | Some i -> let c, b = line t i in if c <= Fix.ninf then "lost" else Printf.sprintf "(%d, %d)" c b)
  done
