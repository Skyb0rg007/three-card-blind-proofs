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

(* TCB_CHOOSE=1 (experiment): A's moves chosen to add the least weight
   [w] of turn-start keys (A's nodes the minimum over their working moves,
   B's the sum over its moves). The hint allows exactly the chosen moves. *)
let chooser p lk (w : state -> float) =
  let memo = H.create 1024 and good = S.create 256 in
  let inf = infinity in
  let rec cost root s c b lo =
    match winner s with
    | Some _ -> inf
    | None ->
      if (not root) && is_turn_start s then
        let k = a_key p.hb p.tt s in
        match lk k with
        | Some (c', b') when c + (b * lo) <= c' + (b' * lo) && ((not (a_has_big p.k s)) || b <= b') -> w k
        | _ -> inf
      else if a_huge_event p.hb s || a_big_event p.k s then inf
      else
        match H.find_opt memo (s, c, b, lo, root) with
        | Some r -> if r < 0. then inf else r
        | None ->
          let r =
            match to_move s with
            | PA ->
              let best = ref inf and bm = ref None in
              List.iter (fun m -> let x = next s c b lo m in if x < !best then (best := x; bm := Some m)) (moves s);
              (match !bm with
               | Some m ->
                 let l = Option.value (S.find_opt good s) ~default:[] in
                 if not (List.mem m l) then S.replace good s (m :: l)
               | None -> ());
              !best
            | PB -> List.fold_left (fun acc m -> if acc = inf then inf else acc +. next s c b lo m) 0. (moves s)
          in
          H.replace memo (s, c, b, lo, root) (if r = inf then -1. else r);
          r
  and next s c b lo m =
    if a_is_create p.k s m && a_has_big p.k s then inf
    else
      let s' = a_stepA p.k p.hb p.tt s m in
      if a_too_many p.ott s' then inf
      else
        match winner s' with
        | Some _ -> inf
        | None ->
          let c1 = if a_is_pump_big p.k s m then c - b else c in
          let b1 = if a_is_create p.k s m then 0 else b in
          let c2 = c1 + (blife s' - blife s) in
          let b2 = if a_is_hit p.k s then b1 - 1 else b1 in
          let lo2 = if a_is_pump_big p.k s m then lo + 1 else if a_is_create p.k s m then 0 else lo in
          if c2 + (b2 * lo2) <= 0 && b2 <= 0 then 0. else cost false s' c2 b2 lo2
  in
  let ok root s c b lo = cost root s c b lo < inf in
  let hint s m = match S.find_opt good s with Some l -> List.mem m l | None -> false in
  let reset () = H.reset memo; S.reset good in
  (ok, hint, reset)

let check p lk hint s c b = a_check_node p.k p.hb p.ott p.tt lk hint p.fuel true (a_entry p.m s) c b 0

(* Does the line (c', b') at a turn start [s] meet what [check_node] asks
   there of the line (c, b) with lower bound [lo]? *)
let meets p s c b lo (c', b') = c + (b * lo) <= c' + (b' * lo) && ((not (a_has_big p.k s)) || b <= b')

(* [check_node]'s edge: fails, kills B for every n, or goes on to the child
   with its line and bound. *)
let edge p s c b lo m =
  if a_is_create p.k s m && a_has_big p.k s then `Fail
  else
    let s' = a_stepA p.k p.hb p.tt s m in
    if a_too_many p.ott s' then `Fail
    else
      match winner s' with
      | Some _ -> `Fail
      | None ->
        let c1 = if a_is_pump_big p.k s m then c - b else c in
        let b1 = if a_is_create p.k s m then 0 else b in
        let c2 = c1 + (blife s' - blife s) in
        let b2 = if a_is_hit p.k s then b1 - 1 else b1 in
        let lo2 = if a_is_pump_big p.k s m then lo + 1 else if a_is_create p.k s m then 0 else lo in
        if c2 + (b2 * lo2) <= 0 && b2 <= 0 then `Dead else `Go (s', c2, b2, lo2)

(* The closure's choice of A's moves: at each A node the move whose turn
   starts cost least ([leaf], infinite where A fails), B's nodes adding up
   their moves' costs; [check_node]'s search otherwise. Returns the cost and
   A's picks, by node (state, line, bound, root). *)
let achoose p leaf s0 c0 b0 =
  let memo = H.create 1024 and pick = H.create 256 in
  let inf = infinity in
  let rec cost root s c b lo =
    match winner s with
    | Some _ -> inf
    | None ->
      if (not root) && is_turn_start s then leaf s c b lo
      else if a_huge_event p.hb s || a_big_event p.k s then inf
      else
        match H.find_opt memo (s, c, b, lo, root) with
        | Some r -> r
        | None ->
          let r =
            match to_move s with
            | PA ->
              let best = ref inf and bm = ref None in
              List.iter (fun m -> if !best > 0. then let x = next s c b lo m in if x < !best then (best := x; bm := Some m))
                (moves s);
              Option.iter (fun m -> H.replace pick (s, c, b, lo, root) m) !bm;
              !best
            | PB -> List.fold_left (fun acc m -> if acc = inf then inf else acc +. next s c b lo m) 0. (moves s)
          in
          H.replace memo (s, c, b, lo, root) r;
          r
  and next s c b lo m =
    match edge p s c b lo m with
    | `Fail -> inf
    | `Dead -> 0.
    | `Go (s', c2, b2, lo2) -> cost false s' c2 b2 lo2
  in
  let r = cost true s0 c0 b0 0 in
  (r, pick)

(* The turn starts A's picks reach from [s0], each given to [leaf] with the
   line and bound [check_node] asks there. *)
let awalk p pick leaf s0 c0 b0 =
  let seen = H.create 1024 in
  let rec go root s c b lo =
    match winner s with
    | Some _ -> ()
    | None ->
      if (not root) && is_turn_start s then leaf s c b lo
      else if not (a_huge_event p.hb s || a_big_event p.k s || H.mem seen (s, c, b, lo, root)) then begin
        H.replace seen (s, c, b, lo, root) ();
        let follow m = match edge p s c b lo m with `Go (s', c2, b2, lo2) -> go false s' c2 b2 lo2 | _ -> () in
        match to_move s with
        | PA -> Option.iter follow (H.find_opt pick (s, c, b, lo, root))
        | PB -> List.iter follow (moves s)
      end
  in
  go true s0 c0 b0 0

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

let dec = Certify.dec

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

(* PackedA.alookup over the entries [find] gives (packed key -> line):
   among the entries of [q]'s position at A's life up to [q]'s, the first,
   by A's life, with the greatest line (c, b) in lexicographic order; it
   answers if that entry is [q] with A's life lowered. Lines almost always
   grow with A's life ([Shrink.amono]), so this is almost always the line
   above all the others. *)
let packed_choice find q =
  let best = ref None in
  for l = 1 to q.sideA.life do
    let e = enc { q with sideA = { q.sideA with life = l } } in
    match find e with
    | Some ln -> (match !best with Some (_, _, b) when compare b ln >= 0 -> () | _ -> best := Some (l, e, ln))
    | None -> ()
  done;
  match !best with
  | Some (l, e, ln) when dec e = { q with sideA = { q.sideA with life = l } } -> Some ln
  | _ -> None

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
  (* A turn start the chosen moves reach is covered by the entry PackedA's
     lookup chooses among the collected entries, if its line is high
     enough; if not, the representative of its key is collected: the same
     position at the lowest A life whose line is at least as high (A safe
     with less life is safe with more: CheckerA.cert_ok), with its line.
     A's moves are chosen to collect as few as possible ([achoose]).
     TCB_DOM=0 collects the key itself. *)
  let dom = Sys.getenv_opt "TCB_DOM" <> Some "0" in
  let choose = true in
  let dom_rep s =
    match lk s with
    | None -> s
    | Some (c, b) ->
      let best = ref s in
      for l = s.sideA.life - 1 downto 1 do
        let s' = { s with sideA = { s.sideA with life = l } } in
        match lk s' with Some (c', b') when c' >= c && b' >= b -> best := s' | _ -> ()
      done;
      !best
  in
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
              (* the entries known to this worker: the table's, and its own new ones *)
              let seen = Hashtbl.create 1024 in
              let find e = match Hashtbl.find_opt seen e with Some ln -> Some ln | None -> Option.map vline (Tbl.find used e) in
              let add r ln =
                let e = key_of r in
                if not (Tbl.mem used e || Hashtbl.mem seen e) then begin
                  Hashtbl.replace seen e ln;
                  let k1, k2 = e in
                  Printf.fprintf oc "+ %d %d %d\n" k1 k2 (venc ln (l + 1))
                end
              in
              let bad = ref 0 in
              for j = a to b - 1 do
                let s = dec fr.(j) and c, b = vline (Option.get (Tbl.find used fr.(j))) in
                (* per entry: each key's representative and its line, and the
                   line the entries known so far give it *)
                let reps = S.create 64 and known = S.create 64 in
                let rep_of q = match S.find_opt reps q with
                  | Some x -> x
                  | None -> let r = if dom then dom_rep q else q in let x = (r, lk r) in S.replace reps q x; x in
                let known_of q = match S.find_opt known q with
                  | Some x -> x
                  | None -> let x = packed_choice find q in S.replace known q x; x in
                let leaf s' c' b' lo' =
                  let q = a_key p.hb p.tt s' in
                  match known_of q with
                  | Some ln when meets p s' c' b' lo' ln -> 0.
                  | _ -> (match rep_of q with _, Some ln when meets p s' c' b' lo' ln -> 1. | _ -> infinity)
                in
                let e = a_entry p.m s in
                let r, pick = if choose then achoose p leaf e c b else (0., H.create 1) in
                if r = infinity then begin
                  incr bad;
                  Printf.fprintf oc "- %d %d\n" (fst fr.(j)) (snd fr.(j))
                end
                else
                  awalk p pick (fun s' c' b' lo' ->
                      let q = a_key p.hb p.tt s' in
                      match known_of q with
                      | Some ln when meets p s' c' b' lo' ln -> ()
                      | _ ->
                        match rep_of q with
                        | r, Some ln when meets p s' c' b' lo' ln -> add r ln; S.reset known
                        | _ -> Printf.fprintf oc "! %d %d: a turn start not covered\n" (fst fr.(j)) (snd fr.(j)))
                    e c b
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
  let restricted s = packed_choice (fun e -> Option.map vline (Tbl.find used e)) s in
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

(* ** The certificate in Rocq (PackedA.v)

   [certify-a-export ENTRIES STARTER OUTDIR CHUNKS] reads the entries [run]
   wrote (sorted by packed key) and checks every one exactly as Rocq will,
   with the extracted [MemoA.check_m]: the lookup is a binary search over
   the sorted keys that answers only for a state that decodes back to
   itself, and the fuel is TCB_FUEL. Each entry also gets the life B has in
   its certificate state (PackedA's [life_of]): the check runs first with
   TCB_M, noting the least life B has in any state it steps to, and the
   entry keeps just enough life for B to stay alive through the turn (1 on
   B's own turns). With that life the search is the same, and cheaper in
   Rocq, whose naturals are unary; the check is run again with it, as Rocq
   will. With no failure, and the opening's line allowing 20 life, it
   writes the table to OUTDIR as PackedA reads it (each column cut into
   parts of 2^20 entries, one compressed file per part), CHUNKS files that
   each check a slice of the entries, and ADraw.v, which proves
   [a_first_a_safe] from them. The slices are balanced by the cost of their
   checks here (nodes searched and lookups made, plus one per entry).

   TCB_DRYRUN=1 checks without writing; TCB_RANGE=LO,HI checks only the
   entries in [LO, HI), to measure (it doesn't write). *)

(* A line, and the entry's life for B, packed as PackedA's line_of and
   life_of read them. *)
let pack_line (c, b) life =
  if c < -2048 || c >= 2048 || b < 0 || b >= 256 || life < 0 || life >= 128 then
    failwith "certify-a-export: a line out of range";
  (life lsl 20) lor ((c + 2048) lsl 8) lor b

let unpack_line v = (((v lsr 8) land 4095) - 2048, v land 255)

(* PackedA's parts: 2^part_bits entries each. *)
let part_bits = 20

let write_adraw ~outdir ~p ~k1s ~k2s ~ls ~bounds ~c0 ~b0 =
  let n = Array.length k1s in
  ignore (Sys.command ("mkdir -p " ^ Filename.quote outdir));
  let file name f = let oc = open_out (Filename.concat outdir name) in f oc; close_out oc in
  let gen = "(* Generated by main.exe; do not edit. *)\n" in
  let header = "From Stdlib Require Import Uint63 PArray List Arith ZArith.\nFrom TCB.Proofs Require Import Packed PackedA.\n" in
  let size = 1 lsl part_bits in
  let parts = (n + size - 1) / size in
  let cols = [ ("C1", k1s); ("C2", k2s); ("CV", ls) ] in
  let pieces = List.concat_map (fun (c, _) -> List.init parts (fun q -> Printf.sprintf "Data%s_%d" c q)) cols in
  List.iter (fun (c, a) ->
      for q = 0 to parts - 1 do
        let name = Printf.sprintf "Data%s_%d.v" c q in
        file name (fun oc ->
            output_string oc (gen ^ "From Stdlib Require Import Uint63 PArray.\n");
            Printf.fprintf oc "Definition %s_%d : array int := [| " c q;
            for j = q * size to min n ((q + 1) * size) - 1 do
              if j > q * size then output_string oc "; ";
              output_string oc (string_of_int a.(j))
            done;
            output_string oc " | 0 : int |]%uint63.\n");
        (* shipped compressed: integer literals compress about 70 times *)
        if Sys.command ("xz -9 -f " ^ Filename.quote (Filename.concat outdir name)) <> 0 then
          failwith "export: xz failed"
      done)
    cols;
  file "Data.v" (fun oc ->
      output_string oc (gen ^ header);
      Printf.fprintf oc
        "Definition K := %d.\nDefinition Hb := %d.\nDefinition ott := %d.\nDefinition tt := %d.\n\
         Definition fuel := %d.\n" p.k p.hb p.ott p.tt p.fuel;
      List.iter (Printf.fprintf oc "Require Import %s.\n") pieces;
      List.iter (fun (c, _) ->
          Printf.fprintf oc "Definition %s : array (array int) := [| %s | %s_0 |].\n" c
            (String.concat "; " (List.init parts (Printf.sprintf "%s_%d" c))) c)
        cols;
      Printf.fprintf oc "Definition N : int := %d%%uint63.\n" n);
  let rec pairs = function a :: (b :: _ as r) -> (a, b) :: pairs r | _ -> [] in
  let ps = pairs bounds in
  let ok = "aentry_ok K Hb ott tt fuel C1 C2 CV N" in
  List.iteri (fun c (lo, hi) ->
      file (Printf.sprintf "Chunk%03d.v" c) (fun oc ->
          output_string oc ("(* Generated; do not edit. *)\n" ^ header ^ "Require Import Data.\n");
          Printf.fprintf oc "Lemma chunk : exists f, range_ok (%s) f %d %d = true.\n" ok lo hi;
          Printf.fprintf oc "Proof. exists %d. vm_cast_no_check (eq_refl true). Qed.\n" (hi - lo)))
    ps;
  file "ADraw.v" (fun oc ->
      output_string oc ("(* Generated; do not edit. *)\n" ^ header);
      output_string oc "From TCB.Spec Require Import Model Claims.\nRequire Import Data.\nImport ListNotations.\n";
      List.iteri (fun c _ -> Printf.fprintf oc "Require Chunk%03d.\n" c) ps;
      Printf.fprintf oc "\nDefinition bounds : list int := [%s]%%uint63.\n"
        (String.concat "; " (List.map string_of_int bounds));
      Printf.fprintf oc "\nTheorem a_first_a_safe_proved : a_first_a_safe.\nProof.\n";
      Printf.fprintf oc "  apply (table_safe_a K Hb ott tt fuel C1 C2 CV N bounds (%d)%%Z (%d)%%Z).\n" c0 b0;
      Printf.fprintf oc "  - exact (%s).\n"
        (List.fold_right (fun c acc -> Printf.sprintf "conj Chunk%03d.chunk (%s)" c acc)
           (List.init (List.length ps) Fun.id) "I");
      output_string oc
        "  - reflexivity.\n  - vm_compute. reflexivity.\n  - apply Nat.ltb_lt. reflexivity.\n\
        \  - apply Nat.leb_le. reflexivity.\n  - vm_compute. reflexivity.\n  - apply Z.leb_le. reflexivity.\nQed.\n";
      output_string oc "\nPrint Assumptions a_first_a_safe_proved.\n");
  file "dune" (fun oc ->
      output_string oc
        "; Generated by solver/main.exe. Data*.v hold a table of positions; Chunk*.v check\n\
         ; every entry with the checker proved sound in proofs/core, so the table needs no trust.\n";
      List.iter (fun f ->
          Printf.fprintf oc
            "(rule\n (target %s.v)\n (deps %s.v.xz)\n (action (with-stdout-to %%{target} (run xz -dc %%{deps}))))\n\n" f f)
        pieces;
      output_string oc "(rocq.theory\n (name TCB.ADraw)\n (theories Stdlib TCB.Spec TCB.Proofs))\n");
  Printf.printf "export: wrote %d parts of %d columns and %d chunks to %s\n%!" parts (List.length cols) (List.length ps)
    outdir

let export entries starter ~outdir ~chunks p =
  let t0 = Unix.gettimeofday () in
  let fold f =
    let ic = open_in entries in
    (try while true do let l = input_line ic in if l <> "" && l.[0] <> '#' then f l done with End_of_file -> ());
    close_in ic
  in
  let n = ref 0 in
  fold (fun _ -> incr n);
  let n = !n in
  let es = Array.make n (0, 0, 0) in
  let j = ref 0 in
  fold (fun l ->
      Scanf.sscanf l "%d %d %d %d" (fun k1 k2 c b -> es.(!j) <- (k1, k2, pack_line (c, b) 0));
      incr j);
  (* PackedA's order: the key without A's life, then A's life *)
  Array.sort (fun (a1, a2, _) (b1, b2, _) -> Certify.packed_cmp (a1, a2) (b1, b2)) es;
  let k1s = Array.map (fun (k1, _, _) -> k1) es and k2s = Array.map (fun (_, k2, _) -> k2) es in
  let ls = Array.map (fun (_, _, l) -> l) es in
  for j = 1 to n - 1 do
    if Certify.packed_cmp (k1s.(j - 1), k2s.(j - 1)) (k1s.(j), k2s.(j)) >= 0 then failwith "certify-a-export: two entries share a key"
  done;
  Printf.printf "certify-a-export %s: %d entries; K=%d Hb=%d ott=%d tt=%d M=%d fuel=%d (%.1fs)\n%!" entries n p.k
    p.hb p.ott p.tt p.m p.fuel (Unix.gettimeofday () -. t0);
  (* PackedA.alookup: in the run of [s]'s position, the first entry with the
     greatest line among those at [s]'s A life or less *)
  let lk0 s =
    let k1, k2 = enc s in
    let lkey j = ls.(j) land 0xfffff in
    let rec go f j best =
      if f = 0 then best
      else if Certify.in_run k1s k2s j k1 k2 then
        if Certify.alife k1s.(j) <= Certify.alife k1 then go (f - 1) (j + 1) (if best >= n || lkey best < lkey j then j else best)
        else best
      else best
    in
    let j = go 64 (Certify.packed_start k1s k2s k1 k2) n in
    if j < n then
      let e = dec (k1s.(j), k2s.(j)) in
      if Certify.bump_a (Certify.nsub s.sideA.life e.sideA.life) e = s then Some (unpack_line ls.(j)) else None
    else None
  in
  let lookups = ref 0 and nodes = ref 0 and minlife = ref max_int in
  let lk s = incr lookups; lk0 s in
  (* MemoA's hash: any function is sound. [probe] also notes the least life
     B has in a state the node steps to (over every move: an upper bound on
     the life the search needs); [counting] counts the nodes searched. *)
  let hash s = Hashtbl.hash_param 100 400 s in
  let probe s =
    List.iter (fun m -> let l = (a_stepA p.k p.hb p.tt s m).sideB.life in if l < !minlife then minlife := l) (moves s);
    hash s
  in
  let counting s = incr nodes; hash s in
  let check_m h s life c b = fst (a_check_m p.k p.hb p.ott p.tt lk h p.fuel true (a_entry life s) c b 0 MLeaf) in
  let s0 = init starter in
  let c0, b0 = match lk0 (a_key p.hb p.tt s0) with Some l -> l | None -> failwith "certify-a-export: no opening entry" in
  Printf.printf "opening: line (%d, %d), B has %d life\n%!" c0 b0 s0.sideB.life;
  let wdir = Filename.dirname entries in
  let rlo, rhi =
    match Sys.getenv_opt "TCB_RANGE" with
    | Some r -> Scanf.sscanf r "%d,%d" (fun a b -> (max 0 a, min n b))
    | None -> (0, n)
  in
  let write = rlo = 0 && rhi = n && Sys.getenv_opt "TCB_DRYRUN" <> Some "1" in
  (* each entry's cost, written by the workers into a shared file *)
  let costf = Filename.concat wdir (Printf.sprintf "export-a-%d-cost" (Unix.getpid ())) in
  let cost =
    let fd = Unix.openfile costf [ Unix.O_RDWR; Unix.O_CREAT; Unix.O_TRUNC ] 0o644 in
    Unix.ftruncate fd (8 * max 1 n);
    let a = Bigarray.array1_of_genarray (Unix.map_file fd Bigarray.int Bigarray.c_layout true [| max 1 n |]) in
    Unix.close fd;
    a
  in
  (* each entry's packed line with its life, likewise *)
  let packf = costf ^ "-lines" in
  let packed =
    let fd = Unix.openfile packf [ Unix.O_RDWR; Unix.O_CREAT; Unix.O_TRUNC ] 0o644 in
    Unix.ftruncate fd (8 * max 1 n);
    let a = Bigarray.array1_of_genarray (Unix.map_file fd Bigarray.int Bigarray.c_layout true [| max 1 n |]) in
    Unix.close fd;
    a
  in
  let slices = if rhi - rlo < n then 1 else 32 in
  let bad = ref 0 in
  for sl = 0 to slices - 1 do
    let lo, hi = Par.chunk (rhi - rlo) slices sl in
    let lo = rlo + lo and hi = rlo + hi in
    let w = Par.workers (hi - lo) 1000 in
    let pid = Unix.getpid () in
    let name k = Filename.concat wdir (Printf.sprintf "export-a-%d-%d" pid k) in
    let r =
      Par.map ~dir:wdir w (fun k ->
          let a, b = Par.chunk (hi - lo) w k in
          let oc = open_out (name k) in
          let nb = ref 0 in
          for j = lo + a to lo + b - 1 do
            let c, b = unpack_line ls.(j) in
            let s = dec (k1s.(j), k2s.(j)) in
            minlife := max_int;
            let life =
              if check_m probe s p.m c b then if !minlife = max_int then 1 else max 1 (p.m - !minlife + 1) else p.m in
            lookups := 0;
            nodes := 0;
            if not (check_m counting s life c b) then begin
              incr nb;
              Printf.fprintf oc "%d %d %d %d\n" k1s.(j) k2s.(j) c b
            end;
            cost.{j} <- !nodes + !lookups;
            packed.{j} <- pack_line (c, b) life
          done;
          close_out oc;
          !nb)
    in
    for k = 0 to w - 1 do read_lines (name k) (fun line -> print_endline ("failed: " ^ line)) done;
    bad := !bad + Array.fold_left ( + ) 0 r;
    let nlk = ref 0 in
    for j = rlo to hi - 1 do nlk := !nlk + cost.{j} done;
    Printf.printf "  slice %d of %d: %d failed so far, cost %d so far (%.0fs)\n%!" (sl + 1) slices !bad !nlk
      (Unix.gettimeofday () -. t0)
  done;
  let total = ref 0 in
  for j = rlo to rhi - 1 do total := !total + cost.{j} done;
  let lifes = Array.make 129 0 in
  for j = rlo to rhi - 1 do let l = packed.{j} lsr 20 in lifes.(min l 128) <- lifes.(min l 128) + 1 done;
  Printf.printf "checked as in Rocq (MemoA.check_m, fuel %d, B's life cut from %d): %d of %d failed, cost %d (%.1fs)\n%!"
    p.fuel p.m !bad (rhi - rlo) !total (Unix.gettimeofday () -. t0);
  Printf.printf "B's life in the entries: %s\n%!"
    (String.concat " " (List.filter (( <> ) "") (Array.to_list (Array.mapi (fun l x -> if x > 0 then Printf.sprintf "%d:%d" l x else "") lifes))));
  for j = rlo to rhi - 1 do ls.(j) <- packed.{j} done;
  (* the slices for Rocq: [chunks] near-equal shares of the cost *)
  let bounds =
    let w = !total + n in
    let bs = ref [ 0 ] and acc = ref 0 and next = ref 1 in
    for j = 0 to n - 1 do
      acc := !acc + cost.{j} + 1;
      if !next < chunks && !acc * chunks >= !next * w then begin
        bs := (j + 1) :: !bs;
        while !next < chunks && !acc * chunks >= !next * w do incr next done
      end
    done;
    List.rev (if List.hd !bs = n then !bs else n :: !bs)
  in
  Sys.remove costf;
  Sys.remove packf;
  if !bad > 0 || c0 < 20 then failwith "certify-a-export: not writing a failing certificate";
  if write then write_adraw ~outdir ~p ~k1s ~k2s ~ls ~bounds ~c0 ~b0
