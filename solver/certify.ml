(* Driver for the extracted certificate checker (proofs/core/Checker.v).

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

(* ** Export to Rocq (Packed.v)

   Turn starts packed as [Packed.enc] does, and [Packed.dec]. *)

let put off w x = (x land ((1 lsl w) - 1)) lsl off
let b2i b = if b then 1 else 0

let enc_walker (wk : walker) = put 0 5 wk.counters lor put 5 1 (b2i wk.wtapped) lor put 6 1 (b2i wk.sick)

let enc_side sd =
  let slot l n f = match List.nth_opt l n with Some x -> f x | None -> 0 in
  let card c = match c with CWalker -> 0 | CElixir -> 1 in
  List.fold_left ( lor ) 0
    [ put 0 5 sd.life; put 5 1 (b2i sd.city); put 6 3 sd.pool; put 9 2 sd.hand_w; put 11 1 (b2i sd.hand_e);
      put 12 1 (b2i sd.elixir_bf); put 13 5 sd.thop_u; put 18 5 sd.thop_t; put 23 2 sd.gy_w;
      put 25 2 (List.length sd.bf); put 27 7 (slot sd.bf 0 enc_walker); put 34 7 (slot sd.bf 1 enc_walker);
      put 41 7 (slot sd.bf 2 enc_walker); put 48 2 (List.length sd.library);
      put 50 1 (slot sd.library 0 card); put 51 1 (slot sd.library 1 card); put 52 1 (slot sd.library 2 card) ]

let enc s =
  (enc_side s.sideA lor put 53 1 (b2i (s.active = PB)) lor put 54 1 (b2i s.first_turn), enc_side s.sideB)

(* Packed.dec: the turn start a packed key stands for. *)
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

(* ** The checks Rocq runs on each entry, and their costs

   Packed.v checks an entry with [MemoB.check_mb] (safety) or
   [MemoB.check_mw] (wins), searches memoised on a hash of states. Their
   result does not depend on the hash (the memo compares states in full),
   so here it only counts the nodes searched: an entry's cost, by which the
   entries are cut into chunks of near-equal work. *)

let memo_hash nodes s = incr nodes; Hashtbl.hash_param 100 400 s

(* [ok j] runs entry [j]'s check, counting its nodes and lookups in the
   given counter; [ok] is run on every entry in [TCB_JOBS] workers. Returns
   each entry's cost and the indices that failed. *)
let costs ~dir n (ok : int ref -> int -> bool) =
  ignore (Sys.command ("mkdir -p " ^ Filename.quote dir));
  let path = Filename.concat dir (Printf.sprintf "costs-%d" (Unix.getpid ())) in
  let fd = Unix.openfile path [ Unix.O_RDWR; Unix.O_CREAT; Unix.O_TRUNC ] 0o644 in
  Unix.ftruncate fd (8 * max 1 n);
  let cost = Bigarray.array1_of_genarray (Unix.map_file fd Bigarray.int Bigarray.c_layout true [| max 1 n |]) in
  Unix.close fd;
  let w = Par.workers n 1000 in
  ignore
    (Par.map ~dir w (fun k ->
         let a, b = Par.chunk n w k in
         let c = ref 0 in
         for j = a to b - 1 do
           c := 0;
           cost.{j} <- (if ok c j then !c else -1)
         done;
         0));
  let res = Array.init n (fun j -> cost.{j}) in
  Sys.remove path;
  let bad = List.filter (fun j -> res.(j) < 0) (List.init n Fun.id) in
  (res, bad)

(* Chunk bounds: [chunks] near-equal shares of the total cost (each entry
   counting one more than its cost). *)
let balance cost chunks =
  let n = Array.length cost in
  let total = Array.fold_left (fun acc c -> acc + c + 1) 0 cost in
  let bs = ref [ 0 ] and acc = ref 0 and next = ref 1 in
  for j = 0 to n - 1 do
    acc := !acc + cost.(j) + 1;
    if !next < chunks && !acc * chunks >= !next * total then begin
      bs := (j + 1) :: !bs;
      while !next < chunks && !acc * chunks >= !next * total do incr next done
    end
  done;
  List.rev (if List.hd !bs = n then !bs else n :: !bs)

(* Write a packed table as Rocq files in [outdir]: Data.v (the arrays), one
   file per chunk proving [range_ok ok] on its index range by computation,
   and [final].v proving [claim] from them with [apply]. *)
let rocq_header = "From Stdlib Require Import Uint63 PArray List Arith.\nFrom TCB.Proofs Require Import Packed.\n"

let write_data ~outdir ~n ~defs ~arrays =
  ignore (Sys.command ("mkdir -p " ^ Filename.quote outdir));
  let file name f = let oc = open_out (Filename.concat outdir name) in f oc; close_out oc in
  let header = rocq_header in
  file "Data.v" (fun oc ->
      output_string oc ("(* Generated by main.exe; do not edit. *)\n" ^ header ^ defs);
      List.iter (fun (name, get) ->
          Printf.fprintf oc "Definition %s : array int := [| " name;
          for j = 0 to n - 1 do
            if j > 0 then output_string oc "; ";
            output_string oc (string_of_int (get j))
          done;
          output_string oc " | 0 : int |]%uint63.\n")
        arrays);
  (* shipped compressed: 50 MB of integer literals become about 1 MB *)
  if Sys.command ("xz -9 -f " ^ Filename.quote (Filename.concat outdir "Data.v")) <> 0 then
    failwith "export: xz failed"

(* The chunk files over [bounds], each proving [range_ok ok] on its range by
   computation, and [final].v proving [claim] from them with [apply]. *)
let write_chunks ~outdir ~bounds ~ok ~final ~claim ~apply =
  let file name f = let oc = open_out (Filename.concat outdir name) in f oc; close_out oc in
  let header = rocq_header in
  (* old chunk files go: there may be fewer now *)
  Array.iter (fun f -> if String.length f > 5 && String.sub f 0 5 = "Chunk" then Sys.remove (Filename.concat outdir f))
    (Sys.readdir outdir);
  let rec pairs = function a :: (b :: _ as r) -> (a, b) :: pairs r | _ -> [] in
  let ps = pairs bounds in
  List.iteri (fun c (lo, hi) ->
      file (Printf.sprintf "Chunk%03d.v" c) (fun oc ->
          output_string oc ("(* Generated; do not edit. *)\n" ^ header ^ "Require Import Data.\n");
          Printf.fprintf oc "Lemma chunk : exists f, range_ok (%s) f %d %d = true.\n" ok lo hi;
          Printf.fprintf oc "Proof. exists %d. vm_cast_no_check (eq_refl true). Qed.\n" (hi - lo)))
    ps;
  file (final ^ ".v") (fun oc ->
      output_string oc ("(* Generated; do not edit. *)\n" ^ header);
      output_string oc "From TCB.Spec Require Import Model Claims.\nRequire Import Data.\nImport ListNotations.\n";
      List.iteri (fun c _ -> Printf.fprintf oc "Require Chunk%03d.\n" c) ps;
      Printf.fprintf oc "\nDefinition bounds : list int := [%s]%%uint63.\n"
        (String.concat "; " (List.map string_of_int bounds));
      Printf.fprintf oc "\nTheorem %s_proved : %s.\nProof.\n  apply (%s).\n" claim claim apply;
      Printf.fprintf oc "  - exact (%s).\n"
        (List.fold_right (fun c acc -> Printf.sprintf "conj Chunk%03d.chunk (%s)" c acc)
           (List.init (List.length ps) Fun.id) "I");
      output_string oc "  - reflexivity.\n  - vm_compute. reflexivity.\n  - vm_compute. reflexivity.\n";
      output_string oc "  - apply Nat.leb_le. reflexivity.\nQed.\n";
      Printf.fprintf oc "\nPrint Assumptions %s_proved.\n" claim);
  file "dune" (fun oc ->
      Printf.fprintf oc
        "; Generated by solver/main.exe. Data.v is a table of positions; Chunk*.v check\n\
         ; every entry with the checker proved sound in proofs/core, so the table needs no trust.\n\
         (rule\n (target Data.v)\n (deps Data.v.xz)\n (action (with-stdout-to %%{target} (run xz -dc %%{deps}))))\n\n\
         (rocq.theory\n (name TCB.%s)\n (theories Stdlib TCB.Spec TCB.Proofs))\n" final);
  Printf.printf "export: wrote %d chunks to %s\n%!" (List.length ps) outdir

let write_rocq ~outdir ~n ~defs ~arrays ~bounds ~ok ~final ~claim ~apply =
  write_data ~outdir ~n ~defs ~arrays;
  write_chunks ~outdir ~bounds ~ok ~final ~claim ~apply

(* ** Packed.v's lookups, emulated

   The arrays are sorted by key without A's life ([hi k1], then [k2]), then
   by A's life: a position's records at every A life form a run. A lookup
   finds the run by binary search and chooses a record of it at A's life or
   more (B tables: B safe or winning against more A life also is against
   less); the record is accepted if it decodes to the looked-up state with
   A's life raised. These follow Packed.v step for step, fuel included. *)

let hi k1 = k1 lsr 5
let alife k1 = k1 land 31

(* The packed order of keys. *)
let packed_cmp (a1, a2) (b1, b2) = compare (hi a1, a2, alife a1) (hi b1, b2, alife b1)

(* Packed.start *)
let packed_start k1s k2s k1 k2 =
  let h = hi k1 in
  let rec go f a b =
    if f = 0 || a >= b then a
    else
      let m = (a + b) / 2 in
      if hi k1s.(m) < h || (hi k1s.(m) = h && k2s.(m) < k2) then go (f - 1) (m + 1) b else go (f - 1) a m
  in
  go 32 0 (Array.length k1s)

(* Packed.in_run *)
let in_run k1s k2s j k1 k2 = j < Array.length k1s && hi k1s.(j) = hi k1 && k2s.(j) = k2

(* Mono.bump PA, and the model's truncated subtraction *)
let bump_a d s = { s with sideA = { s.sideA with life = s.sideA.life + d } }
let nsub a b = max 0 (a - b)

(* Accept record [j] for [s]: it is [s] with A's life raised. *)
let accept k1s k2s j s =
  let e = dec (k1s.(j), k2s.(j)) in
  e = bump_a (nsub e.sideA.life s.sideA.life) s

(* Packed.wbest: the record of the run needing the least life among those
   at [k1]'s A life or more with a rank passing [ok]. *)
let win_best k1s k2s rv ok k1 k2 =
  let n = Array.length k1s in
  let rec go f j best =
    if f = 0 then best
    else if in_run k1s k2s j k1 k2 then
      go (f - 1) (j + 1)
        (if alife k1 <= alife k1s.(j) && ok (rv.(j) lsr 6) && (best >= n || rv.(j) land 63 < rv.(best) land 63)
         then j else best)
    else best
  in
  go 256 (packed_start k1s k2s k1 k2) n

let rank_of rv j = (rv.(j) lsr 6) land 0xffff

(* Packed.lookup and Packed.below *)
let win_lookup k1s k2s rv lookups s r =
  incr lookups;
  let k1, k2 = enc s in
  let j = win_best k1s k2s rv (fun x -> x = r) k1 k2 in
  if j < Array.length k1s && rank_of rv j = r && accept k1s k2s j s then Some (rv.(j) land 63) else None

let win_below k1s k2s rv s r =
  let k1, k2 = enc s in
  let j = win_best k1s k2s rv (fun x -> x < r) k1 k2 in
  if j < Array.length k1s then Some (rank_of rv j) else None

(* Packed.slookup: the entry of the run needing the least life among those
   at [s]'s A life or more. *)
let safe_lookup k1s k2s vs lookups s =
  incr lookups;
  let k1, k2 = enc s in
  let n = Array.length k1s in
  let rec go f j best =
    if f = 0 then best
    else if in_run k1s k2s j k1 k2 then
      go (f - 1) (j + 1) (if alife k1 <= alife k1s.(j) && (best >= n || vs.(j) < vs.(best)) then j else best)
    else best
  in
  let j = go 64 (packed_start k1s k2s k1 k2) n in
  if j < n && accept k1s k2s j s then Some (vs.(j) land 63) else None

(* Record [j] of a win table, entry [j] of a safety table, checked as Rocq
   does (Packed.record_ok, Packed.entry_ok); the counter counts nodes and
   lookups. *)
let record_check ~h ~ott ~tt ~fuel k1s k2s rv c j =
  fst (check_mw h ott tt (memo_hash c) (win_lookup k1s k2s rv c) (win_below k1s k2s rv) (rank_of rv j) fuel true
         (entry (dec (k1s.(j), k2s.(j))) (rv.(j) land 63)) MLeaf)

let entry_check ~h ~ott ~tt ~fuel k1s k2s vs c j =
  fst (check_mb h ott tt (memo_hash c) (safe_lookup k1s k2s vs c) fuel true
         (entry (dec (k1s.(j), k2s.(j))) (vs.(j) land 63)) MLeaf)

(* ** Choosing B's moves, and the closure of the opening

   Only the entries the check of the opening consults are exported. The
   closure starts from the opening's entry and follows one turn from each
   entry it collects: B's move at each of its nodes is chosen to add as
   little as possible ([choose_turn]: B's nodes take the cheapest working
   move, A's add up their moves' costs), and every turn start the chosen
   moves reach must be covered by a collected entry. A turn start covered
   by one already collected (the same position at A's life or more, with
   little enough life needed) costs nothing; otherwise it adds the
   representative the caller gives, and costs its weight. Nothing here is
   trusted: the export checks every collected entry again as Rocq will. *)

(* B's move at each node of the turn from [e], minimising the summed cost of
   the turn starts reached ([leaf], infinite when B fails there). With
   [win], A must have a move (WinCert.check_win). Returns the cost and B's
   picks. *)
let choose_turn ~h ~ott ~win leaf e =
  let memo = H.create 1024 and pick = H.create 256 in
  let rec cost root s =
    match winner s with
    | Some PB -> 0.
    | Some PA -> infinity
    | None ->
      if (not root) && is_turn_start s then leaf s
      else if huge_event h s then infinity
      else
        match H.find_opt memo s with
        | Some c -> c
        | None ->
          let child m = let s' = step s m in if too_many ott s' then infinity else cost false s' in
          let c =
            match to_move s with
            | PA ->
              let ms = moves s in
              if win && ms = [] then infinity
              else List.fold_left (fun acc m -> if acc = infinity then infinity else acc +. child m) 0. ms
            | PB ->
              let best = ref infinity and bm = ref None in
              List.iter (fun m -> if !best > 0. then let c = child m in if c < !best then (best := c; bm := Some m))
                (moves s);
              (match !bm with Some m -> H.replace pick s m | None -> ());
              !best
          in
          H.replace memo s c;
          c
  in
  let c = cost true e in
  (c, pick)

(* The turn starts B's picks reach from [e], each given to [leaf]. *)
let walk_turn ~h ~ott pick leaf e =
  let seen = H.create 1024 in
  let rec go root s =
    match winner s with
    | Some _ -> ()
    | None ->
      if (not root) && is_turn_start s then leaf s
      else if (not (huge_event h s)) && not (H.mem seen s) then begin
        H.replace seen s ();
        let next m = let s' = step s m in if not (too_many ott s') then go false s' in
        match to_move s with
        | PB -> Option.iter next (H.find_opt pick s)
        | PA -> List.iter next (moves s)
      end
  in
  go true e

let env_int k d = match Sys.getenv_opt k with Some v -> int_of_string v | None -> d

(* The weight of adding the key [e] in round [r] of [rounds]: 1 in round 0;
   later a key the previous round collected weighs 1 / (1 + its uses
   there), any other 4 (Shrink's rounds). *)
let round_weight prev e =
  match prev with
  | None -> 1.
  | Some (used, uses) ->
    if Hashtbl.mem used e then 1. /. (1. +. float (Option.value (Hashtbl.find_opt uses e) ~default:0)) else 4.

(* ** Safety certificates in Rocq (Packed.v, SafeTable)

   The closure as above, a turn start [s] being covered by an entry of its
   position at A's life or more needing at most [s]'s B life. A new entry
   is the representative of [key s]: the same position at the highest A
   life up to which the table's value stays at most [key s]'s (Shrink's
   DOMK=2), with its own value. TCB_ROUNDS=R repeats the closure R more
   times, weighing keys by their use in the previous one. Then every entry
   is checked as Rocq will (Packed.entry_ok over the sorted arrays, every B
   move tried, the given fuel). *)

let safe_rep t lk k =
  match lk k with
  | None -> None
  | Some v0 ->
    let nl = t.sv.Fix.nl in
    let rec go k v =
      let k' = { k with sideA = { k.sideA with life = k.sideA.life + 1 } } in
      if k'.sideA.life > nl then (k, v) else match lk k' with Some v' when v' <= v0 -> go k' v' | _ -> (k, v)
    in
    Some (go k v0)

let safe_closure t lk starter prev =
  let t0 = Unix.gettimeofday () in
  let rep = safe_rep t lk in
  let used = Hashtbl.create 1_000_000 and runs = Hashtbl.create 1_000_000 and uses = Hashtbl.create 1_000_000 in
  let queue = Queue.create () in
  let add (s, v) =
    let ((k1, k2) as e) = enc s in
    match Hashtbl.find_opt used e with
    | Some (s', _) -> if s' <> s then failwith "export-safe: two states share a packed key"
    | None ->
      Hashtbl.replace used e (s, v);
      let r = (hi k1, k2) in
      Hashtbl.replace runs r ((alife k1, v, e) :: Option.value (Hashtbl.find_opt runs r) ~default:[]);
      Queue.push (s, v) queue
  in
  (* the collected entry covering [q] (key form) with B on [x] life *)
  let covered q x =
    let k1, k2 = enc q in
    match Hashtbl.find_opt runs (hi k1, k2) with
    | None -> None
    | Some l -> List.find_opt (fun (a, v, _) -> a >= alife k1 && v <= x) l |> Option.map (fun (_, _, e) -> e)
  in
  let use e = Hashtbl.replace uses e (1 + Option.value (Hashtbl.find_opt uses e) ~default:0) in
  let s0 = init starter in
  (match rep (key t.h t.tt s0) with Some r -> add r | None -> failwith "export-safe: the opening has no entry");
  let bad = ref 0 and n = ref 0 in
  while not (Queue.is_empty queue) do
    let s, v = Queue.pop queue in
    let e = entry s v in
    let leaf s' =
      let q = key t.h t.tt s' and x = s'.sideB.life in
      match covered q x with
      | Some _ -> 0.
      | None -> (match rep q with Some (k, v') when v' <= x -> round_weight prev (enc k) | _ -> infinity)
    in
    let c, pick = choose_turn ~h:t.h ~ott:t.ott ~win:false leaf e in
    if c = infinity then incr bad
    else
      walk_turn ~h:t.h ~ott:t.ott pick (fun s' ->
          let q = key t.h t.tt s' and x = s'.sideB.life in
          match covered q x with
          | Some e -> use e
          | None ->
            match rep q with
            | Some ((k, v') as r) when v' <= x -> add r; use (enc k)
            | _ -> incr bad)
        e;
    incr n;
    if !n mod 100_000 = 0 then
      Printf.printf "  closure: %d checked, %d collected (%.0fs)\n%!" !n (Hashtbl.length used) (Unix.gettimeofday () -. t0)
  done;
  (used, uses, !bad)

let certify_safe_export dir starter ~outdir ~chunks ~fuel:f =
  let t = open_table dir in
  let lk = lookup t in
  let t0 = Unix.gettimeofday () in
  let rounds = env_int "TCB_ROUNDS" 0 in
  let res = ref (safe_closure t lk starter None) in
  let report r (used, _, bad) =
    Printf.printf "closure round %d: %d entries, %d failed (%.1fs)\n%!" r (Hashtbl.length used) bad
      (Unix.gettimeofday () -. t0)
  in
  report 0 !res;
  for r = 1 to rounds do
    let used, uses, _ = !res in
    res := safe_closure t lk starter (Some (used, uses));
    report r !res
  done;
  let used, _, bad1 = !res in
  let n = Hashtbl.length used in
  Hashtbl.iter (fun k (s, _) -> if dec k <> s then failwith "export-safe: dec (enc s) <> s") used;
  let recs =
    Hashtbl.fold (fun (k1, k2) (_, v) acc -> (k1, k2, v) :: acc) used []
    |> List.sort (fun (a1, a2, _) (b1, b2, _) -> packed_cmp (a1, a2) (b1, b2))
    |> Array.of_list
  in
  let k1s = Array.map (fun (k1, _, _) -> k1) recs and k2s = Array.map (fun (_, k2, _) -> k2) recs in
  let vs = Array.map (fun (_, _, v) -> if v >= 64 then failwith "export-safe: value too big" else v) recs in
  let cost, bad = costs ~dir:outdir n (entry_check ~h:t.h ~ott:t.ott ~tt:t.tt ~fuel:f k1s k2s vs) in
  let v0 = match safe_lookup k1s k2s vs (ref 0) (key t.h t.tt (init starter)) with Some v -> v | None -> 99 in
  Printf.printf "pass 2 (as in Rocq, fuel %d): %d of %d failed, cost %d (%.1fs); opening needs %d life\n%!" f
    (List.length bad) n (Array.fold_left ( + ) 0 cost) (Unix.gettimeofday () -. t0) v0;
  if bad1 > 0 || bad <> [] || v0 > 20 then failwith "export-safe: not writing a failing certificate";
  write_rocq ~outdir ~n
    ~defs:(Printf.sprintf "Definition H := %d.\nDefinition ott := %d.\nDefinition tt := %d.\nDefinition fuel := %d.\n"
             t.h t.ott t.tt f)
    ~arrays:[ ("K1", fun j -> k1s.(j)); ("K2", fun j -> k2s.(j)); ("V", fun j -> vs.(j)) ]
    ~bounds:(balance cost chunks) ~ok:"entry_ok H ott tt fuel K1 K2 V" ~final:"AFirst" ~claim:"a_first_b_safe"
    ~apply:(Printf.sprintf "table_safe H ott tt fuel K1 K2 V %s bounds %d" (if starter = PA then "PA" else "PB") v0)

(* ** Win certificates in Rocq (Packed.v, WinTable)

   The closure as above with ranks: an entry is a record (a turn start,
   its rank, the life B needs), and a turn start reached from a record of
   rank [r] must be covered by a collected record of its position at A's
   life or more, of rank below [r], needing at most the B life there. A new
   record is the table's latest record below [r] of the same position at
   the highest A life that has one needing little enough life. Only the
   Walker orders the closure reaches are kept. Ranks are renumbered densely
   (only their order matters). *)

let certify_win_export dir starter ~outdir ~chunks ~fuel:f =
  let w = open_win dir in
  let t = w.wt in
  let t0 = Unix.gettimeofday () in
  let rounds = env_int "TCB_ROUNDS" 0 in
  let nl = t.sv.Fix.nl in
  (* the candidates for the key [q] below rank [r]: at each A life from the
     highest down to [q]'s, the latest record below [r] *)
  let candidates q r =
    List.filter_map (fun l ->
        let ql = { q with sideA = { q.sideA with life = l } } in
        match index t ql with
        | None -> None
        | Some i ->
          match below_rec w i r with
          | Some rk -> Option.map (fun v -> (ql, rk, v)) (record w i rk)
          | None -> None)
      (List.init (max 0 (nl - q.sideA.life + 1)) (fun d -> nl - d))
  in
  let s0 = init starter in
  let k0 = key t.h t.tt s0 in
  let i0 = match index t k0 with Some i -> i | None -> failwith "export-win: the opening has no position" in
  let r0 =
    let a, b = recs w i0 in
    let rec go p = if p >= b then failwith "export-win: no opening record on 20 life"
      else if rval w p <= s0.sideB.life then rank w i0 p else go (p + 1) in
    go a
  in
  let v0 = Option.get (record w i0 r0) in
  let closure prev =
    let used = Hashtbl.create 1_000_000 and runs = Hashtbl.create 1_000_000 and uses = Hashtbl.create 1_000_000 in
    let queue = Queue.create () in
    let add (s, r, v) =
      let ((k1, k2) as e) = enc s in
      if not (Hashtbl.mem used (e, r)) then begin
        Hashtbl.replace used (e, r) (s, v);
        let key = (hi k1, k2) in
        Hashtbl.replace runs key ((alife k1, r, v, e) :: Option.value (Hashtbl.find_opt runs key) ~default:[]);
        Queue.push (s, r, v) queue
      end
    in
    let covered q r x =
      let k1, k2 = enc q in
      match Hashtbl.find_opt runs (hi k1, k2) with
      | None -> None
      | Some l ->
        List.find_opt (fun (a, r', v, _) -> a >= alife k1 && r' < r && v <= x) l
        |> Option.map (fun (_, r', _, e) -> (e, r'))
    in
    let use e = Hashtbl.replace uses e (1 + Option.value (Hashtbl.find_opt uses e) ~default:0) in
    add (k0, r0, v0);
    let bad = ref 0 and n = ref 0 in
    while not (Queue.is_empty queue) do
      let s, r, v = Queue.pop queue in
      let e = entry s v in
      (* the record to add for the key [q] with B on [x] life *)
      let memo = H.create 64 in
      let rep q _ x =
        let cs = match H.find_opt memo q with Some cs -> cs | None -> let cs = candidates q r in H.replace memo q cs; cs in
        List.find_opt (fun (_, _, v) -> v <= x) cs
      in
      let leaf s' =
        let q = key t.h t.tt s' and x = s'.sideB.life in
        match covered q r x with
        | Some _ -> 0.
        | None -> (match rep q r x with Some (ql, rk, _) -> round_weight prev (enc ql, rk) | None -> infinity)
      in
      let c, pick = choose_turn ~h:t.h ~ott:t.ott ~win:true leaf e in
      if c = infinity then incr bad
      else
        walk_turn ~h:t.h ~ott:t.ott pick (fun s' ->
            let q = key t.h t.tt s' and x = s'.sideB.life in
            match covered q r x with
            | Some er -> use er
            | None ->
              match rep q r x with
              | Some ((ql, rk, _) as rc) -> add rc; use (enc ql, rk)
              | None -> incr bad)
          e;
      incr n;
      if !n mod 100_000 = 0 then
        Printf.printf "  closure: %d checked, %d collected (%.0fs)\n%!" !n (Hashtbl.length used)
          (Unix.gettimeofday () -. t0)
    done;
    (used, uses, !bad)
  in
  let res = ref (closure None) in
  let report r (used, _, bad) =
    Printf.printf "closure round %d: %d records, %d failed (%.1fs)\n%!" r (Hashtbl.length used) bad
      (Unix.gettimeofday () -. t0)
  in
  report 0 !res;
  for r = 1 to rounds do
    let used, uses, _ = !res in
    res := closure (Some (used, uses));
    report r !res
  done;
  let used, _, bad1 = !res in
  Hashtbl.iter (fun (k, _) (s, _) -> if dec k <> s then failwith "export-win: dec (enc s) <> s") used;
  let ranks = Hashtbl.fold (fun (_, r) _ acc -> r :: acc) used [] |> List.sort_uniq compare |> Array.of_list in
  if Array.length ranks >= 1 lsl 16 then failwith "export-win: too many ranks";
  let dense r =
    let rec go a b = if a >= b then a else let m = (a + b) / 2 in if ranks.(m) < r then go (m + 1) b else go a m in
    go 0 (Array.length ranks)
  in
  let recs =
    Hashtbl.fold (fun ((k1, k2), r) (_, v) acc ->
        if v >= 64 then failwith "export-win: value too big";
        (k1, k2, dense r, v) :: acc) used []
    |> List.sort (fun (a1, a2, ra, _) (b1, b2, rb, _) -> compare (packed_cmp (a1, a2) (b1, b2), ra) (0, rb))
    |> Array.of_list
  in
  let n = Array.length recs in
  Printf.printf "export: %d records, %d ranks\n%!" n (Array.length ranks);
  let k1s = Array.map (fun (k1, _, _, _) -> k1) recs and k2s = Array.map (fun (_, k2, _, _) -> k2) recs in
  let rv = Array.map (fun (_, _, r, v) -> (r lsl 6) lor v) recs in
  let rk0 = dense r0 in
  (* the closure's tables go before the workers fork: a child's GC would
     touch, and so copy, every page of a large heap *)
  Hashtbl.reset used;
  res := (Hashtbl.create 1, Hashtbl.create 1, 0);
  Gc.compact ();
  let cost, bad = costs ~dir:outdir n (record_check ~h:t.h ~ott:t.ott ~tt:t.tt ~fuel:f k1s k2s rv) in
  let lv0 = win_lookup k1s k2s rv (ref 0) k0 rk0 in
  Printf.printf "pass 2 (as in Rocq, fuel %d): %d of %d records fail, cost %d; opening: rank %d, value %s (%.1fs)\n%!"
    f (List.length bad) n (Array.fold_left ( + ) 0 cost) rk0
    (match lv0 with Some v -> string_of_int v | None -> "none") (Unix.gettimeofday () -. t0);
  (match lv0 with Some v when bad1 = 0 && bad = [] && v <= 20 -> () | _ ->
     failwith "export-win: not writing a failing certificate");
  write_rocq ~outdir ~n
    ~defs:(Printf.sprintf "Definition H := %d.\nDefinition ott := %d.\nDefinition tt := %d.\nDefinition fuel := %d.\n"
             t.h t.ott t.tt f)
    ~arrays:[ ("K1", fun j -> k1s.(j)); ("K2", fun j -> k2s.(j)); ("RV", fun j -> rv.(j)) ]
    ~bounds:(balance cost chunks) ~ok:"record_ok H ott tt fuel K1 K2 RV" ~final:"BFirst"
    ~claim:"b_first_b_wins" ~apply:(Printf.sprintf "table_wins H ott tt fuel K1 K2 RV bounds %d %d" rk0 (Option.get lv0))

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
  (match restricted k0 r0 with
   | Some v ->
     Printf.printf "opening record: rank %d, B needs %d life (has %d)\n%!" r0 v s0.sideB.life;
     if bad = 0 && v <= 20 then print_endline "certified: B wins from the opening"
     else print_endline "not certified"
   | None -> print_endline "not certified: the opening record is missing")

(* How long a ranked B win can last: the opening's record on B's starting
   life, and for each A-life level the highest round any record reaches. A
   line from the opening stays within a level for at most that many turn
   starts, so the sum bounds the line's length. *)
let win_depth dir starter =
  let w = open_win dir in
  let t = w.wt in
  let s0 = init starter in
  let i0 = Option.get (index t (key t.h t.tt s0)) in
  let a, b = recs w i0 in
  for p = a to b - 1 do
    let r = rank w i0 p in
    Printf.printf "opening record: B life %d at level %d, round %d\n" (rval w p) (r / level + 1) (r mod level)
  done;
  let nb = t.sv.Fix.nb and nl = t.sv.Fix.nl in
  let total = ref 0 in
  for l = 0 to nl - 1 do
    let m = ref 0 in
    for i = l * nb to ((l + 1) * nb) - 1 do
      let a, b = recs w i in
      for p = a to b - 1 do
        if finite t (rval w p) then m := max !m (Int32.to_int w.hrec.{2 * p})
      done
    done;
    total := !total + !m;
    Printf.printf "A life %d: rounds up to %d\n%!" (l + 1) !m
  done;
  Printf.printf "sum: %d turn starts\n" !total

(* A line of B's ranked win from the opening with B on [life]: B takes the
   move reaching the earliest next record, A the one delaying it most.
   TCB_LAX=1 drops the huge rule, for tables solved with TCB_LAX=dmg,die;
   then A's Walkers keep their real sizes, so the line stops where B's lax
   win relied on a huge A Walker hitting for only [h]. TCB_AGROW=1 makes A
   maximise its Walkers' total counters at the next turn start instead, and
   TCB_ANEED=1 maximise the life the next record needs. *)
let win_line dir starter life nturns =
  let w = open_win dir in
  let t = w.wt in
  let lax = Sys.getenv_opt "TCB_LAX" <> None in
  let grow = Sys.getenv_opt "TCB_AGROW" = Some "1" in
  let need = Sys.getenv_opt "TCB_ANEED" = Some "1" in
  let size s v =
    if grow then list_sum (List.map (fun wk -> wk.counters) s.sideA.bf) else if need then v else 0 in
  (* A gets only the filter's moves if the table was solved that way *)
  let a_moves = if List.assoc_opt "fullopp" (Fix.read_meta dir) = Some "1" then moves else Reduce.moves in
  let moves s = if to_move s = PA then a_moves s else moves s in
  let lk k r = match index t k with Some i -> record w i r | None -> None in
  let below k r = match index t k with Some i -> below_rec w i r | None -> None in
  let s0 = init starter in
  let s0 = { s0 with sideB = { s0.sideB with life } } in
  let i0 = Option.get (index t (key t.h t.tt s0)) in
  let a, b = recs w i0 in
  let rec first p = if p >= b then None else if rval w p <= life then Some (rank w i0 p) else first (p + 1) in
  match first a with
  | None -> Printf.printf "B has no win from the opening on %d life\n" life
  | Some r0 ->
    let memo = H.create 1024 in
    (* the rank of the next turn start's record under best play, -1 if B
       wins this turn, None if B's win fails *)
    let rec far r root s =
      match winner s with
      | Some PB -> Some (-1, 0)
      | Some PA -> None
      | None ->
        if (not root) && is_turn_start s then
          let k = key t.h t.tt s in
          match below k r with
          | Some r' ->
            (match lk k r' with Some v when v <= s.sideB.life -> Some (r', size s v) | _ -> None)
          | None -> None
        else if (not lax) && huge_event t.h s then None
        else
          match H.find_opt memo s with
          | Some x -> x
          | None ->
            let rs = List.map (fun m -> (m, next r s m)) (moves s) in
            let x = pick (to_move s) rs |> Option.map snd in
            H.replace memo s x;
            x
    and next r s m =
      let s' = step s m in
      if too_many t.ott s' then None else far r false s'
    and pick p rs =
      let ok = List.filter_map (fun (m, x) -> Option.map (fun v -> (m, v)) x) rs in
      match p with
      | PB -> List.fold_left (fun acc (m, v) -> match acc with Some (_, v') when fst v' <= fst v -> acc | _ -> Some (m, v)) None ok
      | PA ->
        let sw (r, z) = (z, r) in
        if List.length ok < List.length rs then None
        else List.fold_left (fun acc (m, v) -> match acc with Some (_, v') when sw v' >= sw v -> acc | _ -> Some (m, v)) None ok
    in
    let rec turn n r s =
      if n < nturns then begin
        Printf.printf "--- turn %d (record level %d, round %d) ---\n%s\n" n (r / level + 1) (r mod level) (Show.state s);
        H.reset memo;
        let rec play s root =
          if (not root) && (winner s <> None || is_turn_start s) then Some s
          else
            let rs = List.map (fun m -> (m, next r s m)) (moves s) in
            match pick (to_move s) rs with
            | None -> None
            | Some (m, _) ->
              if m <> Pass then Printf.printf "  %s: %s\n" (Show.player (to_move s)) (Show.move m);
              play (step s m) false
        in
        match play s true with
        | None -> Printf.printf "B's win breaks here (real sizes)\n"
        | Some s' ->
          match winner s' with
          | Some p -> Printf.printf "%s wins\n%s\n" (Show.player p) (Show.state s')
          | None ->
            let k = key t.h t.tt s' in
            turn (n + 1) (Option.get (below k r)) s'
      end
    in
    turn 0 r0 s0

(* The records B's ranked win from the opening (B on [life]) reaches, with
   A given every move the table gave it: how many, the most life one needs,
   and A's largest Walker in them. TCB_LAX=1 as for [win_line]. *)
let win_reach dir starter life =
  let w = open_win dir in
  let t = w.wt in
  let lax = Sys.getenv_opt "TCB_LAX" <> None in
  let a_moves = if List.assoc_opt "fullopp" (Fix.read_meta dir) = Some "1" then moves else Reduce.moves in
  let moves s = if to_move s = PA then a_moves s else moves s in
  let lk k r = match index t k with Some i -> record w i r | None -> None in
  let below k r = match index t k with Some i -> below_rec w i r | None -> None in
  let s0 = init starter in
  let s0 = { s0 with sideB = { s0.sideB with life } } in
  let i0 = Option.get (index t (key t.h t.tt s0)) in
  let a, b = recs w i0 in
  let rec first p = if p >= b then failwith "win-reach: no opening record" else if rval w p <= life then rank w i0 p else first (p + 1) in
  (* each record maps to the record it was first reached from *)
  let used = Hashtbl.create 100_000 and queue = Queue.create () in
  let from = ref (-1, -1) in
  let add i r = if not (Hashtbl.mem used (i, r)) then (Hashtbl.replace used (i, r) !from; Queue.push (i, r) queue) in
  add i0 (first a);
  let memo = H.create 1024 in
  let rec ok r root s =
    match winner s with
    | Some PB -> true
    | Some PA -> false
    | None ->
      if (not root) && is_turn_start s then
        let k = key t.h t.tt s in
        match below k r with
        | Some r' -> (match lk k r' with Some v -> v <= s.sideB.life | None -> false)
        | None -> false
      else if (not lax) && huge_event t.h s then false
      else
        match H.find_opt memo s with
        | Some x -> x
        | None ->
          let x = match to_move s with
            | PB -> List.exists (next r s) (moves s)
            | PA -> List.for_all (next r s) (moves s) in
          H.replace memo s x;
          x
  and next r s m = let s' = step s m in (not (too_many t.ott s')) && ok r false s' in
  (* follow B's first working move and every A move to the next turn starts *)
  let rec collect r root s =
    if winner s <> None then ()
    else if (not root) && is_turn_start s then begin
      let k = key t.h t.tt s in
      match below k r, index t k with
      | Some r', Some i -> add i r'
      | _ -> failwith "win-reach: a turn start without a record"
    end else
      match to_move s with
      | PB -> collect r false (step s (List.find (next r s) (moves s)))
      | PA -> List.iter (fun m -> collect r false (step s m)) (moves s)
  in
  let maxv = ref 0 and maxa = ref 0 and maxb = ref 0 and bad = ref 0 and n = ref 0 and top = ref (i0, 0) in
  while not (Queue.is_empty queue) do
    let i, r = Queue.pop queue in
    from := (i, r);
    match record w i r with
    | None -> incr bad
    | Some v ->
      if v > !maxv then (maxv := v; top := (i, r));
      List.iter (fun s ->
          let s = { s with sideB = { s.sideB with life = v } } in
          List.iter (fun wk -> maxa := max !maxa wk.counters) s.sideA.bf;
          List.iter (fun wk -> maxb := max !maxb wk.counters) s.sideB.bf;
          H.reset memo;
          if ok r true s then collect r true s else incr bad)
        (record_states w i);
      incr n;
      if !n mod 100_000 = 0 then Printf.printf "  %d records, %d queued\n%!" !n (Queue.length queue)
  done;
  Printf.printf "%d records reached: B needs at most %d life; A's largest Walker %d (huge %d), B's %d; %d failed\n"
    (Hashtbl.length used) !maxv !maxa t.h !maxb !bad;
  (* the chain of records from the opening to the first one needing the most *)
  let rec chain ir acc = if fst ir < 0 then acc else chain (Hashtbl.find used ir) (ir :: acc) in
  print_endline "chain to the first record needing the most life:";
  List.iteri (fun n (i, r) ->
      let s = Fix.of_key (Fix.key_at t.sv i) in
      let v = Option.value (record w i r) ~default:(-1) in
      Printf.printf "%3d level %d round %d, B needs %d | %s\n" n (r / level + 1) (r mod level) v
        (String.concat " | " (List.tl (String.split_on_char '\n' (Show.state s)))))
    (chain !top [])

(* Cost probe for checking win records inside Rocq: on the first [n] records
   reached from the opening, count search nodes with the memoised oracle and
   with an unmemoised one (as a pure Rocq hint would be). *)
let win_cost dir starter n =
  let w = open_win dir in
  let t = w.wt in
  let below s r = match index t s with Some i -> below_rec w i r | None -> None in
  let full s r = match index t s with Some i -> record w i r | None -> None in
  let s0 = init starter in
  let k0 = key t.h t.tt s0 in
  let i0 = Option.get (index t k0) in
  let a, b = recs w i0 in
  let rec go p = if rval w p <= s0.sideB.life then rank w i0 p else go (p + 1) in
  let r0 = go a in
  ignore b;
  let used = Hashtbl.create 1000 and queue = Queue.create () in
  let add i r = if not (Hashtbl.mem used (i, r)) && Hashtbl.length used < n then (Hashtbl.replace used (i, r) (); Queue.push (i, r) queue) in
  add i0 r0;
  let logging s r = match full s r with
    | Some v -> (match index t s with Some i -> add i r | None -> ()); Some v
    | None -> None in
  let nodes = ref 0 in
  (* unmemoised oracle *)
  let rec ok r root s =
    incr nodes;
    match winner s with
    | Some PB -> true
    | Some PA -> false
    | None ->
      if (not root) && is_turn_start s then
        let k = key t.h t.tt s in
        (match below k r with
         | Some r' -> r' < r && (match full k r' with Some v -> v <= s.sideB.life | None -> false)
         | None -> false)
      else if huge_event t.h s then false
      else
        let next m = let s' = step s m in (not (too_many t.ott s')) && ok r false s' in
        match to_move s with
        | PB -> List.exists next (moves s)
        | PA -> moves s <> [] && List.for_all next (moves s)
  in
  let tm = ref 0. and tn = ref 0. and mn = ref 0 and nn = ref 0 and cnt = ref 0 in
  while not (Queue.is_empty queue) do
    let i, r = Queue.pop queue in
    List.iter (fun s ->
        match logging s r with
        | None -> ()
        | Some v ->
          incr cnt;
          let memo, okm = win_oracle w full below in
          let t1 = Unix.gettimeofday () in
          let hint s m = let s' = step s m in (not (too_many t.ott s')) && okm r false s' in
          assert (check_win t.h t.ott t.tt logging below hint r fuel true (entry s v));
          tm := !tm +. (Unix.gettimeofday () -. t1);
          mn := !mn + H.length memo;
          nodes := 0;
          let t2 = Unix.gettimeofday () in
          assert (ok r true (entry s v));
          tn := !tn +. (Unix.gettimeofday () -. t2);
          nn := !nn + !nodes)
      (record_states w i)
  done;
  Printf.printf "%d states: memoised %.1f ms/state (%.0f memo entries/state); unmemoised %.1f ms/state (%.0f nodes/state)\n"
    !cnt (1000. *. !tm /. float !cnt) (float !mn /. float !cnt) (1000. *. !tn /. float !cnt) (float !nn /. float !cnt)

(* ** Re-cutting an exported table into chunks

   Reads an exported directory's Data.v.xz (afirst or bfirst), checks every
   entry as Rocq will and rewrites the chunk files and the final file with
   [chunks] chunks of near-equal cost. The table itself is unchanged. *)

let read_data dir =
  let ic = Unix.open_process_in ("xz -dc " ^ Filename.quote (Filename.concat dir "Data.v.xz")) in
  let buf = Buffer.create (64 lsl 20) in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  ignore (Unix.close_process_in ic);
  let s = Buffer.contents buf in
  let find key =
    let n = String.length s and k = String.length key in
    let rec go i = if i + k > n then failwith ("rechunk: no " ^ key) else if String.sub s i k = key then i + k else go (i + 1) in
    go 0
  in
  let num name =
    let i = find ("Definition " ^ name ^ " := ") in
    int_of_string (String.sub s i (String.index_from s i '.' - i))
  in
  let arr name =
    let i = find ("Definition " ^ name ^ " : array int := [| ") in
    let j = String.index_from s i '|' in
    (* the literals between i and j, separated by "; " *)
    let xs = ref [] and x = ref 0 and digits = ref false in
    for p = i to j do
      match s.[p] with
      | '0' .. '9' as d -> x := (!x * 10) + Char.code d - 48; digits := true
      | _ -> if !digits then (xs := !x :: !xs; x := 0; digits := false)
    done;
    Array.of_list (List.rev !xs)
  in
  (num, arr, fun key -> try ignore (find key); true with Failure _ -> false)

let rechunk dir chunks =
  let t0 = Unix.gettimeofday () in
  let num, arr, has = read_data dir in
  let h = num "H" and ott = num "ott" and tt = num "tt" and fuel = num "fuel" in
  let k1s = arr "K1" and k2s = arr "K2" in
  let n = Array.length k1s in
  let win = has "Definition RV " in
  Printf.printf "rechunk %s: %d %s, H=%d ott=%d tt=%d fuel=%d (%.1fs)\n%!" dir n
    (if win then "records" else "entries") h ott tt fuel (Unix.gettimeofday () -. t0);
  let dummy = ref 0 in
  if win then begin
    let rv = arr "RV" in
    let cost, bad = costs ~dir n (record_check ~h ~ott ~tt ~fuel k1s k2s rv) in
    (* the opening's lowest-rank record on at most 20 life *)
    let s0 = init PB in
    let k0 = key h tt s0 in
    let e0 = enc k0 in
    let r0 = ref max_int in
    Array.iteri (fun j k1 -> if (k1, k2s.(j)) = e0 && rv.(j) land 63 <= s0.sideB.life then r0 := min !r0 (rank_of rv j)) k1s;
    let v0 = match win_lookup k1s k2s rv dummy k0 !r0 with Some v -> v | None -> failwith "rechunk: no opening record" in
    Printf.printf "%d of %d records fail, cost %d; opening: rank %d, value %d (%.1fs)\n%!" (List.length bad) n
      (Array.fold_left ( + ) 0 cost) !r0 v0 (Unix.gettimeofday () -. t0);
    if bad <> [] || v0 > 20 then failwith "rechunk: not writing a failing certificate";
    write_chunks ~outdir:dir ~bounds:(balance cost chunks) ~ok:"record_ok H ott tt fuel K1 K2 RV" ~final:"BFirst"
      ~claim:"b_first_b_wins" ~apply:(Printf.sprintf "table_wins H ott tt fuel K1 K2 RV bounds %d %d" !r0 v0)
  end else begin
    let vs = arr "V" in
    let cost, bad = costs ~dir n (entry_check ~h ~ott ~tt ~fuel k1s k2s vs) in
    let v0 = match safe_lookup k1s k2s vs dummy (key h tt (init PA)) with
      | Some v -> v | None -> failwith "rechunk: no opening entry" in
    Printf.printf "%d of %d entries fail, cost %d; opening needs %d life (%.1fs)\n%!" (List.length bad) n
      (Array.fold_left ( + ) 0 cost) v0 (Unix.gettimeofday () -. t0);
    if bad <> [] || v0 > 20 then failwith "rechunk: not writing a failing certificate";
    write_chunks ~outdir:dir ~bounds:(balance cost chunks) ~ok:"entry_ok H ott tt fuel K1 K2 V" ~final:"AFirst"
      ~claim:"a_first_b_safe" ~apply:(Printf.sprintf "table_safe H ott tt fuel K1 K2 V PA bounds %d" v0)
  end
