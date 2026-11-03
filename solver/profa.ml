(* [profile-a ENTRIES] (experiment): as [Prof.profile_b] for the A-safe
   table (certify-a's entries, [MemoA.check_m]'s search): nodes and leaves
   as Rocq searches, and with A trying first a move that works. Lines are
   read as certify-a writes them (k1 k2 c b); B's life in each entry is
   TCB_M. Measurements only. *)
open Model

module HA = Hashtbl.Make (struct
    type t = state * int * int * int
    let equal = ( = )
    let hash = Hashtbl.hash_param 100 400
  end)

let profile_a entries (p : Certifya.params) =
  let es = ref [] in
  let ic = open_in entries in
  (try
     while true do
       let l = input_line ic in
       if l <> "" && l.[0] <> '#' then Scanf.sscanf l "%d %d %d %d" (fun k1 k2 c b -> es := (k1, k2, c, b) :: !es)
     done
   with End_of_file -> ());
  close_in ic;
  let es = Array.of_list !es in
  Array.sort (fun (a1, a2, _, _) (b1, b2, _, _) -> Certify.packed_cmp (a1, a2) (b1, b2)) es;
  let n = Array.length es in
  let k1s = Array.map (fun (k1, _, _, _) -> k1) es and k2s = Array.map (fun (_, k2, _, _) -> k2) es in
  let lns = Array.map (fun (_, _, c, b) -> (c, b)) es in
  (* PackedA.alookup *)
  let lk s = Option.map (fun j -> lns.(j)) (Certify.a_index k1s k2s s) in
  let leaf s c b lo =
    match lk (a_key p.hb p.tt s) with
    | Some (c', b') -> c + (b * lo) <= c' + (b' * lo) && ((not (a_has_big p.k s)) || b <= b')
    | None -> false
  in
  let edge s c b lo m g =
    match Certifya.edge p s c b lo m with
    | `Fail -> false
    | `Dead -> true
    | `Go (s', c2, b2, lo2) -> g s' c2 b2 lo2
  in
  (* the search as MemoA.check_m; [order] gives A's order at a node *)
  let search (cnt : Prof.counts) order s0 c0 b0 =
    let memo = HA.create 256 in
    let rec go root s c b lo =
      match winner s with
      | Some _ -> false
      | None ->
        if (not root) && is_turn_start s then (cnt.leaves <- cnt.leaves + 1; leaf s c b lo)
        else if a_huge_event p.hb s || a_big_event p.k s then false
        else begin
          cnt.nodes <- cnt.nodes + 1;
          match HA.find_opt memo (s, c, b, lo) with
          | Some r -> cnt.hits <- cnt.hits + 1; r
          | None ->
            let g m = cnt.steps <- cnt.steps + 1; edge s c b lo m (go false) in
            let ms = moves s in
            if List.length ms = 1 then cnt.forced <- cnt.forced + 1;
            let r =
              match to_move s with
              | PA ->
                let ao = a_order s ms in
                let o = order s c b lo ao in
                if List.length ms > 1 then begin
                  cnt.bdec <- cnt.bdec + 1;
                  if List.hd o <> List.hd ao then cnt.bnz <- cnt.bnz + 1
                end;
                List.exists g o
              | PB -> List.for_all g ms
            in
            HA.replace memo (s, c, b, lo) r;
            r
        end
    in
    go true s0 c0 b0 0
  in
  let first_working s0 c0 b0 =
    let memo = HA.create 1024 and pick = HA.create 256 in
    let rec go root s c b lo =
      match winner s with
      | Some _ -> false
      | None ->
        if (not root) && is_turn_start s then leaf s c b lo
        else if a_huge_event p.hb s || a_big_event p.k s then false
        else
          match HA.find_opt memo (s, c, b, lo) with
          | Some r -> r
          | None ->
            let g m = edge s c b lo m (go false) in
            let ms = moves s in
            let r =
              match to_move s with
              | PA -> (match List.find_opt g (a_order s ms) with Some m -> HA.replace pick (s, c, b, lo) m; true | None -> false)
              | PB -> List.for_all g ms
            in
            HA.replace memo (s, c, b, lo) r;
            r
    in
    ignore (go true s0 c0 b0 0);
    fun s c b lo ms ->
      match HA.find_opt pick (s, c, b, lo) with Some m -> m :: List.filter (fun m' -> m' <> m) ms | None -> ms
  in
  let nf = 10 in
  let dir = Filename.dirname entries in
  let path = Filename.concat dir (Printf.sprintf "profa-%d" (Unix.getpid ())) in
  let fd = Unix.openfile path [ Unix.O_RDWR; Unix.O_CREAT; Unix.O_TRUNC ] 0o644 in
  Unix.ftruncate fd (8 * nf * n);
  let fa = Bigarray.array1_of_genarray (Unix.map_file fd Bigarray.int Bigarray.c_layout true [| nf * n |]) in
  Unix.close fd;
  let w = Par.workers n 1000 in
  ignore
    (Par.map ~dir w (fun k ->
         let a, b = Par.chunk n w k in
         for j = a to b - 1 do
           let s = a_entry p.m (Certify.dec (k1s.(j), k2s.(j))) and c, bb = lns.(j) in
           let c1 = Prof.zero () and c2 = Prof.zero () in
           let ok1 = search c1 (fun _ _ _ _ ms -> ms) s c bb in
           let order = first_working s c bb in
           let ok2 = search c2 order s c bb in
           if not (ok1 && ok2) then failwith (Printf.sprintf "profile-a: entry %d fails" j);
           let put i x = fa.{(nf * j) + i} <- x in
           put 0 c1.nodes; put 1 c1.forced; put 2 c1.hits; put 3 c1.steps; put 4 c1.leaves;
           put 5 c2.nodes; put 6 c2.steps; put 7 c2.leaves; put 8 c2.bdec; put 9 c2.bnz
         done;
         0));
  let tot = Array.make nf 0 in
  for j = 0 to n - 1 do for i = 0 to nf - 1 do tot.(i) <- tot.(i) + fa.{(nf * j) + i} done done;
  Sys.remove path;
  let names = [| "nodes"; "forced"; "hits"; "steps"; "leaves"; "nodes(oracle order)"; "steps(oracle order)";
                 "leaves(oracle order)"; "A choices (oracle)"; "not first (oracle)" |] in
  Printf.printf "profile-a %s: %d entries\n" entries n;
  Array.iteri (fun i x -> Printf.printf "  %-20s %12d  (%.1f per entry)\n" names.(i) x (float x /. float n)) tot
