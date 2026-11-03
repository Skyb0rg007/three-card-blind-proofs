(* Experiments on the cost of Rocq's checks of the B-side tables
   (proofs/afirst, proofs/bfirst): [profile-b DIR] reads an exported
   Data.v.xz and runs, for every entry, a mirror of [MemoB.check_mb] /
   [MemoB.check_mw] (the same search and memo, in OCaml) that counts the
   internal nodes (forced ones too), memo hits, moves listed and steps
   taken; and a second search where B tries first a move that works
   (found by an exhaustive memoised search), which bounds what any order
   of B's moves could save. Writes one line per entry to TCB_FEAT and
   prints the totals. Measurements only. *)
open Model

module H = Certify.H

type counts = { mutable nodes : int; mutable forced : int; mutable hits : int; mutable moves : int;
                mutable steps : int; mutable leaves : int; mutable bdec : int; mutable bnz : int; mutable maxlen : int }

let zero () = { nodes = 0; forced = 0; hits = 0; moves = 0; steps = 0; leaves = 0; bdec = 0; bnz = 0; maxlen = 0 }

(* The mirror: [leaf s] is the turn-start test, [order s ms] B's order. *)
let search ~h ~ott ~win cnt leaf order e =
  let memo = H.create 256 in
  let rec go root s =
    match winner s with
    | Some PB -> true
    | Some PA -> false
    | None ->
      if (not root) && is_turn_start s then (cnt.leaves <- cnt.leaves + 1; leaf s)
      else if huge_event h s then false
      else begin
        cnt.nodes <- cnt.nodes + 1;
        let ms = moves s in
        cnt.moves <- cnt.moves + List.length ms;
        let g m = cnt.steps <- cnt.steps + 1; let s' = step s m in (not (too_many ott s')) && go false s' in
        let run () =
          match to_move s with
          | PB ->
            let o = order s ms in
            if List.length ms > 1 then begin
              cnt.bdec <- cnt.bdec + 1;
              if List.hd o <> List.hd ms then cnt.bnz <- cnt.bnz + 1;
              cnt.maxlen <- max cnt.maxlen (List.length ms)
            end;
            List.exists g o
          | PA -> if win && ms = [] then false else List.for_all g ms
        in
        match ms with
        | [ _ ] -> cnt.forced <- cnt.forced + 1; run ()
        | _ ->
          match H.find_opt memo s with
          | Some r -> cnt.hits <- cnt.hits + 1; r
          | None -> let r = run () in H.replace memo s r; r
      end
  in
  go true e

(* The mirror where B tries [pick s] first only on the opening path of the
   turn: from the entry through B's nodes and A's forced nodes, until A has
   a choice (what a hint stored with the entry could encode). *)
let search_path ~h ~ott ~win cnt leaf pick e =
  let memo = H.create 256 in
  let rec go root onpath s =
    match winner s with
    | Some PB -> true
    | Some PA -> false
    | None ->
      if (not root) && is_turn_start s then leaf s
      else if huge_event h s then false
      else begin
        cnt.nodes <- cnt.nodes + 1;
        let ms = moves s in
        let g on m = cnt.steps <- cnt.steps + 1; let s' = step s m in (not (too_many ott s')) && go false on s' in
        let run () =
          match to_move s with
          | PB ->
            if onpath then
              match pick s with
              | Some m -> g true m || List.exists (g false) (List.filter (fun m' -> m' <> m) ms)
              | None -> List.exists (g false) ms
            else List.exists (g false) ms
          | PA ->
            if win && ms = [] then false
            else (match ms with [ m ] -> g onpath m | _ -> List.for_all (g false) ms)
        in
        match ms with
        | [ _ ] -> run ()
        | _ ->
          match H.find_opt memo s with
          | Some r -> r
          | None -> let r = run () in H.replace memo s r; r
      end
  in
  go true true e

(* B's working moves: an exhaustive memoised search, B nodes recording
   their first working move. *)
let first_working ~h ~ott ~win leaf e =
  let memo = H.create 1024 and pick = H.create 256 in
  let rec go root s =
    match winner s with
    | Some PB -> true
    | Some PA -> false
    | None ->
      if (not root) && is_turn_start s then leaf s
      else if huge_event h s then false
      else
        match H.find_opt memo s with
        | Some r -> r
        | None ->
          let ms = moves s in
          let g m = let s' = step s m in (not (too_many ott s')) && go false s' in
          let r =
            match to_move s with
            | PB -> (match List.find_opt g ms with Some m -> H.replace pick s m; true | None -> false)
            | PA -> if win && ms = [] then false else List.for_all g ms
          in
          H.replace memo s r;
          r
  in
  ignore (go true e);
  ((fun s ms -> match H.find_opt pick s with Some m -> m :: List.filter (fun m' -> m' <> m) ms | None -> ms),
   fun s -> H.find_opt pick s)

(* TCB_BORDER=k1,k2,... (experiment): B tries its moves in reverse order at
   nodes of these kinds (attack, block, order, damage, window, upkeep). *)
let border =
  let ks = match Sys.getenv_opt "TCB_BORDER" with Some l -> String.split_on_char ',' l | None -> [] in
  fun s ms ->
    let k = match s.pend with
      | ChooseAttack -> "attack" | ChooseBlock -> "block" | ChooseOrder -> "order" | ChooseDamage -> "damage"
      | Window (Upkeep, _, _) -> "upkeep" | Window _ -> "window" | _ -> "" in
    if List.mem k ks then List.rev ms else ms

let profile_b dir =
  let num, arr, has = Certify.read_data dir in
  let h = num "H" and ott = num "ott" and tt = num "tt" in
  let k1s = arr "K1" and k2s = arr "K2" in
  let n = Array.length k1s in
  let win = has "Definition RV " in
  let vs = if win then arr "RV" else arr "V" in
  let nf = 17 in
  let path = Filename.concat dir (Printf.sprintf "prof-%d" (Unix.getpid ())) in
  let fd = Unix.openfile path [ Unix.O_RDWR; Unix.O_CREAT; Unix.O_TRUNC ] 0o644 in
  Unix.ftruncate fd (8 * nf * n);
  let fa = Bigarray.array1_of_genarray (Unix.map_file fd Bigarray.int Bigarray.c_layout true [| nf * n |]) in
  Unix.close fd;
  let w = Par.workers n 1000 in
  ignore
    (Par.map ~dir w (fun k ->
         let a, b = Par.chunk n w k in
         for j = a to b - 1 do
           let e, leaf =
             if win then begin
               let r = Certify.rank_of vs j in
               let lk = Certify.win_lookup k1s k2s vs (ref 0) and bl = Certify.win_below k1s k2s vs in
               let leaf s =
                 let q = key h tt s in
                 match bl q r with
                 | Some r' when r' < r -> (match lk q r' with Some v -> v <= s.sideB.life | None -> false)
                 | _ -> false
               in
               (entry (Certify.dec (k1s.(j), k2s.(j))) (vs.(j) land 63), leaf)
             end
             else begin
               let lk = Certify.safe_lookup k1s k2s vs (ref 0) in
               let leaf s = match lk (key h tt s) with Some v -> v <= s.sideB.life | None -> false in
               (entry (Certify.dec (k1s.(j), k2s.(j))) (vs.(j) land 63), leaf)
             end
           in
           let c1 = zero () and c2 = zero () in
           Certify.c_lk := 0; Certify.c_scan := 0; Certify.c_bs := 0;
           let ok1 = search ~h ~ott ~win c1 leaf border e in
           let lk1 = !Certify.c_lk and sc1 = !Certify.c_scan and bs1 = !Certify.c_bs in
           let order, pick = first_working ~h ~ott ~win leaf e in
           let ok2 = search ~h ~ott ~win c2 leaf order e in
           let c3 = zero () in
           let ok3 = search_path ~h ~ott ~win c3 leaf pick e in
           if not (ok1 && ok2 && ok3) then failwith (Printf.sprintf "profile-b: entry %d fails" j);
           let put i x = fa.{(nf * j) + i} <- x in
           put 0 c1.nodes; put 1 c1.forced; put 2 c1.hits; put 3 c1.moves; put 4 c1.steps; put 5 c1.leaves;
           put 6 lk1; put 7 sc1; put 8 bs1; put 9 c2.nodes; put 10 c2.steps; put 11 c2.moves;
           put 12 c3.nodes; put 13 c3.steps; put 14 c2.bdec; put 15 c2.bnz; put 16 c2.maxlen
         done;
         0));
  let tot = Array.make nf 0 in
  let out = Sys.getenv_opt "TCB_FEAT" in
  let oc = Option.map open_out out in
  for j = 0 to n - 1 do
    for i = 0 to nf - 1 do tot.(i) <- tot.(i) + fa.{(nf * j) + i} done;
    Option.iter (fun oc ->
        output_string oc (string_of_int j);
        for i = 0 to nf - 1 do Printf.fprintf oc " %d" fa.{(nf * j) + i} done;
        output_char oc '\n') oc
  done;
  Option.iter close_out oc;
  Sys.remove path;
  let names = [| "nodes"; "forced"; "hits"; "moves"; "steps"; "leaves"; "starts"; "scan"; "bs"; "nodes(oracle order)";
                 "steps(oracle order)"; "moves(oracle order)"; "nodes(path hint)"; "steps(path hint)";
                 "B choices (oracle)"; "not first (oracle)"; "most moves (sum)" |] in
  Printf.printf "profile-b %s: %d entries\n" dir n;
  Array.iteri (fun i x -> Printf.printf "  %-20s %12d  (%.1f per entry)\n" names.(i) x (float x /. float n)) tot

(* [profile-order DIR]: at B's nodes with several moves (every 10th entry,
   searched as Rocq does), which move works first: counts by the kind of
   node, the index of the first working move and the number of moves, and
   the nodes searched below the failing moves tried before it. *)
let pend_kind s =
  match s.pend with
  | Window (st, p, _) ->
    let st = match st with Upkeep -> "upkeep" | DrawStep -> "draw" | Main1 -> "main1" | BeginCombat -> "begincombat"
                         | DeclAtk -> "declatk" | DeclBlk -> "declblk" | DamageStep -> "damage" | EndCombat -> "endcombat"
                         | Main2 -> "main2" | EndStep -> "end" in
    Printf.sprintf "window-%s-%s%s" st (if p = PA then "A" else "B") (if s.active = PA then "(A's turn)" else "(B's turn)")
  | ChooseAttack -> "attack" | ChooseBlock -> "block" | ChooseOrder -> "order" | ChooseDamage -> "damage"
  | ChooseShuffle _ -> "shuffle" | Over _ -> "over"

let profile_order dir =
  let num, arr, has = Certify.read_data dir in
  let h = num "H" and ott = num "ott" and tt = num "tt" in
  let k1s = arr "K1" and k2s = arr "K2" in
  let n = Array.length k1s in
  let win = has "Definition RV " in
  let vs = if win then arr "RV" else arr "V" in
  let stats = Hashtbl.create 64 in
  let bump k w = let c, x = Option.value (Hashtbl.find_opt stats k) ~default:(0, 0) in Hashtbl.replace stats k (c + 1, x + w) in
  let j = ref 0 in
  while !j < n do
    let jj = !j in
    let leaf =
      if win then begin
        let r = Certify.rank_of vs jj in
        let lk = Certify.win_lookup k1s k2s vs (ref 0) and bl = Certify.win_below k1s k2s vs in
        fun s ->
          let q = key h tt s in
          match bl q r with
          | Some r' when r' < r -> (match lk q r' with Some v -> v <= s.sideB.life | None -> false)
          | _ -> false
      end
      else begin
        let lk = Certify.safe_lookup k1s k2s vs (ref 0) in
        fun s -> match lk (key h tt s) with Some v -> v <= s.sideB.life | None -> false
      end
    in
    let e = entry (Certify.dec (k1s.(jj), k2s.(jj))) (vs.(jj) land 63) in
    (* the Rocq-order search, recording at each B node the nodes spent on failing moves *)
    let memo = H.create 256 in
    let nodes = ref 0 in
    let rec go root s =
      match winner s with
      | Some PB -> true
      | Some PA -> false
      | None ->
        if (not root) && is_turn_start s then leaf s
        else if huge_event h s then false
        else begin
          incr nodes;
          let ms = moves s in
          let g m = let s' = step s m in (not (too_many ott s')) && go false s' in
          let run () =
            match to_move s with
            | PB ->
              let rec first i = function
                | [] -> None
                | m :: r -> let n0 = !nodes in if g m then Some (i, n0) else first (i + 1) r
              in
              let n0 = !nodes in
              (match first 0 ms with
               | Some (i, n1) ->
                 if List.length ms > 1 then
                   bump (Printf.sprintf "%-34s %2d of %2d" (pend_kind s) i (List.length ms)) (n1 - n0);
                 true
               | None ->
                 if List.length ms > 1 then bump (Printf.sprintf "%-34s none of %2d" (pend_kind s) (List.length ms)) (!nodes - n0);
                 false)
            | PA -> if win && ms = [] then false else List.for_all g ms
          in
          match ms with
          | [ _ ] -> run ()
          | _ ->
            match H.find_opt memo s with
            | Some r -> r
            | None -> let r = run () in H.replace memo s r; r
        end
    in
    ignore (go true e);
    j := !j + 10
  done;
  let l = Hashtbl.fold (fun k (c, x) acc -> (x, c, k) :: acc) stats [] |> List.sort compare |> List.rev in
  Printf.printf "profile-order %s: B nodes with several moves, every 10th entry; wasted nodes, count, kind/index\n" dir;
  List.iteri (fun i (x, c, k) -> if i < 40 then Printf.printf "  %9d %8d  %s\n" x c k) l
