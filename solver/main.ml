open Model
open Rules

let pl = function "A" -> PA | _ -> PB

let print_line line =
  let prev = ref None in
  List.iter (fun (s, m) ->
      if (match !prev with None -> true | Some p -> p <> s.active) then
        Printf.printf "--- turn start ---\n%s\n" (Show.state s);
      prev := Some s.active;
      if m <> Pass then Printf.printf "  %s: %s\n" (Show.player (to_move s)) (Show.move m))
    line

let env_int v d = try int_of_string (Sys.getenv v) with Not_found -> d

let a_policy kind k =
  let k2 = try int_of_string (Sys.getenv "TCB_LOOK") with Not_found -> 4 in
  match kind with
  | "all" -> Policy.a_all ~k
  | "over" -> Policy.a_over ~k
  | "small" -> Policy.a_chipsmall ~x:k
  | "grind" -> Policy.a_grind ~k
  | "deter" -> Policy.a_deter ~g:(env_int "TCB_G" 3) ~x:k
  | "deterL" -> Policy.with_lookahead ~d:k2 (Policy.a_deter ~g:(env_int "TCB_G" 3) ~x:k)
  | "deterM" -> Policy.with_lookahead ~mine:Reduce.a_macro ~d:k2 (Policy.a_deter ~g:(env_int "TCB_G" 3) ~x:k)
  | _ -> Policy.a_chip ~chip:k

let usage () =
  prerr_endline
    "usage: main bfs|rbfs A|B TURNS\n\
    \       main win STARTER WHO MAXTURNS\n\
    \       main beat STARTER grow|elixir MAXTURNS\n\
    \       main check STARTER chip|all|over K TURNS"

let () =
  match Sys.argv with
  | [| _; "bfs"; p; n |] -> Explore.bfs (pl p) (int_of_string n)
  | [| _; "rbfs"; p; n |] ->
    Explore.moves_fn := Reduce.moves;
    Explore.bfs (pl p) (int_of_string n)
  | [| _; "win"; starter; who; dmax |] ->
    let tbl, wins = Search.make ~mine:Reduce.moves ~theirs:Reduce.moves (pl who) in
    for d = 1 to int_of_string dmax do
      let t0 = Sys.time () in
      let r = wins (init (pl starter)) d in
      Printf.printf "%s first: %s forces a win within %d turns: %b  (%d nodes, %d table, %.1fs)\n%!"
        starter who d r !Search.nodes (Search.H.length tbl) (Sys.time () -. t0)
    done
  | [| _; "cwin"; starter; who; dmin; dmax |] ->
    let tbl, wins = Csearch.make ~mine:Reduce.moves ~theirs:Reduce.moves (pl who) in
    for d = int_of_string dmin to int_of_string dmax do
      let t0 = Sys.time () in
      let r = wins (init (pl starter)) d in
      Printf.printf "%s first: %s forces a win within %d turns: %b  (%d nodes, %d table, %.1fs)\n%!"
        starter who d r !Csearch.nodes (Hashtbl.length tbl) (Sys.time () -. t0)
    done
  | [| _; "mwin"; starter; dmin; dmax |] ->
    let tbl, wins = Csearch.make ~mine:Reduce.a_macro ~theirs:Reduce.moves PA in
    for d = int_of_string dmin to int_of_string dmax do
      let t0 = Sys.time () in
      let r = wins (init (pl starter)) d in
      Printf.printf "%s first: A (macro moves) forces a win within %d turns: %b  (%d nodes, %d table, %.1fs)\n%!"
        starter d r !Csearch.nodes (Hashtbl.length tbl) (Sys.time () -. t0)
    done
  | [| _; "bmwin"; starter; dmin; dmax |] ->
    let tbl, wins = Csearch.make ~mine:Reduce.moves ~theirs:Reduce.b_macro PA in
    for d = int_of_string dmin to int_of_string dmax do
      let t0 = Sys.time () in
      let r = wins (init (pl starter)) d in
      Printf.printf "%s first: A forces a win vs B macro within %d turns: %b  (%d nodes, %d table, %.1fs)\n%!"
        starter d r !Csearch.nodes (Hashtbl.length tbl) (Sys.time () -. t0)
    done
  | [| _; "beat"; starter; pol; dmax |] ->
    let policy = match pol with
      | "grow" -> Policy.turtle ~elixir:(fun _ -> false)
      | "smart" -> Policy.b_smart
      | "mirror" -> Policy.b_mirror
      | "fortress" -> Policy.b_fortress
      | _ -> Policy.turtle ~elixir:(fun _ -> true)
    in
    (* iterative deepening, so the line found is a shortest one *)
    let rec go d =
      if d > int_of_string dmax then Printf.printf "no win within %s turns\n" dmax
      else match Policy.beat PA policy (init (pl starter)) d with
        | Some line -> Printf.printf "A beats %s within %d turns\n" pol d; print_line line
        | None -> Printf.printf "  (no win within %d)\n%!" d; go (d + 2)
    in
    go 20
  | [| _; "check"; starter; kind; k; d |] ->
    let t0 = Sys.time () in
    (match Policy.check PA (a_policy kind (int_of_string k)) (init (pl starter)) (int_of_string d) with
     | None -> Printf.printf "A's %s %s policy wins within %s turns (%.1fs)\n" kind k d (Sys.time () -. t0)
     | Some line ->
       Printf.printf "B survives %s turns against %s %s (%.1fs)\n" d kind k (Sys.time () -. t0);
       print_line line)
  | [| _; "abeat"; starter; kind; k; d |] ->
    (* can B, with every legal move, beat a fixed A policy within d turns? *)
    let t0 = Sys.time () in
    let rec go n =
      if n > int_of_string d then Printf.printf "B can't beat %s %s within %s turns (%.1fs)\n" kind k d (Sys.time () -. t0)
      else match Policy.beat ~mine:moves PB (a_policy kind (int_of_string k)) (init (pl starter)) n with
        | Some line -> Printf.printf "B beats %s %s within %d turns (%.1fs)\n" kind k n (Sys.time () -. t0); print_line line
        | None -> Printf.printf "  (no B win within %d, %.1fs)\n%!" n (Sys.time () -. t0); go (n + 2)
    in
    go 10
  | [| _ |] | [| _; ("-h" | "--help") |] -> usage ()
  | _ -> ()

(* Custom positions at the start of a turn:
   pwin ACTIVE ALIFE AWALKERS ATHOP AHAND BLIFE BWALKERS BTHOP BHAND ELIXIR D
   walkers as comma-separated sizes or "-"; ELIXIR in hand|bf|lib|gone *)
let walkers_of str =
  if str = "-" then [] else
    List.map (fun n -> { counters = int_of_string n; wtapped = false; sick = false })
      (String.split_on_char ',' str)

let position active alife aw athop ahand blife bw bthop bhand el =
  let a = { life = alife; city = true; pool = 0; hand_w = ahand; hand_e = false; bf = walkers_of aw;
            elixir_bf = false; thop_u = athop; thop_t = 0; library = []; gy_w = 0 } in
  let nb = List.length (walkers_of bw) + bhand in
  let b = { life = blife; city = true; pool = 0; hand_w = bhand; hand_e = el = "hand"; bf = walkers_of bw;
            elixir_bf = el = "bf"; thop_u = bthop; thop_t = 0;
            library = (if el = "lib" then [ CElixir ] else []); gy_w = 1 - nb } in
  { active; first_turn = false; sideA = a; sideB = b; cmb = no_combat;
    pend = Window (Upkeep, active, false) }

let () =
  match Sys.argv with
  | [| _; "pwin"; act; al; aw; at; ah; bl; bw; bt; bh; el; d |] ->
    let s = position (pl act) (int_of_string al) aw (int_of_string at) (int_of_string ah)
        (int_of_string bl) bw (int_of_string bt) (int_of_string bh) el in
    (* TCB_WHO=B searches for B's wins instead *)
    let who = if Sys.getenv_opt "TCB_WHO" = Some "B" then PB else PA in
    let name = Show.player who in
    let tbl, wins = Csearch.make ~mine:Reduce.moves ~theirs:Reduce.moves who in
    let rec go k =
      if k > int_of_string d then Printf.printf "no %s win within %s turns\n" name d
      else if wins s k then Printf.printf "%s wins within %d turns\n" name k
      else go (k + 1)
    in
    ignore tbl; go 1
  | _ -> ()

let () =
  match Sys.argv with
  | [| _; "pcheck"; kind; k; act; al; aw; at; ah; bl; bw; bt; bh; el; d |] ->
    let s = position (pl act) (int_of_string al) aw (int_of_string at) (int_of_string ah)
        (int_of_string bl) bw (int_of_string bt) (int_of_string bh) el in
    (match Policy.check PA (a_policy kind (int_of_string k)) s (int_of_string d) with
     | None -> Printf.printf "A's %s %s policy wins within %s turns\n" kind k d
     | Some line -> Printf.printf "B survives %s turns against %s %s\n" d kind k; print_line line)
  | _ -> ()


let () =
  match Sys.argv with
  | [| _; "reach"; starter; c; t; l |] ->
    Explore.moves_fn := Reduce.moves;
    Explore.reach (pl starter) (int_of_string c) (int_of_string t) (int_of_string l)
  | _ -> ()

(* Principal variation of an A win from a custom position: A plays a move
   that keeps the shortest win, B the reply that delays it the most. *)
let () =
  match Sys.argv with
  | [| _; "pline"; act; al; aw; at; ah; bl; bw; bt; bh; el; d |] ->
    let s0 = position (pl act) (int_of_string al) aw (int_of_string at) (int_of_string ah)
        (int_of_string bl) bw (int_of_string bt) (int_of_string bh) el in
    let _, wins = Csearch.make ~mine:Reduce.moves ~theirs:Reduce.moves PA in
    let dmax = int_of_string d in
    let least s = let rec go k = if k > dmax then None else if wins s k then Some k else go (k + 1) in go 0 in
    let rec walk s acc =
      match winner s, least s with
      | Some _, _ | _, None -> List.rev acc
      | None, Some k ->
        let pick =
          if to_move s = PA then
            List.find (fun m -> let s' = step s m in wins s' (Search.tick s s' k)) (Reduce.moves s)
          else
            let score m = let s' = step s m in
              match least s' with Some j -> j - (k - Search.tick s s' k) | None -> max_int in
            List.fold_left (fun (bm, bv) m -> let v = score m in if v > bv then (m, v) else (bm, bv))
              (Pass, min_int) (Reduce.moves s) |> fst
        in
        walk (step s pick) ((s, pick) :: acc)
    in
    (match least s0 with
     | None -> Printf.printf "no A win within %d turns\n" dmax
     | Some k -> Printf.printf "A wins within %d turns:\n" k; print_line (walk s0 []))
  | _ -> ()

let () =
  match Sys.argv with
  | [| _; "pbeat"; pol; act; al; aw; at; ah; bl; bw; bt; bh; el; d |] ->
    let s = position (pl act) (int_of_string al) aw (int_of_string at) (int_of_string ah)
        (int_of_string bl) bw (int_of_string bt) (int_of_string bh) el in
    let policy = match pol with "fortress" -> Policy.b_fortress | "mirror" -> Policy.b_mirror | _ -> Policy.b_smart in
    let rec go k =
      if k > int_of_string d then Printf.printf "no A win against %s within %s turns\n" pol d
      else match Policy.beat PA policy s k with
        | Some line -> Printf.printf "A beats %s within %d turns\n" pol k; print_line line
        | None -> Printf.printf "  (no win within %d)\n%!" k; go (k + 2)
    in
    go 2
  | _ -> ()

(* Turn-start transposition table (Tsearch): deeper searches in the same memory.
   twin STARTER WHO DMIN DMAX; ptwin <position as for pwin> D (TCB_WHO=B for B) *)
let () =
  let report label who d r t0 tbl =
    Printf.printf "%s: %s forces a win within %d turns: %b  (%d nodes, %d table, %.1fs)\n%!"
      label (Show.player who) d r !Tsearch.nodes (Hashtbl.length tbl) (Sys.time () -. t0)
  in
  match Sys.argv with
  | [| _; "twin"; starter; who; dmin; dmax |] ->
    let who = pl who in
    let tbl, wins = Tsearch.make ~mine:Reduce.moves ~theirs:Reduce.moves who in
    for d = int_of_string dmin to int_of_string dmax do
      let t0 = Sys.time () in
      let r = wins (init (pl starter)) d in
      report (starter ^ " first") who d r t0 tbl
    done
  | [| _; "ptwin"; act; al; aw; at; ah; bl; bw; bt; bh; el; d |] ->
    let s = position (pl act) (int_of_string al) aw (int_of_string at) (int_of_string ah)
        (int_of_string bl) bw (int_of_string bt) (int_of_string bh) el in
    let who = if Sys.getenv_opt "TCB_WHO" = Some "B" then PB else PA in
    let tbl, wins = Tsearch.make ~mine:Reduce.moves ~theirs:Reduce.moves who in
    let rec go k =
      if k <= int_of_string d then begin
        let t0 = Sys.time () in
        let r = wins s k in
        report "position" who k r t0 tbl;
        if not r then go (k + 1)
      end
    in
    go 1
  | _ -> ()

(* Fixed points on the finite abstraction (Fix):
   fix safe|win A|B T TT LMAX STARTER; pfix safe|win A|B T TT LMAX <position as for pwin> *)
let () =
  let cfg who t ot tt ott lmax ~fulla ~macro ~fullopp =
    { Fix.prot = pl who; t; ot; tt; ott; lmax;
      full_a = pl who = PB && fulla;
      (* macro: the protagonist only uses its macro move set (a sound
         restriction); TCB_FULLMINE=1 gives it every legal move instead *)
      mine = (if Sys.getenv_opt "TCB_FULLMINE" = Some "1" then Rules.moves
              else if not macro then Reduce.moves else if pl who = PB then Reduce.b_macro else Reduce.a_macro);
      (* fullopp: the opponent gets every legal move, not just the filter's *)
      theirs = (if fullopp then Rules.moves else Reduce.moves) }
  in
  let flag v = Sys.getenv_opt v = Some "1" in
  let run mode who t tt lmax s0 =
    let t = int_of_string t and tt = int_of_string tt and lmax = int_of_string lmax in
    let ot = env_int "TCB_OT" t and ott = env_int "TCB_OTT" tt and fulla = flag "TCB_FULLA" and macro = flag "TCB_MACRO"
    and fullopp = flag "TCB_FULLOPP" in
    let c = cfg who t ot tt ott lmax ~fulla ~macro ~fullopp in
    let t0 = Unix.gettimeofday () in
    (* TCB_LINE=N prints N turns of a line of play; TCB_RANKS=1 or TCB_LINE
       computes the rounds a line needs *)
    let n = env_int "TCB_LINE" 0 in
    let ranks = n > 0 || flag "TCB_RANKS" in
    (* TCB_SAVE=DIR solves in DIR and keeps it as a saved table; otherwise the
       solver works in a temporary directory under TCB_WORK (default tables/) *)
    let dir = match Sys.getenv_opt "TCB_SAVE" with
      | Some d -> d
      | None ->
        let base = Option.value (Sys.getenv_opt "TCB_WORK") ~default:"tables" in
        Filename.concat base (Printf.sprintf ".work-%d" (Unix.getpid ())) in
    let b i = if i then "1" else "0" in
    (* TCB_FROM=TABLE warm-starts a win from a table of the same check that
       is no better for the protagonist: caps no larger, and if anything a
       macro protagonist or an opponent with every legal move *)
    let warm = match Sys.getenv_opt "TCB_FROM" with
      | None -> None
      | Some p ->
        let h, wsv = Fix.load p in
        let g k = List.assoc k h in
        let gi k = int_of_string (g k) in
        let gott = match List.assoc_opt "ott" h with Some v -> int_of_string v | None -> gi "tt" in
        let same k v = if g k <> v then failwith (Printf.sprintf "TCB_FROM: %s has %s=%s, not %s" p k (g k) v) in
        same "mode" mode; same "who" who; same "fulla" (b fulla);
        (* restrictions the old table may have had but this run drops *)
        let lifted k v = if v && g k = "0" then failwith (Printf.sprintf "TCB_FROM: %s has %s=0, this run 1" p k) in
        lifted "macro" macro; lifted "fullopp" fullopp;
        (* the protagonist's macro: the old table's restrictions must
           include this run's (old tables without the list had them all) *)
        if macro then begin
          let key, mine, all = if who = "B" then ("bmacro", Reduce.b_macro_rules, [ "blk"; "tr"; "atk"; "dmg" ])
            else ("amacro", Reduce.a_macro_rules, [ "atk"; "pump"; "order"; "dmg" ]) in
          let rules = match List.assoc_opt key h with Some l -> String.split_on_char ',' l | None -> all in
          (* atkN restricts more the smaller N is; atk is atk0 *)
          let covered r = match Reduce.held_of r with
            | Some n -> List.exists (fun r' -> match Reduce.held_of r' with Some m -> m <= n | None -> false) rules
            | None -> List.mem r rules in
          List.iter (fun r -> if not (covered r) then
                        failwith (Printf.sprintf "TCB_FROM: %s lacks macro rule %s" p r)) mine
        end;
        if ranks then failwith "TCB_FROM: a warm start has no ranks (drop TCB_RANKS and TCB_LINE)";
        if mode <> "win" || gi "t" > t || gi "ot" > ot || gi "tt" > tt || gott > ott || gi "lmax" > lmax then
          failwith "TCB_FROM: needs a win table with caps no larger than this run's";
        Some { Fix.wc = cfg who t (gi "ot") (gi "tt") gott (gi "lmax") ~fulla ~macro ~fullopp; wsv }
    in
    let sv = if mode = "safe" then Fix.safe c s0 dir else Fix.win ~ranks ?warm c s0 dir in
    Printf.printf "%s %s from the start position: %s  (%.1fs)\n%!" who mode (Fix.show c (Fix.value c sv s0))
      (Unix.gettimeofday () -. t0);
    if n > 0 then Fix.line c sv s0 s0.sideB.life n;
    match Sys.getenv_opt "TCB_SAVE" with
    | Some path ->
      Fix.save_meta sv
        [ ("mode", mode); ("who", who); ("t", string_of_int t); ("ot", string_of_int ot);
          ("tt", string_of_int tt); ("ott", string_of_int ott); ("lmax", string_of_int lmax); ("fulla", b fulla);
          ("macro", b macro); ("bmacro", String.concat "," Reduce.b_macro_rules);
          ("amacro", String.concat "," Reduce.a_macro_rules); ("fullopp", b fullopp); ("blife", string_of_int s0.sideB.life);
          ("start", Fix.hex (Fix.key_gen c.full_a s0)) ];
      Printf.printf "saved %d positions to %s\n%!" sv.n path
    | None -> Fix.remove sv
  in
  (* fixload TABLE [N [BLIFE]]: the value of the saved start position, and a
     line of N turns (tables saved with ranks only). TABLE is a saved
     directory, or an old single-file table (converted once, into TABLE.d).
     TCB_START=A or B looks up that player's opening instead, if the table
     reached it. *)
  let load path n blife =
    let h, sv = Fix.load path in
    let g k = List.assoc k h in
    let gi k = int_of_string (g k) in
    let ott = match List.assoc_opt "ott" h with Some v -> int_of_string v | None -> gi "tt" in
    let c = cfg (g "who") (gi "t") (gi "ot") (gi "tt") ott (gi "lmax") ~fulla:(g "fulla" = "1")
        ~macro:(g "macro" = "1") ~fullopp:(g "fullopp" = "1") in
    let s0 = match Sys.getenv_opt "TCB_START" with
      | Some p -> init (pl p)
      | None -> Fix.of_key (Fix.unhex (g "start")) in
    let life = match blife with Some l -> l | None -> gi "blife" in
    match Fix.value c sv s0 with
    | exception Not_found -> Printf.printf "%s: the start position is not in this table\n" path
    | v ->
    Printf.printf "%s: %s %s, %d positions; start position: %s\n" path (g "who") (g "mode") sv.Fix.n
      (Fix.show c v);
    if n > 0 then
      begin
        if not (Fix.has_ranks sv) then
          print_endline "(no ranks saved: this line keeps values but may not make progress; re-solve with TCB_RANKS=1 for one that does)";
        Fix.line c sv s0 life n
      end
  in
  (* fixcmp OLD NEW: every position of table OLD has the same value in NEW *)
  let compare_tables a b =
    let _, sa = Fix.load a and _, sb = Fix.load b in
    let missing = ref 0 and differ = ref 0 in
    (* TCB_DIFFS=FILE lists the differing positions: OLD's index and both values *)
    let diffs = Option.map Disk.out (Sys.getenv_opt "TCB_DIFFS") in
    for i = 0 to sa.Fix.n - 1 do
      match Fix.id sb (Fix.key_at sa i) with
      | j ->
        let va = Fix.get sa i and vb = Fix.get sb j in
        if va <> vb then begin
          incr differ;
          Option.iter (fun oc -> List.iter (Disk.output_int32 oc) [ i; va; vb ]) diffs
        end
      | exception Not_found -> incr missing
    done;
    Option.iter close_out diffs;
    Printf.printf "%d positions of %s: %d differ in %s, %d missing from it\n" sa.Fix.n a !differ b !missing
  in
  match Sys.argv with
  | [| _; "fixcmp"; a; b |] -> compare_tables a b
  | [| _; "certify"; dir; starter |] -> Certify.run dir (pl starter)
  | [| _; "certify-win"; dir; starter |] -> Certify.certify_win dir (pl starter)
  | [| _; "certify-safe-export"; dir; starter; outdir; chunks; fuel |] ->
    Certify.certify_safe_export dir (pl starter) ~outdir ~chunks:(int_of_string chunks) ~fuel:(int_of_string fuel)
  | [| _; "certify-win-export"; dir; starter; outdir; chunks; fuel |] ->
    Certify.certify_win dir (pl starter)
      ~export:(Certify.export_rocq ~outdir ~chunks:(int_of_string chunks) ~fuel:(int_of_string fuel))
  | [| _; "win-depth"; dir; starter |] -> Certify.win_depth dir (pl starter)
  | [| _; "win-cost"; dir; starter; n |] -> Certify.win_cost dir (pl starter) (int_of_string n)
  | [| _; "certify-debug"; dir; hex; v |] -> Certify.debug dir hex (int_of_string v)
  | [| _; "walk"; seed; steps |] -> Walk.run (int_of_string seed) (int_of_string steps)
  | [| _; "walk"; seed; steps; "bias" |] -> Walk.run ~bias:true (int_of_string seed) (int_of_string steps)
  | [| _; "fix"; mode; who; t; tt; lmax; starter |] -> run mode who t tt lmax (init (pl starter))
  | [| _; "fixload"; path |] -> load path 0 None
  | [| _; "fixload"; path; n |] -> load path (int_of_string n) None
  | [| _; "fixload"; path; n; l |] -> load path (int_of_string n) (Some (int_of_string l))
  | [| _; "pfix"; mode; who; t; tt; lmax; act; al; aw; at; ah; bl; bw; bt; bh; el |] ->
    let s = position (pl act) (int_of_string al) aw (int_of_string at) (int_of_string ah)
        (int_of_string bl) bw (int_of_string bt) (int_of_string bh) el in
    run mode who t tt lmax s
  | _ -> ()
