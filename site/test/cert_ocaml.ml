(* Differential check of the site's certified B (site/engine/src/cert.rs)
   against the Rocq model extracted to OCaml (_build/default/solver/model.ml,
   which includes [check_win], [key], [entry], [huge_event], [too_many] and
   [is_turn_start]). Built and run by test/cert-ocaml.sh.

     cert_ocaml trace DATA_V START STEP COUNT CAP
       For records START, START+STEP, ...: the nodes [check_win] visits, in
       the format of `cert-tool trace` (state and legal moves at each node
       that searches moves, lookups at turn starts). CAP > 0 prints the
       first CAP lines and then "R j ok"; CAP = 0 prints only
       "R j ok lines md5" over the whole search. [ok] is the result of the
       extracted [check_win] itself; the hand-written traversal must agree
       with it.
     cert_ocaml replay < GAMES
       Each input line is a game record "starter lifeA lifeB m1 m2 ...";
       prints every position along it with its legal moves, as
       `cert-tool replay`.

   The table is read from Data.v itself, and [lookup]/[below] follow
   proofs/core/Packed.v, independently of the site's binary table and of
   cert.rs. *)
open Model

(* ---- Data.v ---- *)

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let find_from s i sub =
  let n = String.length sub in
  let rec go i = if i + n > String.length s then raise Not_found
    else if String.sub s i n = sub then i else go (i + 1) in
  go i

let def text name =
  let pat = "\nDefinition " ^ name ^ " " in
  let i = find_from text 0 pat + String.length pat in
  let j = find_from text i ":=" + 2 in
  (text, j)

let nat_def text name =
  let _, j = def text name in
  let k = find_from text j ".\n" in
  int_of_string (String.trim (String.sub text j (k - j)))

let array_def text name =
  let _, j = def text name in
  let a = find_from text j "[|" + 2 in
  let b = find_from text a "|" in
  (* a loop, not lists: the arrays have 1.5M entries *)
  let out = ref [||] and n = ref 0 in
  let push x =
    if !n = Array.length !out then out := Array.append !out (Array.make (max 1024 !n) 0);
    !out.(!n) <- x; incr n in
  let i = ref a in
  while !i < b do
    let j = try min b (String.index_from text !i ';') with Not_found -> b in
    push (int_of_string (String.trim (String.sub text !i (j - !i))));
    i := j + 1
  done;
  Array.sub !out 0 !n

(* ---- Packed.v ---- *)

let put off w x = (x land ((1 lsl w) - 1)) lsl off
let b2i b = if b then 1 else 0
let field i off k = (i lsr off) land ((1 lsl k) - 1)
let bit i off = (i lsr off) land 1 = 1

let enc_walker w = put 0 5 w.counters lor put 5 1 (b2i w.wtapped) lor put 6 1 (b2i w.sick)
let enc_card = function CWalker -> 0 | CElixir -> 1

let enc_side sd =
  let wslot n = match List.nth_opt sd.bf n with Some w -> enc_walker w | None -> 0 in
  let cslot n = match List.nth_opt sd.library n with Some c -> enc_card c | None -> 0 in
  List.fold_right ( lor )
    [ put 0 5 sd.life; put 5 1 (b2i sd.city); put 6 3 sd.pool; put 9 2 sd.hand_w; put 11 1 (b2i sd.hand_e);
      put 12 1 (b2i sd.elixir_bf); put 13 5 sd.thop_u; put 18 5 sd.thop_t; put 23 2 sd.gy_w;
      put 25 2 (List.length sd.bf); put 27 7 (wslot 0); put 34 7 (wslot 1); put 41 7 (wslot 2);
      put 48 2 (List.length sd.library); put 50 1 (cslot 0); put 51 1 (cslot 1); put 52 1 (cslot 2) ] 0

let player_bit = function PA -> false | PB -> true

let enc s =
  (enc_side s.sideA lor put 53 1 (b2i (player_bit s.active)) lor put 54 1 (b2i s.first_turn), enc_side s.sideB)

let rec firstn n l = match n, l with 0, _ | _, [] -> [] | n, x :: r -> x :: firstn (n - 1) r

let dec_walker x = { counters = field x 0 5; wtapped = bit x 5; sick = bit x 6 }
let dec_card b = if b then CElixir else CWalker

let dec_side x =
  { life = field x 0 5; city = bit x 5; pool = field x 6 3; hand_w = field x 9 2; hand_e = bit x 11;
    bf = firstn (field x 25 2) [ dec_walker (x lsr 27); dec_walker (x lsr 34); dec_walker (x lsr 41) ];
    elixir_bf = bit x 12; thop_u = field x 13 5; thop_t = field x 18 5;
    library = firstn (field x 48 2) [ dec_card (bit x 50); dec_card (bit x 51); dec_card (bit x 52) ];
    gy_w = field x 23 2 }

let dec k1 k2 =
  let p = if bit k1 53 then PB else PA in
  { active = p; first_turn = bit k1 54; sideA = dec_side k1; sideB = dec_side k2; cmb = no_combat;
    pend = Window (Upkeep, p, false) }

type table = { h : int; ott : int; tt : int; fuel : int; k1 : int array; k2 : int array; rv : int array }

let rank_of t j = (t.rv.(j) lsr 6) land 0xffff
let val_of t j = t.rv.(j) land 63
let get a j = if j < Array.length a then a.(j) else 0

let start t k1 k2 =
  let rec lower f lo hi =
    if f = 0 then lo
    else if lo < hi then
      let mid = (lo + hi) lsr 1 in
      let a1 = get t.k1 mid and a2 = get t.k2 mid in
      if a1 < k1 || (a1 = k1 && a2 < k2) then lower (f - 1) (mid + 1) hi else lower (f - 1) lo mid
    else lo
  in
  lower 32 0 (Array.length t.k1)

let at_key t j k1 k2 = j < Array.length t.k1 && t.k1.(j) = k1 && t.k2.(j) = k2

let rec scan t f j k1 k2 r =
  if f = 0 then None
  else if at_key t j k1 k2 then (if rank_of t j = r then Some j else scan t (f - 1) (j + 1) k1 k2 r)
  else None

let rec scan_below t f j k1 k2 r best =
  if f = 0 then best
  else if at_key t j k1 k2 then
    scan_below t (f - 1) (j + 1) k1 k2 r (if rank_of t j < r then Some (rank_of t j) else best)
  else best

let lookup t s r =
  let k1, k2 = enc s in
  match scan t 64 (start t k1 k2) k1 k2 r with
  | Some j -> if dec k1 k2 = s then Some (val_of t j) else None
  | None -> None

let below t s r =
  let k1, k2 = enc s in
  scan_below t 64 (start t k1 k2) k1 k2 r None

let hint _ _ = true

(* ---- text, as solver/walk.ml and rsolver/src/walk.rs ---- *)

let b x = if x then "1" else "0"
let step_i = function
  | Upkeep -> 0 | DrawStep -> 1 | Main1 -> 2 | BeginCombat -> 3 | DeclAtk -> 4
  | DeclBlk -> 5 | DamageStep -> 6 | EndCombat -> 7 | Main2 -> 8 | EndStep -> 9
let pl = function PA -> "A" | PB -> "B"
let list f l = "[" ^ String.concat ";" (List.map f l) ^ "]"
let card = function CWalker -> "W" | CElixir -> "E"
let blocker = function BT -> "T" | BW i -> "W" ^ string_of_int i

let side sd =
  Printf.sprintf "%d,%s,%d,%d,%s,%s,%s,%d,%d,%s,%d" sd.life (b sd.city) sd.pool sd.hand_w (b sd.hand_e)
    (list (fun w -> Printf.sprintf "%d:%s:%s" w.counters (b w.wtapped) (b w.sick)) sd.bf)
    (b sd.elixir_bf) sd.thop_u sd.thop_t (list card sd.library) sd.gy_w

let pend = function
  | Window (st, p, x) -> Printf.sprintf "W%d,%s,%s" (step_i st) (pl p) (b x)
  | ChooseAttack -> "CA" | ChooseBlock -> "CB" | ChooseOrder -> "CO" | ChooseDamage -> "CD"
  | ChooseShuffle (st, p, cs) -> Printf.sprintf "CS%d,%s,%s" (step_i st) (pl p) (list card cs)
  | Over p -> "O" ^ pl p

let state s =
  Printf.sprintf "S act=%s ft=%s pend=%s cmb=%s/%d/%s/%d A=%s B=%s" (pl s.active) (b s.first_turn) (pend s.pend)
    (list string_of_int s.cmb.atk) s.cmb.atk_thop (list (list blocker) s.cmb.blk) s.cmb.trades
    (side s.sideA) (side s.sideB)

let move = function
  | Pass -> "P" | Pump i -> "U" ^ string_of_int i | ActElixir -> "X" | CastWalker x -> "C" ^ string_of_int x
  | CastElixir -> "E"
  | Attack (ws, k) -> "A" ^ list string_of_int ws ^ string_of_int k
  | Block (wb, tb, tr) ->
    "B" ^ list (function None -> "-" | Some i -> string_of_int i) wb ^ list string_of_int tb ^ string_of_int tr
  | Order os -> "O" ^ list (list blocker) os
  | Assign js -> "S" ^ list string_of_int js
  | Arrange l -> "R" ^ list card l

(* ---- the checker's search, as text ---- *)

let trace t buf lines cap r0 s0 =
  let emit line =
    if !lines < cap then (Buffer.add_string buf line; Buffer.add_char buf '\n');
    incr lines
  in
  let rec go fuel root s =
    if fuel = 0 then (emit "F"; false)
    else
      match winner s with
      | Some p -> emit ("O" ^ pl p); p = PB
      | None ->
        if (not root) && is_turn_start s then begin
          let k = key t.h t.tt s in
          let bl = below t k r0 in
          let v = match bl with Some r2 when r2 < r0 -> lookup t k r2 | _ -> None in
          let f = function Some x -> string_of_int x | None -> "-" in
          emit (Printf.sprintf "L %s %s %d" (f bl) (f v) s.sideB.life);
          match v with Some v -> v <= s.sideB.life | None -> false
        end
        else if huge_event t.h s then (emit "H"; false)
        else begin
          let ms = moves s in
          emit (state s);
          emit ("M " ^ String.concat " " (List.map move ms));
          let child m =
            let s' = step s m in
            if too_many t.ott s' then (emit "T"; false) else go (fuel - 1) false s'
          in
          match to_move s with
          | PB -> List.exists child ms
          | PA -> ms <> [] && List.for_all child ms
        end
  in
  go t.fuel true s0

let trace_cmd path start stride count cap =
  let text = read_file path in
  let t = { h = nat_def text "H"; ott = nat_def text "ott"; tt = nat_def text "tt"; fuel = nat_def text "fuel";
            k1 = array_def text "K1"; k2 = array_def text "K2"; rv = array_def text "RV" } in
  let n = Array.length t.k1 in
  assert (Array.length t.k2 = n && Array.length t.rv = n);
  for c = 0 to count - 1 do
    let j = start + (c * stride) in
    if j < n then begin
      let s = entry (dec t.k1.(j) t.k2.(j)) (val_of t j) in
      let r = rank_of t j in
      let ok = check_win t.h t.ott t.tt (lookup t) (below t) hint r t.fuel true s in
      let buf = Buffer.create 4096 and lines = ref 0 in
      let ok' = trace t buf lines (if cap = 0 then max_int else cap) r s in
      if ok <> ok' then Printf.printf "MISMATCH %d: check_win %b, traversal %b\n" j ok ok';
      if cap = 0 then
        Printf.printf "R %d %b %d %s\n" j ok !lines (Digest.to_hex (Digest.string (Buffer.contents buf)))
      else (print_string (Buffer.contents buf); Printf.printf "R %d %b\n" j ok)
    end
  done

(* ---- game records ---- *)

let replay_cmd () =
  try
    while true do
      let line = input_line stdin in
      match List.filter (( <> ) "") (String.split_on_char ' ' (String.trim line)) |> List.map int_of_string with
      | starter :: la :: lb :: ms ->
        let s = init (if starter = 0 then PA else PB) in
        let s = { s with sideA = { s.sideA with life = la }; sideB = { s.sideB with life = lb } } in
        let show s =
          print_endline (state s);
          print_endline ("M " ^ String.concat " " (List.map move (moves s)))
        in
        let s = List.fold_left (fun s i -> show s; step s (List.nth (moves s) i)) s ms in
        show s;
        print_endline "G"
      | _ -> ()
    done
  with End_of_file -> ()

let () =
  match Sys.argv with
  | [| _; "trace"; path; start; stride; count; cap |] ->
    trace_cmd path (int_of_string start) (int_of_string stride) (int_of_string count) (int_of_string cap)
  | [| _; "replay" |] -> replay_cmd ()
  | _ -> prerr_endline "usage: cert_ocaml trace DATA_V START STEP COUNT CAP | replay < GAMES"; exit 2
