(* Unbounded-horizon solving on a finite abstraction of the game.

   Three reductions make the set of turn-start positions finite:

   - B's life is not part of the position. Every property computed here is
     monotone in B's life, so a position gets a threshold instead: for B's
     properties the least life B needs, for A's the most life B may have.
     Life only shifts along a turn (damage, Elixir), so thresholds compose
     exactly and this loses nothing.

   - The protagonist's own resources are capped: its Walkers stop pumping at
     [t] counters and Thopters above [tt] are discarded. Both only take
     options away from the protagonist (a Thopter is never a liability: its
     controller may ignore it), so results stay sound.

   - The opponent's resources saturate: a Walker pumped past [t] counters is
     "huge" (kept at t+1), and anything whose outcome would depend on its
     exact size counts as a loss for the protagonist: it dealing damage to the
     protagonist, it dying (its Thopters are unbounded), or being blocked by
     more toughness than t+1. More than [ott] opposing Thopters is also a loss.

   [safe] computes a greatest fixed point (the protagonist never loses), [win]
   a least one (it wins). Thresholds are cut to [lmax] on the pessimistic
   side: B needing more life than that counts as "never", and A's bound on B's
   life is lowered to it. *)
open Model
open Rules

let inf = max_int / 4
let ninf = min_int / 4
let big = 1000  (* B's life while a turn is searched, so the model never ends the game for B *)

type cfg = {
  prot : player;
  t : int;   (* the protagonist's Walkers stop at t counters *)
  ot : int;  (* the opponent's Walkers are huge above ot counters *)
  tt : int;   (* the protagonist's Thopters above tt are discarded *)
  ott : int;  (* more than ott opposing Thopters is a loss *)
  lmax : int;
  full_a : bool;  (* B protagonist only: A's life is reset to 20 at each turn start *)
  mine : state -> move list;
  theirs : state -> move list;
}

(* B is the protagonist: values are least life needed, smaller is better.
   A is the protagonist: values are most life allowed, larger is better. *)
let up c = c.prot = PB
let best c a b = if up c then min a b else max a b
let worst c a b = if up c then max a b else min a b
let lose c = if up c then inf else ninf
let shift v d = if v >= inf || v <= ninf then v else v - d

(* Normalise a turn-start value: B's life is at least 1 there. *)
let norm c v =
  if up c then (if v > c.lmax then inf else if v <= 1 then 1 else v)
  else if v < 1 then ninf else if v >= inf then inf else min v c.lmax

let side_of p s = get_side p s
let huge c = c.ot + 1

(* Drop what the abstraction ignores: B's life (a threshold instead), A's
   graveyard (A has no Elixir), and with [full_a] A's life. *)
let normal full_a s =
  let s = Explore.canon s in
  let b = s.sideB and a = s.sideA in
  let a = { a with gy_w = 0; life = (if full_a then 20 else a.life) } in
  { s with sideA = a; sideB = { b with life = 0 } }

(* Key of any position, used inside a turn. *)
let key s = Marshal.to_string (normal false s) [ Marshal.No_sharing ]

(* Turn-start positions get a packed key, about a third of the marshalled
   size: a flags byte, then per side life, flags, pool, Walkers in hand,
   graveyard, Thopters (untapped, tapped), the Walkers (counters and flags
   each) and the library. *)
let pack_side buf sd =
  let byte n = assert (n >= 0 && n < 256); Buffer.add_char buf (Char.chr n) in
  let bit b k = if b then 1 lsl k else 0 in
  byte sd.life;
  byte (bit sd.city 0 lor bit sd.hand_e 1 lor bit sd.elixir_bf 2);
  byte sd.pool; byte sd.hand_w; byte sd.gy_w; byte sd.thop_u; byte sd.thop_t;
  byte (List.length sd.bf);
  List.iter (fun w -> byte w.counters; byte (bit w.wtapped 0 lor bit w.sick 1)) sd.bf;
  byte (List.length sd.library);
  List.iter (fun c -> byte (match c with CWalker -> 0 | CElixir -> 1)) sd.library

let key_gen full_a s =
  assert (Search.is_turn_start s && s.cmb = no_combat);
  let s = normal full_a s in
  let buf = Buffer.create 32 in
  Buffer.add_char buf (Char.chr ((if s.active = PA then 0 else 1) lor if s.first_turn then 2 else 0));
  pack_side buf s.sideA;
  pack_side buf s.sideB;
  Buffer.contents buf

let of_key k : state =
  let pos = ref 0 in
  let byte () = let n = Char.code k.[!pos] in incr pos; n in
  let side () =
    let life = byte () in
    let f = byte () in
    let pool = byte () in
    let hand_w = byte () in
    let gy_w = byte () in
    let thop_u = byte () in
    let thop_t = byte () in
    let bf = List.init (byte ()) (fun _ ->
        let counters = byte () in let g = byte () in
        { counters; wtapped = g land 1 <> 0; sick = g land 2 <> 0 }) in
    let library = List.init (byte ()) (fun _ -> if byte () = 0 then CWalker else CElixir) in
    { life; city = f land 1 <> 0; pool; hand_w; hand_e = f land 2 <> 0; bf; elixir_bf = f land 4 <> 0;
      thop_u; thop_t; library; gy_w }
  in
  let g = byte () in
  let active = if g land 1 = 0 then PA else PB in
  let sideA = side () in
  let sideB = side () in
  { active; first_turn = g land 2 <> 0; sideA; sideB = { sideB with life = big }; cmb = no_combat;
    pend = Window (Upkeep, active, false) }

(* Diagnostics only (unsound): TCB_LAX lists conservative rules to relax,
   so a failing check can be traced to the reduction responsible:
   dmg (a huge Walker's damage is its representative's), die (a huge Walker
   may die or be over-blocked; its Thopters are its representative's),
   many (opposing Thopters beyond ott are discarded instead of losing). *)
let lax =
  match Sys.getenv_opt "TCB_LAX" with
  | None -> []
  | Some l -> String.split_on_char ',' l

(* Clamp after a step: the opponent's Walkers at most huge, the
   protagonist's Thopters at most tt (tapped ones go first), and with
   TCB_LAX=many the opponent's at most ott. *)
let clamp c s =
  let o = opp c.prot in
  let os = side_of o s in
  let os = { os with bf = List.map (fun w -> if w.counters > huge c then { w with counters = huge c } else w) os.bf } in
  let cut tt sd =
    let extra = sd.thop_u + sd.thop_t - tt in
    if extra <= 0 then sd
    else
      let dt = min extra sd.thop_t in
      { sd with thop_t = sd.thop_t - dt; thop_u = sd.thop_u - (extra - dt) }
  in
  let os = if List.mem "many" lax then cut c.ott os else os in
  set_side c.prot (cut c.tt (side_of c.prot s)) (set_side o os s)

(* Does this move make an exact huge size matter (a loss for the protagonist)? *)
let huge_event c s m =
  let o = opp c.prot in
  let strict r = not (List.mem r lax) in
  match s.pend, m with
  | ChooseDamage, Assign _ ->
    let att = side_of s.active s and def = side_of (opp s.active) s in
    let is_huge sd i = (List.nth sd.bf i).counters >= huge c in
    let tough sd = function BW i -> (List.nth sd.bf i).counters | BT -> 1 in
    let total bs = List.fold_left (fun n b -> n + tough def b) 0 bs in
    let fights = List.combine s.cmb.atk s.cmb.blk in
    (* an attacking huge Walker of the opponent that is unblocked *)
    (strict "dmg" && s.active = o && List.exists (fun (i, bs) -> is_huge att i && bs = []) fights)
    (* ... or blocked by enough toughness to matter: it may die, or kill more than its representative *)
    || (strict "die" && s.active = o
        && List.exists (fun (i, bs) -> is_huge att i && bs <> [] && total bs >= huge c) fights)
    (* a huge blocking Walker of the opponent that its attacker could kill *)
    || (strict "die" && s.active <> o
        && List.exists (fun (i, bs) ->
            List.exists (function BW j -> is_huge def j && (List.nth att.bf i).counters >= huge c | BT -> false) bs)
          fights)
  | _ -> false

let too_many c s =
  (not (List.mem "many" lax)) && let os = side_of (opp c.prot) s in os.thop_u + os.thop_t > c.ott

let moves_for c s =
  if to_move s = c.prot then
    let ps = side_of c.prot s in
    List.filter (function Pump i -> (List.nth ps.bf i).counters < c.t | _ -> true) (c.mine s)
  else c.theirs s

(* Value from [s], given the table; [root] marks the turn start the search
   began at (turn starts after it are looked up). *)
let eval_from c (lookup : string -> int) s root =
  let local = Hashtbl.create 256 in
  let rec go s root =
    match winner s with
    | Some PB -> ninf  (* A died: a win for B, a loss for A *)
    | Some PA -> assert false
    | None ->
      if (not root) && Search.is_turn_start s then lookup (key_gen c.full_a s)
      else begin
        let k = key s in
        match Hashtbl.find_opt local k with
        | Some v -> v
        | None ->
          let ms = moves_for c s in
          let pick = if to_move s = c.prot then best c else worst c in
          let v =
            List.fold_left (fun acc m -> pick acc (edge s m))
              (if to_move s = c.prot then lose c else if up c then ninf else inf) ms
          in
          Hashtbl.replace local k v;
          v
      end
  and edge s m =
    if huge_event c s m then lose c
    else
      let s' = clamp c (step s m) in
      if too_many c s' then lose c
      else
        let d = s'.sideB.life - s.sideB.life in
        let v = shift (go s' false) d in
        if d < 0 then (if up c then max (1 - d) v else max (-d) v) else v
  in
  go s root

(* Value of the turn starting at [s] (a turn start). *)
let eval_turn c lookup s = eval_from c lookup s true

(* The same turn, compiled once into a straight-line program over the values
   of the turn starts it can end in, so re-evaluating it needs no model
   steps. Nodes come in post-order. A node is a header word (2n + pick, pick
   0 for the protagonist) and n children of two words each: x, then
   4d + kind, where d is the change in B's life on that edge and kind is
   0 for a constant (x = 0 for ninf, 1 for inf), 1 for node number x, 2 for
   turn start x (given by [tgt]). Single-child nodes are inlined and
   children that can never be picked are dropped.

   A's life only matters at one point of a turn: combat damage to A, after
   which A is dead if the damage reached its life. Turns are compiled with
   A on [sent] life, which no turn can take, and the damage step gets a
   guard node: its header carries the damage u (header lsr 16), and at an
   A-life level of at most u the node is a win for B. The header's low bits
   are 2n + pick as usual. *)
type cref = Const of int | Ref of int * int * int  (* kind, x, d *)

let sent = 100

let compile c (tgt : state -> int) s =
  let local = Hashtbl.create 256 in
  let buf = ref [] and nodes = ref 0 in
  let lost = if lose c = ninf then 0 else 1 in
  let won = 1 - lost in
  let rec go s root =
    match winner s with
    | Some PB -> Const 0
    | Some PA -> assert false
    | None ->
      if (not root) && Search.is_turn_start s then Ref (2, tgt s, 0)
      else begin
        let k = key s in
        match Hashtbl.find_opt local k with
        | Some r -> r
        | None ->
          let mine = to_move s = c.prot in
          (* the constant the chooser can never prefer, and the one that decides the node *)
          let useless = if mine then lost else won and decisive = if mine then won else lost in
          let kids = List.map (fun m -> edge s m) (moves_for c s) in
          let r =
            if List.mem (Const decisive) kids then Const decisive
            else
              match List.sort_uniq compare (List.filter (fun r -> r <> Const useless) kids) with
              | [] -> Const useless
              | [ r ] -> r
              | kids ->
                assert (List.length kids < 0x8000);
                buf := ((2 * List.length kids) + if mine then 0 else 1) :: !buf;
                List.iter (function
                    | Ref (kind, x, d) -> buf := ((4 * d) + kind) :: x :: !buf
                    | Const v -> buf := 0 :: v :: !buf) kids;
                incr nodes;
                Ref (1, !nodes - 1, 0)
          in
          Hashtbl.replace local k r;
          r
      end
  and edge s m =
    if huge_event c s m then Const lost
    else
      let s' = clamp c (step s m) in
      if too_many c s' then Const lost
      else
        let d = s'.sideB.life - s.sideB.life and u = s.sideA.life - s'.sideA.life in
        assert (u = 0 || d = 0);
        let wrap kind x d' = buf := ((4 * d') + kind) :: x :: 2 :: !buf; incr nodes; Ref (1, !nodes - 1, d) in
        let r =
          match go s' false with
          | Const v when d >= 0 -> Const v  (* constants are sentinels: shifts don't move them *)
          | Const v -> wrap 0 v 0  (* but B may die on this edge *)
          | Ref (kind, x, 0) -> Ref (kind, x, d)
          | Ref (kind, x, d') when d = 0 -> Ref (kind, x, d')
          | Ref (kind, x, d') -> wrap kind x d'  (* two life changes on one path: the inner one gets its own node *)
        in
        (* combat damage to A: a guard node *)
        match r with
        | _ when u = 0 -> r
        | Const 0 -> r
        | Const v -> buf := 0 :: v :: ((u lsl 16) lor 2) :: !buf; incr nodes; Ref (1, !nodes - 1, 0)
        | Ref (kind, x, d') -> buf := ((4 * d') + kind) :: x :: ((u lsl 16) lor 2) :: !buf; incr nodes; Ref (1, !nodes - 1, 0)
  in
  let root = go s true in
  (* make sure the program ends with the root node *)
  (match root with
   | Ref (1, n, 0) when n = !nodes - 1 -> ()
   | Ref (kind, x, d) -> buf := ((4 * d) + kind) :: x :: 2 :: !buf; incr nodes
   | Const v -> buf := 0 :: v :: 2 :: !buf; incr nodes);
  let l = List.rev !buf in
  let a = Bigarray.(Array1.create int32 c_layout (List.length l)) in
  List.iteri (fun i x -> a.{i} <- Int32.of_int x) l;
  (a, !nodes)

(* Values are stored as 32-bit ints, with the sentinels ninf and inf as the
   int32 extremes. *)
let to32 v = if v <= ninf then -0x40000000 else if v >= inf then 0x3fffffff else v
let of32 v = if v = -0x40000000 then ninf else if v = 0x3fffffff then inf else v

(* Evaluate the program of [nodes] nodes at word [off] of [prog], at A-life
   level [l]. *)
let run c l (value : int -> int) prog off nodes =
  let get i = Int32.to_int (Bigarray.Array1.unsafe_get prog (off + i)) in
  let nv = Array.make nodes 0 in
  let pc = ref 0 in
  for n = 0 to nodes - 1 do
    let h = get !pc in
    let mine = h land 1 = 0 in
    let pick = if mine then best c else worst c in
    let cnt = (h lsr 1) land 0x7fff and guard = h lsr 16 in
    incr pc;
    let acc = ref (if mine then lose c else if up c then ninf else inf) in
    for _ = 1 to cnt do
      let x = get !pc and kd = get (!pc + 1) in
      pc := !pc + 2;
      let kind = kd land 3 and d = kd asr 2 in
      let v = match kind with 0 -> if x = 0 then ninf else inf | 1 -> nv.(x) | _ -> value x in
      let v = shift v d in
      let v = if d < 0 then (if up c then max (1 - d) v else max (-d) v) else v in
      acc := pick !acc v
    done;
    nv.(n) <- (if guard > 0 && l <= guard then ninf else !acc)
  done;
  nv.(nodes - 1)

(* The solver's state lives in a directory of files:
   - dig: the bases' digests, sorted; a base's index is its rank here. A base
     is a turn-start key with A's life (key byte 1) zeroed;
   - keys: per base, a 32-byte record: key length, packed key, padding;
   - vals: per position, its value (int32). Position i is base i mod nb at
     A-life level slot i / nb: levels 1 to nl, A's life at the start, or
     just 20 when A's life is pinned (nl = 1). Every base is a position at every level:
     turns only differ across levels in whether combat damage kills A, so
     the levels share the bases' compiled turns;
   - hist (with ranks): (key, value) pairs of int64, key = index lsl 24 lor
     round, sorted: the rounds at which each value changed;
   - meta (saved tables): the header.
   The arrays are memory-mapped. Anonymous memory is bounded by the sort
   buffer ([mem] bytes, TCB_MEM megabytes) plus a few words per position of
   the A-life level being solved. *)
let rsize = 32

type solver = {
  dir : string;
  n : int;   (* positions *)
  nb : int;  (* bases *)
  nl : int;  (* levels; 0 for a legacy table, whose positions are its bases *)
  pinned : bool;  (* A's life pinned at 20: one level *)
  dig : (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array1.t;
  keys : (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t;
  vals : (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t;
  mutable hist : (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array1.t option;
}

let mem = (match Sys.getenv_opt "TCB_MEM" with Some m -> int_of_string m | None -> 256) * 1_000_000

let path sv name = Filename.concat sv.dir name
let base_key_at sv b = let o = b * rsize in String.init (Char.code sv.keys.{o}) (fun j -> sv.keys.{o + 1 + j})
let with_life k l = let b = Bytes.of_string k in Bytes.set b 1 (Char.chr l); Bytes.to_string b
let base_of k = with_life k 0
let life_of_slot sv k = if sv.pinned then 20 else k + 1

(* The key of position [i]. *)
let key_at sv i =
  if sv.nl = 0 then base_key_at sv i else with_life (base_key_at sv (i mod sv.nb)) (life_of_slot sv (i / sv.nb))
let get sv i = of32 (Int32.to_int sv.vals.{i})
let set sv i v = sv.vals.{i} <- Int32.of_int (to32 v)

(* Index of the position with digest [d]. Digests are uniform, so
   interpolation search needs only a few probes. *)
let find sv d =
  let dg i = Int64.to_int (Bigarray.Array1.unsafe_get sv.dig i) in
  let rec bin a b =
    if a > b then raise Not_found
    else
      let m = (a + b) / 2 in
      let x = dg m in
      if x = d then m else if x < d then bin (m + 1) b else bin a (m - 1)
  in
  let rec interp a b steps =
    if b - a < 64 || steps = 0 then bin a b
    else
      let lo = dg a and hi = dg b in
      if d < lo || d > hi then raise Not_found
      else
        let f = (float_of_int d -. float_of_int lo) /. (float_of_int hi -. float_of_int lo) in
        let m = max a (min b (a + int_of_float (f *. float_of_int (b - a)))) in
        let x = dg m in
        if x = d then m else if x < d then interp (m + 1) b (steps - 1) else interp a (m - 1) (steps - 1)
  in
  interp 0 (sv.nb - 1) 8

(* Index of the position with key [k]. *)
let id sv k =
  if sv.nl = 0 then find sv (Tsearch.digest_key k)
  else
    let slot = if sv.pinned then 0 else Char.code k.[1] - 1 in
    (slot * sv.nb) + find sv (Tsearch.digest_key (base_of k))

(* A warm start for [win]: a table solved for the same check, with caps no
   larger than [c]'s. Raising a cap only removes pessimism: a larger
   protagonist cap adds options (Thopter monotonicity), and a larger opponent
   cap moves the huge and too-many losses further out, while a Walker that
   was huge before behaves either as its representative did or so that the
   old abstraction counted a loss. So the old value of a position, read
   through the old abstraction (clamped to the old caps), is still achieved
   under the new one: it is never better than the new fixed point. *)
type warm = { wc : cfg; wsv : solver }

let warm_value c w s =
  if too_many w.wc s then lose c
  else
    match id w.wsv (key_gen c.full_a (clamp w.wc s)) with
    | i -> norm c (get w.wsv i)
    | exception Not_found -> lose c

(* Map the arrays of a solver directory with [nb] bases and [nl] levels. *)
let open_dir ?(pinned = false) dir ~nb ~nl ~write =
  let n = if nl = 0 then nb else nl * nb in
  let hist =
    let p = Filename.concat dir "hist" in
    if Sys.file_exists p && Disk.count p 16 > 0 then Some (Disk.map Bigarray.int64 p (2 * Disk.count p 16) ~write:false)
    else None
  in
  { dir; n; nb; nl; pinned;
    dig = Disk.map Bigarray.int64 (Filename.concat dir "dig") nb ~write:false;
    keys = Disk.map Bigarray.char (Filename.concat dir "keys") (nb * rsize) ~write:false;
    vals = Disk.map Bigarray.int32 (Filename.concat dir "vals") n ~write;
    hist }

(* The bases reachable from [s0]'s, by breadth-first search with duplicate
   detection on disk. Each layer's successors are sorted in runs, merged, and
   filtered against the sorted file of bases seen so far. A record is a
   digest and a key record. A base is expanded with A on 20 life: at lower
   life A can only die sooner, so that gives every successor base of every
   level. *)
let reach c s0 dir =
  (try Unix.mkdir dir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  let p = Filename.concat dir in
  let size = 8 + rsize in
  let record = Bytes.create size in
  let fill k =
    assert (String.length k < rsize);
    Bytes.fill record 0 size '\000';
    Disk.set_key record 0 (Tsearch.digest_key k);
    Bytes.set record 8 (Char.chr (String.length k));
    Bytes.blit_string k 0 record 9 (String.length k)
  in
  let layer i = p (Printf.sprintf "layer-%d" i) in
  let k0 = base_of (key_gen c.full_a s0) in
  fill k0;
  let oc = Disk.out (layer 0) in output oc record 0 size; close_out oc;
  let oc = Disk.out (p "visited") in Disk.output_key oc (Tsearch.digest_key k0); close_out oc;
  let depth = ref 0 and total = ref 1 and fresh = ref 1 and t0 = Unix.gettimeofday () in
  while !fresh > 0 do
    (* expand the layer: each worker sorts its slice's successors into runs *)
    let cnt = Disk.count (layer !depth) size in
    let w = Par.workers cnt 16 in
    ignore (Par.map ~dir w (fun j ->
        let lo, hi = Par.chunk cnt w j in
        let runs = Disk.runs ~base:(p (Printf.sprintf "run-%d" j)) ~size ~mem:(mem / Par.jobs) in
        let seen = Hashtbl.create 64 in
        Disk.iter_range (layer !depth) size lo hi (fun b ->
            let k = with_life (Bytes.sub_string b 9 (Char.code (Bytes.get b 8))) 20 in
            let s = of_key k in
            assert (key_gen c.full_a s = k);  (* the packing round-trips *)
            Hashtbl.reset seen;
            ignore (eval_turn c (fun k' ->
                let k' = base_of k' in
                if not (Hashtbl.mem seen k') then begin Hashtbl.add seen k' (); fill k'; Disk.push runs record 0 end;
                0) s));
        Disk.flush runs;
        0));
    let runs =
      List.map p (List.filter (fun f -> String.length f > 4 && String.sub f 0 4 = "run-") (Array.to_list (Sys.readdir dir)))
    in
    (* the new positions: successors not seen before *)
    let seen_r = Disk.reader (p "visited") 8 in
    let vo = Disk.out (p "visited.new") and fo = Disk.out (layer (!depth + 1)) in
    fresh := 0;
    Disk.merge runs size (fun b ->
        let k = Disk.key b 0 in
        while (not seen_r.Disk.eof) && seen_r.Disk.k < k do Disk.output_key vo seen_r.Disk.k; Disk.advance seen_r done;
        if seen_r.Disk.eof || seen_r.Disk.k > k then begin
          Disk.output_key vo k; output fo b 0 size; incr fresh
        end);
    while not seen_r.Disk.eof do Disk.output_key vo seen_r.Disk.k; Disk.advance seen_r done;
    close_out vo; close_out fo;
    List.iter Disk.remove runs;
    Sys.rename (p "visited.new") (p "visited");
    incr depth;
    total := !total + !fresh;
    Printf.printf "  reach: layer %d, %d expanded, %d found (%.1fs)\n%!" !depth cnt !total (Unix.gettimeofday () -. t0)
  done;
  (* all layers, merged in digest order: the key records *)
  let layers = List.init (!depth + 1) layer in
  let ko = Disk.out (p "keys") in
  let rank = ref 0 in
  Disk.merge layers size (fun b -> output ko b 8 rsize; incr rank);
  close_out ko;
  List.iter Disk.remove layers;
  assert (!rank = !total);
  Sys.rename (p "visited") (p "dig");
  (* A never gains life: the levels run up to its life at the start *)
  let nb = !total and nl = if c.full_a then 1 else s0.sideA.life in
  let n = nl * nb in
  let fd = Unix.openfile (p "vals") [ Unix.O_RDWR; Unix.O_CREAT; Unix.O_TRUNC ] 0o644 in
  Unix.ftruncate fd (4 * n); Unix.close fd;
  Disk.remove (p "hist");
  Printf.printf "  reach: %d layers\n%!" !depth;
  open_dir ~pinned:c.full_a dir ~nb ~nl ~write:true

let read_int32s path =
  let ic = open_in_bin path in
  let n = in_channel_length ic / 4 in
  let b = Bytes.create (4 * n) in
  really_input ic b 0 (4 * n);
  close_in ic;
  Array.init n (fun i -> Int32.to_int (Bytes.get_int32_le b (4 * i)))

(* Iterate to the fixed point from [start] (optimistic for [safe],
   pessimistic for [win]). A never gains life, so positions are solved one
   A-life level at a time, lowest first: a level's turns only end in its own
   level or in lower, already solved ones.

   The bases are split into slices, one per worker. The workers compile
   their slices' turns to files once; then, level by level, they sweep them (alternately forwards and
   backwards) in rounds, all writing to the shared value map, until a round
   changes nothing. Reading values that other workers are changing is fine:
   the operator is monotone and the iteration starts at its bottom (or top),
   so every value read lies between the start and the fixed point, and
   this chaotic iteration reaches the same fixed point. With ranks the rounds
   are synchronous instead: each round's values are computed from the
   previous round's.

   With [warm] (least fixed points only), values start from the warm table
   instead, and a sweep only keeps a change for the better. The start lies
   on the pessimistic side of the fixed point, every update keeps it there,
   and when a round changes nothing each value is at least as good as one
   step from the others: from such a point the iteration from the true
   start can only arrive below it, so the two coincide. Rounds cannot be
   numbered from a warm start, so it excludes ranks. *)
let solve ?(ranks = false) ?warm c sv ~start =
  let n = sv.n in
  (match warm with
   | None -> for i = 0 to n - 1 do set sv i start done
   | Some w ->
     if ranks then invalid_arg "solve: a warm start has no ranks";
     let t0 = Unix.gettimeofday () in
     let nw = Par.workers n 4096 in
     let good = Par.map ~dir:sv.dir nw (fun k ->
         let lo, hi = Par.chunk n nw k in
         let good = ref 0 in
         for i = lo to hi - 1 do
           let v = warm_value c w (of_key (key_at sv i)) in
           set sv i v;
           if v <> lose c then incr good
         done;
         !good) in
     Printf.printf "  warm start: %d of %d positions not lost (%.1fs)\n%!" (Array.fold_left ( + ) 0 good) n
       (Unix.gettimeofday () -. t0));
  (* Updates keep only changes in the iteration's direction: a no-op from
     the true start, needed from a warm or lower-level start. *)
  let win = start = lose c in
  let keep = if win then best c else worst c in
  (* The value one level down bounds a position's value (more life is never
     worse for A, in the abstraction as in the game). It lies on the far side
     of the fixed point when the protagonist's win is sought for B or its
     safety for A: a position that reaches it is final and is skipped.
     Otherwise it is a closer start than [start]. The extreme value is the
     far bound at the lowest level. TCB_NOBOUND=1 disables both, for
     testing. *)
  let bounds = Sys.getenv_opt "TCB_NOBOUND" <> Some "1" in
  let lower_is_far = win = up c in
  let extreme = if win then (if up c then 1 else inf) else if up c then inf else ninf in
  let id = id sv in
  let nb = sv.nb in
  let hist = if ranks then Some (Disk.runs ~base:(path sv "histrun") ~size:16 ~mem) else None in
  let hrec = Bytes.create 16 in
  let evals = ref 0 and t0 = Unix.gettimeofday () in
  let prog_file k = path sv (Printf.sprintf "prog-%d" k) and index_file k = path sv (Printf.sprintf "index-%d" k) in
  (* compile every base's turn once, for all levels: per slice, a program
     file and an index of (nodes, words). A turn start becomes base lsl 5
     lor the damage A took on the way. *)
  let w = Par.workers nb 64 in
  let tgt s =
    let u = sent - s.sideA.life in
    assert (u >= 0);
    (* damage of 20 or more kills A at every level: exploration (with A on
       20) never reached these turn starts, and they are never read, since
       the guard decides; they get a placeholder that reads as dead *)
    if u >= 20 then 31
    else
      let b = find sv (Tsearch.digest_key (base_of (key_gen c.full_a s))) in
      assert (b < 1 lsl 26);
      (b lsl 5) lor u
  in
  let words =
    Par.map ~dir:sv.dir w (fun k ->
        let lo, hi = Par.chunk nb w k in
        let po = Disk.out (prog_file k) and io = Disk.out (index_file k) in
        let words = ref 0 in
        for j = lo to hi - 1 do
          let prog, nn = compile c tgt (of_key (with_life (base_key_at sv j) sent)) in
          let len = Bigarray.Array1.dim prog in
          let b = Bytes.create (4 * len) in
          for x = 0 to len - 1 do Bytes.set_int32_le b (4 * x) prog.{x} done;
          output_bytes po b;
          Disk.output_int32 io nn;
          Disk.output_int32 io len;
          words := !words + len
        done;
        close_out po;
        close_out io;
        !words)
  in
  let progs = Array.mapi (fun k ws -> Disk.map Bigarray.int32 (prog_file k) (max 1 ws) ~write:false) words in
  let offs = Array.make nb 0 and nodes = Array.make nb 0 and part = Array.make nb 0 in
  for k = 0 to w - 1 do
    let lo, hi = Par.chunk nb w k in
    let idx = read_int32s (index_file k) in
    let off = ref 0 in
    for j = lo to hi - 1 do
      part.(j) <- k;
      nodes.(j) <- idx.(2 * (j - lo));
      offs.(j) <- !off;
      off := !off + idx.((2 * (j - lo)) + 1)
    done
  done;
  Printf.printf "  compiled %d turns, %d program words (%.1fs)\n%!" nb (Array.fold_left ( + ) 0 words)
    (Unix.gettimeofday () -. t0);
  (* the levels, lowest first *)
  for slot = 0 to sv.nl - 1 do
    let l = life_of_slot sv slot in
    let first = slot * nb in
    let value x =
      let b = x lsr 5 and u = x land 31 in
      if sv.pinned then get sv b
      else if l - u < 1 then lose c  (* A is dead before this: never read, the guard decides *)
      else get sv (((l - u - 1) * nb) + b)
    in
    let eval j = norm c (run c l value progs.(part.(j)) offs.(j) nodes.(j)) in
    let below = bounds && slot > 0 && not sv.pinned in
    let far =
      if below && lower_is_far then fun j -> get sv (first - nb + j)
      else if bounds then fun _ -> extreme
      else fun _ -> max_int in
    let final j = get sv (first + j) = far j in
    if below && (not lower_is_far) && hist = None then
      for j = 0 to nb - 1 do set sv (first + j) (keep (get sv (first + j)) (get sv (first - nb + j))) done;
    (match hist with
     | Some h ->
       (* synchronous rounds, so each value change gets a round number *)
       let nv_path = path sv "next" in
       let fd = Unix.openfile nv_path [ Unix.O_RDWR; Unix.O_CREAT; Unix.O_TRUNC ] 0o644 in
       Unix.ftruncate fd (4 * nb); Unix.close fd;
       let nv = Disk.map Bigarray.int32 nv_path (max 1 nb) ~write:true in
       let round = ref 0 and changed = ref true in
       while !changed do
         incr round;
         assert (!round < 1 lsl 24);
         changed := false;
         Par.map ~dir:sv.dir w (fun k ->
             let lo, hi = Par.chunk nb w k in
             let ev = ref 0 in
             for j = lo to hi - 1 do
               nv.{j} <- Int32.of_int (to32 (if final j then get sv (first + j) else (incr ev; eval j)))
             done;
             !ev)
         |> Array.iter (fun e -> evals := !evals + e);
         for j = 0 to nb - 1 do
           let i = first + j and v = of32 (Int32.to_int nv.{j}) in
           if v <> get sv i then begin
             changed := true;
             Disk.set_key hrec 0 ((i lsl 24) lor !round);
             Bytes.set_int64_le hrec 8 (Int64.of_int (to32 v));
             Disk.push h hrec 0;
             set sv i v
           end
         done
       done;
       Disk.remove nv_path
     | None -> ());
    let changed = ref true and sweeps = ref 0 in
    while !changed do
      incr sweeps;
      let forward = !sweeps land 1 = 1 in
      let r = Par.map ~dir:sv.dir w (fun k ->
          let lo, hi = Par.chunk nb w k in
          let changed = ref 0 and ev = ref 0 in
          for x = lo to hi - 1 do
            let j = if forward then x else lo + hi - 1 - x in
            if not (final j) then begin
              incr ev;
              let v = keep (get sv (first + j)) (eval j) in
              if v <> get sv (first + j) then begin set sv (first + j) v; incr changed end
            end
          done;
          (!ev lsl 31) lor !changed)
      in
      Array.iter (fun x -> evals := !evals + (x lsr 31)) r;
      changed := Array.exists (fun x -> x land 0x7fffffff > 0) r
    done;
    let good = ref 0 in
    for j = 0 to nb - 1 do if get sv (first + j) <> lose c then incr good done;
    Printf.printf "  A life %d: %d positions (%d not lost for the protagonist), %d sweeps, %d evaluations so far (%.1fs)\n%!"
      l nb !good !sweeps !evals (Unix.gettimeofday () -. t0)
  done;
  Gc.full_major ();  (* unmap the programs *)
  for k = 0 to w - 1 do Disk.remove (prog_file k); Disk.remove (index_file k) done;
  (match hist with
   | Some h ->
     Disk.sort_to h (path sv "hist");
     let k = Disk.count (path sv "hist") 16 in
     sv.hist <- (if k > 0 then Some (Disk.map Bigarray.int64 (path sv "hist") (2 * k) ~write:false) else None)
   | None -> ());
  (* spot check: the compiled turns agree with direct evaluation through the model *)
  let lookup k = get sv (id k) in
  let w = Par.workers (n / 500) 16 in
  let bad = Array.fold_left ( + ) 0 (Par.map ~dir:sv.dir w (fun k ->
      let lo, hi = Par.chunk n w k in
      let bad = ref 0 in
      for i = lo to hi - 1 do
        if i mod 500 = 0 && norm c (eval_turn c lookup (of_key (key_at sv i))) <> get sv i then incr bad
      done;
      !bad)) in
  if bad > 0 then Printf.printf "  SPOT CHECK FAILED at %d positions\n%!" bad
  else Printf.printf "  spot check passed\n%!"

let value c sv s = get sv (id sv (key_gen c.full_a s))

let safe c s0 dir =
  let sv = reach c s0 dir in
  Printf.printf "%d positions (%d bases at %d levels)\n%!" sv.n sv.nb sv.nl;
  solve c sv ~start:(if up c then 1 else inf);
  sv

let win ?ranks ?warm c s0 dir =
  let sv = reach c s0 dir in
  Printf.printf "%d positions (%d bases at %d levels)\n%!" sv.n sv.nb sv.nl;
  solve ?ranks ?warm c sv ~start:(lose c);
  sv

let show c v =
  if up c then (if v >= inf then "never" else Printf.sprintf "B life >= %d" v)
  else if v <= ninf then "never" else if v >= inf then "any B life" else Printf.sprintf "B life <= %d" v

(* The (round, value) changes of position [i], in round order. *)
let history sv i =
  match sv.hist with
  | None -> []
  | Some h ->
    let k j = Int64.to_int h.{2 * j} in
    let cnt = Bigarray.Array1.dim h / 2 in
    (* the first record with key >= i lsl 24 *)
    let rec lower a b = if a >= b then a else let m = (a + b) / 2 in if k m < i lsl 24 then lower (m + 1) b else lower a m in
    let rec collect j acc =
      if j < cnt && k j lsr 24 = i then collect (j + 1) ((k j land 0xffffff, of32 (Int64.to_int h.{(2 * j) + 1})) :: acc)
      else List.rev acc
    in
    collect (lower 0 cnt) []

let has_ranks sv = sv.hist <> None

(* A line of play from [s0] with B on [life], following the solved values
   (needs ranks). The protagonist plays a move that keeps its value as of
   the previous round of the current position's level (so the line makes
   progress); the opponent plays a worst move for it. Without ranks the
   protagonist only keeps its current value, so the line may go round in
   circles, but it still shows the plan. *)
let line c sv s0 life turns =
  let id = id sv in
  let level k = (of_key k).sideA.life in
  let at_round i r =
    match List.find_opt (fun (r', _) -> r' <= r) (List.rev (history sv i)) with Some (_, v) -> v | None -> lose c
  in
  let at_big s = { s with sideB = { s.sideB with life = big } } in
  let rec walk s t =
    match winner s with
    | Some w -> Printf.printf "*** %s wins\n" (Show.player w)
    | None ->
      if Search.is_turn_start s then begin
        let k = key_gen c.full_a s in
        let i = id k in
        let l = s.sideB.life in
        (* the first round at which this position was won with this life *)
        let r = match List.find_opt (fun (_, v) -> v <= l) (history sv i) with Some (r', _) -> r' | None -> max_int in
        Printf.printf "--- turn %d (round %d of A-life level %d) ---\n%s\n" t r (level k) (Show.state s);
        let lk k' = let j = id k' in if level k' < level k || not (has_ranks sv) then get sv j else at_round j (r - 1) in
        if t < turns then go lk s (t + 1)
      end else go (fun k' -> get sv (id k')) s t
  and go lk s t =
    let scored = List.map (fun m ->
        let s' = clamp c (step s m) in
        let v = if huge_event c s m || too_many c s' then lose c else
            match winner s' with Some _ -> ninf | None ->
              let d = s'.sideB.life - s.sideB.life in
              let v = shift (eval_from c lk (at_big s') false) d in
              if d < 0 then max (1 - d) v else v in
        (m, s', v)) (moves_for c s) in
    let pick = if to_move s = c.prot then best c else worst c in
    let m, s', _ = List.fold_left (fun ((_, _, bv) as acc) ((_, _, v) as x) -> if pick v bv <> bv then x else acc)
        (List.hd scored) (List.tl scored) in
    if m <> Pass then Printf.printf "  %s: %s\n" (Show.player (to_move s)) (Show.move m);
    walk_in lk s' t
  and walk_in lk s t =
    match winner s with
    | Some _ -> walk s t
    | None -> if Search.is_turn_start s then walk s t else go lk s t
  in
  walk { s0 with sideB = { s0.sideB with life } } 0

(* Saved tables are solver directories with a meta file: a format line,
   then one key=value field per line. Format 3 has bases and levels; format
   2 (legacy) has one key per position. *)
let save_meta sv header =
  let oc = open_out (path sv "meta") in
  output_string oc "TCBFIX 3\n";
  List.iter (fun (k, v) -> Printf.fprintf oc "%s=%s\n" k v)
    (("n", string_of_int sv.n) :: ("nb", string_of_int sv.nb) :: ("nl", string_of_int sv.nl) :: header);
  close_out oc

(* Delete a solver directory that is not kept. *)
let remove sv =
  Array.iter (fun f -> Sys.remove (path sv f)) (Sys.readdir sv.dir);
  Sys.rmdir sv.dir

let read_meta dir =
  let ic = open_in (Filename.concat dir "meta") in
  (match input_line ic with "TCBFIX 2" | "TCBFIX 3" -> () | _ -> failwith (dir ^ ": not a solved table"));
  let rec fields acc =
    match input_line ic with
    | l -> (match String.index_opt l '=' with
        | Some i -> fields ((String.sub l 0 i, String.sub l (i + 1) (String.length l - i - 1)) :: acc)
        | None -> fields acc)
    | exception End_of_file -> close_in ic; List.rev acc
  in
  fields []

(* Convert a table in the old single-file format ("TCBFIX 1") into a
   solver directory. *)
let import_v1 file dir =
  let ic = open_in_bin file in
  if input_line ic <> "TCBFIX 1" then failwith (file ^ ": not a solved table");
  let header = input_line ic in
  let n = input_binary_int ic in
  let ranks = input_byte ic = 1 in
  let recs = Array.init n (fun _ ->
      let k = really_input_string ic (input_byte ic) in
      let v = input_binary_int ic in
      let h = if ranks then List.init (input_binary_int ic) (fun _ -> let r = input_binary_int ic in (r, input_binary_int ic)) else [] in
      (Tsearch.digest_key k, k, v, List.rev h)) in
  close_in ic;
  Array.sort (fun (a, _, _, _) (b, _, _, _) -> Int.compare a b) recs;
  (try Unix.mkdir dir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  let p = Filename.concat dir in
  let dg = Disk.out (p "dig") and ko = Disk.out (p "keys") and vo = Disk.out (p "vals") and ho = Disk.out (p "hist") in
  let kb = Bytes.create rsize in
  Array.iteri (fun i (d, k, v, h) ->
      Disk.output_key dg d;
      Bytes.fill kb 0 rsize '\000';
      Bytes.set kb 0 (Char.chr (String.length k));
      Bytes.blit_string k 0 kb 1 (String.length k);
      output_bytes ko kb;
      Disk.output_int32 vo v;  (* already in the int32 encoding *)
      List.iter (fun (r, v) -> Disk.output_key ho ((i lsl 24) lor r); Disk.output_key ho v) h)
    recs;
  List.iter close_out [ dg; ko; vo; ho ];
  let oc = open_out (p "meta") in
  output_string oc "TCBFIX 2\n";
  Printf.fprintf oc "n=%d\n" n;
  List.iter (fun f -> output_string oc (f ^ "\n")) (String.split_on_char ' ' header);
  close_out oc

(* Open a saved table: a directory, or an old-format file (converted once,
   into FILE.d). *)
let load file =
  let dir = if Sys.is_directory file then file else file ^ ".d" in
  if not (Sys.file_exists (Filename.concat dir "meta")) then import_v1 file dir;
  let header = read_meta dir in
  let gi k = int_of_string (List.assoc k header) in
  let sv = match List.assoc_opt "nl" header with
    | Some _ -> open_dir ~pinned:(List.assoc_opt "fulla" header = Some "1") dir ~nb:(gi "nb") ~nl:(gi "nl") ~write:false
    | None -> open_dir dir ~nb:(gi "n") ~nl:0 ~write:false in
  (header, sv)

let hex s = String.concat "" (List.map (fun c -> Printf.sprintf "%02x" (Char.code c)) (List.of_seq (String.to_seq s)))
let unhex h = String.init (String.length h / 2) (fun i -> Char.chr (int_of_string ("0x" ^ String.sub h (2 * i) 2)))
