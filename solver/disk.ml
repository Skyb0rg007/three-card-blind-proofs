(* Disk-backed storage for the fixed-point solver, so that memory stays
   bounded however many positions there are.

   - Files of fixed-size records sorted by an integer key, held in the
     first 8 bytes of each record. They are built with bounded memory:
     records are buffered, sorted and written as runs, and the runs are
     merged.
   - Memory-mapped arrays. Their pages are file-backed, so the kernel can
     drop them under memory pressure instead of swapping. *)

let key b off = Int64.to_int (Bytes.get_int64_le b off)
let set_key b off k = Bytes.set_int64_le b off (Int64.of_int k)

let out path = open_out_gen [ Open_wronly; Open_creat; Open_trunc; Open_binary ] 0o644 path

let b4 = Bytes.create 4
let output_int32 oc x = Bytes.set_int32_le b4 0 (Int32.of_int x); output_bytes oc b4

let b8 = Bytes.create 8
let output_key oc k = set_key b8 0 k; output_bytes oc b8

let remove path = if Sys.file_exists path then Sys.remove path

(* Records pushed in any order, kept as sorted runs on disk. Within a run,
   records with equal keys are kept once. *)
type runs = {
  size : int;
  cap : int;
  mutable buf : Bytes.t;  (* grows on demand up to [cap] records *)
  mutable ds : int array;
  mutable fill : int;
  mutable files : string list;
  base : string;
}

(* At most [mem] bytes of buffer, counting the sort's index arrays. *)
let runs ~base ~size ~mem =
  let cap = max 1024 (mem / (size + 16)) in
  let n0 = min cap 65536 in
  { size; cap; buf = Bytes.create (n0 * size); ds = Array.make n0 0; fill = 0; files = []; base }

let flush r =
  if r.fill > 0 then begin
    let idx = Array.init r.fill (fun i -> i) in
    Array.sort (fun a b -> Int.compare r.ds.(a) r.ds.(b)) idx;
    let path = Printf.sprintf "%s.%d" r.base (List.length r.files) in
    let oc = out path in
    Array.iteri (fun j i ->
        if j = 0 || r.ds.(i) <> r.ds.(idx.(j - 1)) then output oc r.buf (i * r.size) r.size)
      idx;
    close_out oc;
    r.files <- path :: r.files;
    r.fill <- 0
  end

let push r b off =
  if r.fill = Array.length r.ds then begin
    if r.fill = r.cap then flush r
    else begin
      let n = min r.cap (2 * r.fill) in
      let buf = Bytes.create (n * r.size) in
      Bytes.blit r.buf 0 buf 0 (r.fill * r.size);
      r.buf <- buf;
      r.ds <- Array.append r.ds (Array.make (n - r.fill) 0)
    end
  end;
  Bytes.blit b off r.buf (r.fill * r.size) r.size;
  r.ds.(r.fill) <- key b off;
  r.fill <- r.fill + 1

(* Sequential reading of a record file; [k] is the current record's key. *)
type reader = { ic : in_channel; rbuf : Bytes.t; mutable k : int; mutable eof : bool }

let advance r =
  match really_input r.ic r.rbuf 0 (Bytes.length r.rbuf) with
  | () -> r.k <- key r.rbuf 0
  | exception End_of_file -> r.eof <- true; close_in r.ic

let reader path size =
  let r = { ic = open_in_bin path; rbuf = Bytes.create size; k = 0; eof = false } in
  advance r;
  r

let iter path size f =
  let r = reader path size in
  while not r.eof do f r.rbuf; advance r done

(* Records [lo, hi) of a file. *)
let iter_range path size lo hi f =
  let ic = open_in_bin path in
  seek_in ic (lo * size);
  let b = Bytes.create size in
  for _ = lo to hi - 1 do really_input ic b 0 size; f b done;
  close_in ic

(* Merge sorted record files, calling [f] once per distinct key, in key
   order. Many files are merged in groups first. *)
let max_fan_in = 400

let rec merge files size f =
  if List.length files > max_fan_in then begin
    let rec groups acc cur n = function
      | [] -> List.rev (if cur = [] then acc else cur :: acc)
      | x :: rest -> if n = max_fan_in then groups (cur :: acc) [ x ] 1 rest else groups acc (x :: cur) (n + 1) rest
    in
    let merged =
      List.mapi (fun g fs ->
          let path = Printf.sprintf "%s.m%d" (List.hd fs) g in
          let oc = out path in
          merge fs size (fun b -> output oc b 0 size);
          close_out oc;
          path)
        (groups [] [] 0 files)
    in
    merge merged size f;
    List.iter remove merged
  end else begin
    let h = Array.of_list (List.filter_map (fun p -> let r = reader p size in if r.eof then None else Some r) files) in
    let n = ref (Array.length h) in
    let less i j = h.(i).k < h.(j).k in
    let rec down i =
      let l = (2 * i) + 1 and r = (2 * i) + 2 and m = ref i in
      if l < !n && less l !m then m := l;
      if r < !n && less r !m then m := r;
      if !m <> i then begin
        let t = h.(i) in
        h.(i) <- h.(!m); h.(!m) <- t; down !m
      end
    in
    for i = (!n / 2) - 1 downto 0 do down i done;
    let first = ref true and last = ref 0 in
    while !n > 0 do
      let r = h.(0) in
      if !first || r.k <> !last then begin first := false; last := r.k; f r.rbuf end;
      advance r;
      if r.eof then begin decr n; h.(0) <- h.(!n) end;
      down 0
    done
  end

(* Sort the records pushed to [r] into one file at [path]. *)
let sort_to r path =
  flush r;
  let oc = out path in
  merge r.files r.size (fun b -> output oc b 0 r.size);
  close_out oc;
  List.iter remove r.files;
  r.files <- []

(* Memory-mapped arrays of [n] elements over the file at [path]. *)
let map kind path n ~write =
  let fd = Unix.openfile path (if write then [ Unix.O_RDWR; Unix.O_CREAT ] else [ Unix.O_RDONLY ]) 0o644 in
  let a = Bigarray.array1_of_genarray (Unix.map_file fd kind Bigarray.c_layout write [| n |]) in
  Unix.close fd;
  a

(* The number of [size]-byte records in a file. *)
let count path size = (Unix.stat path).Unix.st_size / size
