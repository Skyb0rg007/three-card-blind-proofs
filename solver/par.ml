(* Parallelism by forking. OCaml 4.14 has one domain, so work is split
   among child processes. They share the solver's memory-mapped files (their
   writes to shared mappings are seen by everyone), write any other output
   to files of their own, and return one int each. *)

(* TCB_JOBS workers, by default one per processor. *)
let jobs =
  match Sys.getenv_opt "TCB_JOBS" with
  | Some j -> max 1 (int_of_string j)
  | None ->
    (try
       let ic = open_in "/proc/cpuinfo" in
       let n = ref 0 in
       (try
          while true do
            let l = input_line ic in
            if String.length l >= 9 && String.sub l 0 9 = "processor" then incr n
          done
        with End_of_file -> ());
       close_in ic;
       max 1 !n
     with Sys_error _ -> 1)

(* The [k]-th of [w] near-equal slices of [0, n). *)
let chunk n w k = (k * n / w, (k + 1) * n / w)

(* Run [f 0], ..., [f (w - 1)] in [w] child processes and return their
   results. [dir] holds the shared results file while they run. *)
let map ~dir w f =
  let path = Filename.concat dir (Printf.sprintf "par-%d" (Unix.getpid ())) in
  let fd = Unix.openfile path [ Unix.O_RDWR; Unix.O_CREAT; Unix.O_TRUNC ] 0o644 in
  Unix.ftruncate fd (8 * w);
  let res = Bigarray.array1_of_genarray (Unix.map_file fd Bigarray.int64 Bigarray.c_layout true [| w |]) in
  Unix.close fd;
  flush_all ();
  let pids =
    List.init w (fun k ->
        match Unix.fork () with
        | 0 ->
          (try
             res.{k} <- Int64.of_int (f k);
             flush_all ();
             Unix._exit 0
           with e ->
             prerr_endline ("worker " ^ string_of_int k ^ ": " ^ Printexc.to_string e);
             flush_all ();
             Unix._exit 2)
        | pid -> pid)
  in
  let failed = List.filter (fun pid -> snd (Unix.waitpid [] pid) <> Unix.WEXITED 0) pids in
  let r = Array.init w (fun k -> Int64.to_int res.{k}) in
  Sys.remove path;
  if failed <> [] then failwith (Printf.sprintf "%d of %d workers failed" (List.length failed) w);
  r

(* At most [jobs] workers, and none with fewer than [min_each] items. *)
let workers n min_each = max 1 (min jobs (n / max 1 min_each))
