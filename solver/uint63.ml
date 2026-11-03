(* What the extracted code needs of the kernel's Uint63: its literals are
   OCaml ints with the same 63 bits (solver/Extract.v). *)
let of_int (x : int) : int = x
