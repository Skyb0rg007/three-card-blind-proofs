(* Which damage rules the solver runs: pre-Foundations (authoritative) or
   post-Foundations (comparison mode, spec/RULES.md §3.6). *)
let modern = ref false
let moves s = Model.moves_gen !modern s
let step s m = Model.step_gen !modern s m
