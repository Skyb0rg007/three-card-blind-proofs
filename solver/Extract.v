From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From TCB Require Import Model.
Set Warnings "-extraction-default-directory".
Extraction Language OCaml.
Extraction "model.ml" init moves step moves_gen step_gen to_move winner.
