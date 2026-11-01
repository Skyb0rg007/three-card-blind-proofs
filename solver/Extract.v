From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From TCB.Spec Require Import Model.
From TCB.Proofs Require Import Checker WinCert.
Set Warnings "-extraction-default-directory".
Extraction Language OCaml.
Extraction "model.ml" init moves step moves_gen step_gen to_move winner
  check_node check_win key entry is_turn_start huge_event too_many.
