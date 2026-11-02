From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt ZArith.
From TCB.Spec Require Import Model.
From TCB.Proofs Require Import Checker WinCert.
From TCB.Proofs Require CheckerA.
Set Warnings "-extraction-default-directory".
Extraction Language OCaml.
(* keeps Model's [opp] from being renamed *)
Extract Inlined Constant BinInt.Z.opp => "(~-)".

(* CheckerA reuses Checker's names; these aliases give its functions stable
   names in the extracted file. *)
Definition a_check_node := CheckerA.check_node.
Definition a_key := CheckerA.key.
Definition a_entry := CheckerA.entry.
Definition a_stepA := CheckerA.stepA.
Definition a_huge_event := CheckerA.huge_event.
Definition a_big_event := CheckerA.big_event.
Definition a_too_many := CheckerA.too_many.
Definition a_is_pump_big := CheckerA.is_pump_big.
Definition a_is_create := CheckerA.is_create.
Definition a_is_hit := CheckerA.is_hit.
Definition a_has_big := CheckerA.has_big.

Extraction "model.ml" init moves step to_move winner
  check_node check_win key entry is_turn_start huge_event too_many
  a_check_node a_key a_entry a_stepA a_huge_event a_big_event a_too_many
  a_is_pump_big a_is_create a_is_hit a_has_big.
