From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt ZArith.
From TCB.Spec Require Import Model.
From TCB.Proofs Require Import Checker WinCert.
From TCB.Proofs Require CheckerA MemoA MemoB Packed.
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
Definition a_check_m := MemoA.check_m.
Definition check_mb := MemoB.check_mb.
Definition check_mw := MemoB.check_mw.

(* MemoA's memo orders its hashes with the primitive integers' [ltb]: OCaml
   ints have the same 63 bits, compared unsigned. *)
Extract Inlined Constant PrimInt63.int => "int".
Extract Inlined Constant PrimInt63.ltb => "(fun x y -> (x lxor Stdlib.min_int) < (y lxor Stdlib.min_int))".

(* The hash and the move hints of the memos (Packed.shash, Packed.hint_of),
   with OCaml's 63-bit ints for the primitive ones: the same bits, with
   unsigned shifts and remainders as the kernel computes them. *)
Extract Inlined Constant PrimInt63.add => "(+)".
Extract Inlined Constant PrimInt63.sub => "(-)".
Extract Inlined Constant PrimInt63.mul => "( * )".
Extract Inlined Constant PrimInt63.land => "(land)".
Extract Inlined Constant PrimInt63.lor => "(lor)".
Extract Inlined Constant PrimInt63.eqb => "(=)".
Extract Inlined Constant PrimInt63.lsl => "(fun x y -> if y < 0 || y >= 63 then 0 else x lsl y)".
Extract Inlined Constant PrimInt63.lsr => "(fun x y -> if y < 0 || y >= 63 then 0 else x lsr y)".
Extract Inlined Constant PrimInt63.mod =>
  "(fun x y -> if y = 0 then x else Int64.to_int (Int64.rem (Int64.logand (Int64.of_int x) 0x7FFFFFFFFFFFFFFFL) (Int64.logand (Int64.of_int y) 0x7FFFFFFFFFFFFFFFL)))".

Definition shash := Packed.shash.
Definition hint_key := Packed.hint_key.
Definition hint_slot := Packed.hint_slot.
Definition hint_dec := Packed.hint_dec.
Definition hfirst := MemoA.hfirst.

Extraction "model.ml" init moves step to_move winner
  check_node check_win key entry is_turn_start huge_event too_many
  a_check_node a_key a_entry a_stepA a_huge_event a_big_event a_too_many
  a_is_pump_big a_is_create a_is_hit a_has_big a_check_m check_mb check_mw
  shash hint_key hint_slot hint_dec hfirst.
