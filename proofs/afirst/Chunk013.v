(* Generated; do not edit. *)
From Stdlib Require Import Uint63 PArray List Arith.
From TCB.Proofs Require Import Packed.
Require Import Data.
Lemma chunk : exists f, range_ok (entry_ok H ott tt fuel K1 K2 V) f 242878 253742 = true.
Proof. exists 10864. vm_cast_no_check (eq_refl true). Qed.
