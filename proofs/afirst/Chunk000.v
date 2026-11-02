(* Generated; do not edit. *)
From Stdlib Require Import Uint63 PArray List Arith.
From TCB.Proofs Require Import Packed.
Require Import Data.
Lemma chunk : exists f, range_ok (entry_ok H ott tt fuel K1 K2 V) f 0 45984 = true.
Proof. exists 45984. vm_cast_no_check (eq_refl true). Qed.
