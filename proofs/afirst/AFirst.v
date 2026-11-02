(* Generated; do not edit. *)
From Stdlib Require Import Uint63 PArray List Arith.
From TCB.Proofs Require Import Packed.
From TCB.Spec Require Import Model Claims.
Require Import Data.
Import ListNotations.
Require Chunk000.
Require Chunk001.
Require Chunk002.
Require Chunk003.

Definition bounds : list int := [0; 45984; 152957; 189361; 270340]%uint63.

Theorem a_first_b_safe_proved : a_first_b_safe.
Proof.
  apply (table_safe H ott tt fuel K1 K2 V PA bounds 20).
  - exact (conj Chunk000.chunk (conj Chunk001.chunk (conj Chunk002.chunk (conj Chunk003.chunk (I))))).
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply Nat.leb_le. reflexivity.
Qed.

Print Assumptions a_first_b_safe_proved.
