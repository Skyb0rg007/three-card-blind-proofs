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
Require Chunk004.
Require Chunk005.
Require Chunk006.
Require Chunk007.
Require Chunk008.
Require Chunk009.
Require Chunk010.
Require Chunk011.
Require Chunk012.
Require Chunk013.
Require Chunk014.
Require Chunk015.

Definition bounds : list int := [0; 45504; 76552; 117756; 142797; 171459; 201172; 227992; 261422; 288524; 319257; 353533; 398525; 430692; 480171; 515974; 573869]%uint63.

Theorem b_first_b_wins_proved : b_first_b_wins.
Proof.
  apply (table_wins H ott tt fuel K1 K2 RV bounds 331 17).
  - exact (conj Chunk000.chunk (conj Chunk001.chunk (conj Chunk002.chunk (conj Chunk003.chunk (conj Chunk004.chunk (conj Chunk005.chunk (conj Chunk006.chunk (conj Chunk007.chunk (conj Chunk008.chunk (conj Chunk009.chunk (conj Chunk010.chunk (conj Chunk011.chunk (conj Chunk012.chunk (conj Chunk013.chunk (conj Chunk014.chunk (conj Chunk015.chunk (I))))))))))))))))).
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply Nat.leb_le. reflexivity.
Qed.

Print Assumptions b_first_b_wins_proved.
