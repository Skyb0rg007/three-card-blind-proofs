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

Definition bounds : list int := [0; 48190; 81096; 184371; 219890; 261029; 398759; 429109; 450970; 472004; 500778; 618937; 687104; 721053; 754761; 817505; 936099]%uint63.

Theorem b_first_b_wins_proved : b_first_b_wins.
Proof.
  apply (table_wins H ott tt fuel K1 K2 RV bounds 594 17).
  - exact (conj Chunk000.chunk (conj Chunk001.chunk (conj Chunk002.chunk (conj Chunk003.chunk (conj Chunk004.chunk (conj Chunk005.chunk (conj Chunk006.chunk (conj Chunk007.chunk (conj Chunk008.chunk (conj Chunk009.chunk (conj Chunk010.chunk (conj Chunk011.chunk (conj Chunk012.chunk (conj Chunk013.chunk (conj Chunk014.chunk (conj Chunk015.chunk (I))))))))))))))))).
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply Nat.leb_le. reflexivity.
Qed.

Print Assumptions b_first_b_wins_proved.
