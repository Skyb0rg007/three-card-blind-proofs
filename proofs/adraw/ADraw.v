(* Generated; do not edit. *)
From Stdlib Require Import Uint63 PArray List Arith ZArith.
From TCB.Proofs Require Import Packed PackedA.
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
Require Chunk016.
Require Chunk017.
Require Chunk018.
Require Chunk019.
Require Chunk020.
Require Chunk021.
Require Chunk022.
Require Chunk023.

Definition bounds : list int := [0; 22719; 32883; 67120; 89459; 108806; 136890; 153906; 162228; 173856; 193375; 203970; 222818; 240940; 272659; 320536; 362409; 390466; 403333; 435609; 459639; 483194; 504385; 542959; 581561]%uint63.

Theorem a_first_a_safe_proved : a_first_a_safe.
Proof.
  apply (table_safe_a K Hb ott tt fuel C1 C2 CV N bounds (20)%Z (0)%Z).
  - exact (conj Chunk000.chunk (conj Chunk001.chunk (conj Chunk002.chunk (conj Chunk003.chunk (conj Chunk004.chunk (conj Chunk005.chunk (conj Chunk006.chunk (conj Chunk007.chunk (conj Chunk008.chunk (conj Chunk009.chunk (conj Chunk010.chunk (conj Chunk011.chunk (conj Chunk012.chunk (conj Chunk013.chunk (conj Chunk014.chunk (conj Chunk015.chunk (conj Chunk016.chunk (conj Chunk017.chunk (conj Chunk018.chunk (conj Chunk019.chunk (conj Chunk020.chunk (conj Chunk021.chunk (conj Chunk022.chunk (conj Chunk023.chunk (I))))))))))))))))))))))))).
  - reflexivity.
  - vm_compute. reflexivity.
  - apply Nat.ltb_lt. reflexivity.
  - apply Nat.leb_le. reflexivity.
  - vm_compute. reflexivity.
  - apply Z.leb_le. reflexivity.
Qed.

Print Assumptions a_first_a_safe_proved.
