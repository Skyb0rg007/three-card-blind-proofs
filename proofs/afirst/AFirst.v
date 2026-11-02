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
Require Chunk016.
Require Chunk017.
Require Chunk018.
Require Chunk019.
Require Chunk020.
Require Chunk021.
Require Chunk022.
Require Chunk023.
Require Chunk024.
Require Chunk025.
Require Chunk026.
Require Chunk027.
Require Chunk028.
Require Chunk029.
Require Chunk030.
Require Chunk031.
Require Chunk032.
Require Chunk033.
Require Chunk034.
Require Chunk035.
Require Chunk036.
Require Chunk037.
Require Chunk038.
Require Chunk039.
Require Chunk040.
Require Chunk041.
Require Chunk042.
Require Chunk043.
Require Chunk044.
Require Chunk045.
Require Chunk046.
Require Chunk047.

Definition bounds : list int := [0; 22198; 34061; 44739; 54026; 63123; 72122; 80758; 115134; 158809; 178993; 200494; 221370; 242878; 253742; 276636; 298187; 319406; 340337; 351294; 372125; 392681; 498755; 649843; 694236; 723834; 751280; 779361; 805230; 860191; 946896; 1018447; 1090023; 1111518; 1131184; 1151172; 1171556; 1192264; 1212783; 1233698; 1255000; 1279902; 1306470; 1360782; 1414799; 1466984; 1513980; 1569363; 1626854]%uint63.

Theorem a_first_b_safe_proved : a_first_b_safe.
Proof.
  apply (table_safe H ott tt fuel K1 K2 V PA bounds 20).
  - exact (conj Chunk000.chunk (conj Chunk001.chunk (conj Chunk002.chunk (conj Chunk003.chunk (conj Chunk004.chunk (conj Chunk005.chunk (conj Chunk006.chunk (conj Chunk007.chunk (conj Chunk008.chunk (conj Chunk009.chunk (conj Chunk010.chunk (conj Chunk011.chunk (conj Chunk012.chunk (conj Chunk013.chunk (conj Chunk014.chunk (conj Chunk015.chunk (conj Chunk016.chunk (conj Chunk017.chunk (conj Chunk018.chunk (conj Chunk019.chunk (conj Chunk020.chunk (conj Chunk021.chunk (conj Chunk022.chunk (conj Chunk023.chunk (conj Chunk024.chunk (conj Chunk025.chunk (conj Chunk026.chunk (conj Chunk027.chunk (conj Chunk028.chunk (conj Chunk029.chunk (conj Chunk030.chunk (conj Chunk031.chunk (conj Chunk032.chunk (conj Chunk033.chunk (conj Chunk034.chunk (conj Chunk035.chunk (conj Chunk036.chunk (conj Chunk037.chunk (conj Chunk038.chunk (conj Chunk039.chunk (conj Chunk040.chunk (conj Chunk041.chunk (conj Chunk042.chunk (conj Chunk043.chunk (conj Chunk044.chunk (conj Chunk045.chunk (conj Chunk046.chunk (conj Chunk047.chunk (I))))))))))))))))))))))))))))))))))))))))))))))))).
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply Nat.leb_le. reflexivity.
Qed.

Print Assumptions a_first_b_safe_proved.
