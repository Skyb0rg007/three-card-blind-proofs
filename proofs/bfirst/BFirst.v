(* Generated; do not edit. *)
From Stdlib Require Import Uint63 PArray List Arith.
From TCB.Proofs Require Import Packed.
From TCB.Spec Require Import Claims.
From TCB.Spec Require Import Model.
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

Definition bounds : list int := [0; 31502; 63004; 94506; 126008; 157510; 189012; 220514; 252016; 283518; 315020; 346522; 378024; 409526; 441028; 472530; 504032; 535534; 567036; 598538; 630040; 661542; 693044; 724546; 756048; 787550; 819052; 850554; 882056; 913558; 945060; 976562; 1008064; 1039566; 1071068; 1102570; 1134072; 1165574; 1197076; 1228578; 1260080; 1291582; 1323084; 1354586; 1386088; 1417590; 1449092; 1480594; 1512056]%uint63.

Theorem b_first_b_wins_proved : b_first_b_wins.
Proof.
  apply (table_wins H ott tt fuel K1 K2 RV bounds 587 17).
  - exact (conj Chunk000.chunk (conj Chunk001.chunk (conj Chunk002.chunk (conj Chunk003.chunk (conj Chunk004.chunk (conj Chunk005.chunk (conj Chunk006.chunk (conj Chunk007.chunk (conj Chunk008.chunk (conj Chunk009.chunk (conj Chunk010.chunk (conj Chunk011.chunk (conj Chunk012.chunk (conj Chunk013.chunk (conj Chunk014.chunk (conj Chunk015.chunk (conj Chunk016.chunk (conj Chunk017.chunk (conj Chunk018.chunk (conj Chunk019.chunk (conj Chunk020.chunk (conj Chunk021.chunk (conj Chunk022.chunk (conj Chunk023.chunk (conj Chunk024.chunk (conj Chunk025.chunk (conj Chunk026.chunk (conj Chunk027.chunk (conj Chunk028.chunk (conj Chunk029.chunk (conj Chunk030.chunk (conj Chunk031.chunk (conj Chunk032.chunk (conj Chunk033.chunk (conj Chunk034.chunk (conj Chunk035.chunk (conj Chunk036.chunk (conj Chunk037.chunk (conj Chunk038.chunk (conj Chunk039.chunk (conj Chunk040.chunk (conj Chunk041.chunk (conj Chunk042.chunk (conj Chunk043.chunk (conj Chunk044.chunk (conj Chunk045.chunk (conj Chunk046.chunk (conj Chunk047.chunk (I))))))))))))))))))))))))))))))))))))))))))))))))).
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply Nat.leb_le. reflexivity.
Qed.

Print Assumptions b_first_b_wins_proved.
