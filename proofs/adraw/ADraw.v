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
Require Chunk048.
Require Chunk049.
Require Chunk050.
Require Chunk051.
Require Chunk052.
Require Chunk053.
Require Chunk054.
Require Chunk055.
Require Chunk056.
Require Chunk057.
Require Chunk058.
Require Chunk059.
Require Chunk060.
Require Chunk061.
Require Chunk062.
Require Chunk063.
Require Chunk064.
Require Chunk065.
Require Chunk066.
Require Chunk067.
Require Chunk068.
Require Chunk069.
Require Chunk070.
Require Chunk071.
Require Chunk072.
Require Chunk073.
Require Chunk074.
Require Chunk075.
Require Chunk076.
Require Chunk077.
Require Chunk078.
Require Chunk079.
Require Chunk080.
Require Chunk081.
Require Chunk082.
Require Chunk083.
Require Chunk084.
Require Chunk085.
Require Chunk086.
Require Chunk087.
Require Chunk088.
Require Chunk089.
Require Chunk090.
Require Chunk091.
Require Chunk092.
Require Chunk093.
Require Chunk094.
Require Chunk095.
Require Chunk096.
Require Chunk097.
Require Chunk098.
Require Chunk099.
Require Chunk100.
Require Chunk101.
Require Chunk102.
Require Chunk103.
Require Chunk104.
Require Chunk105.
Require Chunk106.
Require Chunk107.
Require Chunk108.
Require Chunk109.
Require Chunk110.
Require Chunk111.
Require Chunk112.
Require Chunk113.
Require Chunk114.
Require Chunk115.
Require Chunk116.
Require Chunk117.
Require Chunk118.
Require Chunk119.
Require Chunk120.
Require Chunk121.
Require Chunk122.
Require Chunk123.
Require Chunk124.
Require Chunk125.
Require Chunk126.
Require Chunk127.

Definition bounds : list int := [0; 87065; 119529; 160855; 190427; 235707; 267638; 316287; 351251; 400640; 437608; 489982; 525276; 578500; 613894; 667286; 702304; 756194; 790268; 845435; 884274; 934041; 975962; 1022061; 1066407; 1109329; 1155535; 1196192; 1242807; 1282276; 1328977; 1367682; 1414709; 1452867; 1500028; 1537760; 1581429; 1615362; 1691649; 1762270; 1833391; 1895909; 1960303; 2028699; 2090774; 2157187; 2223708; 2285146; 2349792; 2413367; 2476399; 2540535; 2602062; 2664815; 2725534; 2787674; 2849631; 2909680; 2971118; 3031451; 3091864; 3151250; 3211814; 3271294; 3330235; 3389494; 3449499; 3508127; 3567843; 3627436; 3667844; 3697468; 3725013; 3749963; 3779486; 3809892; 3842842; 3875000; 3907784; 3941535; 3973702; 4007569; 4041268; 4074944; 4110995; 4148845; 4184300; 4218081; 4249583; 4283838; 4317292; 4352675; 4387784; 4423546; 4458935; 4493709; 4527023; 4563578; 4599093; 4635836; 4672450; 4708640; 4744583; 4778920; 4816080; 4855694; 4912689; 4959998; 5005642; 5050628; 5099646; 5149829; 5206279; 5266484; 5315433; 5357408; 5399721; 5441734; 5481755; 5521569; 5560608; 5599535; 5639436; 5679050; 5719892; 5759948; 5799406; 5839824; 5879511]%uint63.

Theorem a_first_a_safe_proved : a_first_a_safe.
Proof.
  apply (table_safe_a K Hb ott tt fuel C1 C2 CV N bounds (20)%Z (0)%Z).
  - exact (conj Chunk000.chunk (conj Chunk001.chunk (conj Chunk002.chunk (conj Chunk003.chunk (conj Chunk004.chunk (conj Chunk005.chunk (conj Chunk006.chunk (conj Chunk007.chunk (conj Chunk008.chunk (conj Chunk009.chunk (conj Chunk010.chunk (conj Chunk011.chunk (conj Chunk012.chunk (conj Chunk013.chunk (conj Chunk014.chunk (conj Chunk015.chunk (conj Chunk016.chunk (conj Chunk017.chunk (conj Chunk018.chunk (conj Chunk019.chunk (conj Chunk020.chunk (conj Chunk021.chunk (conj Chunk022.chunk (conj Chunk023.chunk (conj Chunk024.chunk (conj Chunk025.chunk (conj Chunk026.chunk (conj Chunk027.chunk (conj Chunk028.chunk (conj Chunk029.chunk (conj Chunk030.chunk (conj Chunk031.chunk (conj Chunk032.chunk (conj Chunk033.chunk (conj Chunk034.chunk (conj Chunk035.chunk (conj Chunk036.chunk (conj Chunk037.chunk (conj Chunk038.chunk (conj Chunk039.chunk (conj Chunk040.chunk (conj Chunk041.chunk (conj Chunk042.chunk (conj Chunk043.chunk (conj Chunk044.chunk (conj Chunk045.chunk (conj Chunk046.chunk (conj Chunk047.chunk (conj Chunk048.chunk (conj Chunk049.chunk (conj Chunk050.chunk (conj Chunk051.chunk (conj Chunk052.chunk (conj Chunk053.chunk (conj Chunk054.chunk (conj Chunk055.chunk (conj Chunk056.chunk (conj Chunk057.chunk (conj Chunk058.chunk (conj Chunk059.chunk (conj Chunk060.chunk (conj Chunk061.chunk (conj Chunk062.chunk (conj Chunk063.chunk (conj Chunk064.chunk (conj Chunk065.chunk (conj Chunk066.chunk (conj Chunk067.chunk (conj Chunk068.chunk (conj Chunk069.chunk (conj Chunk070.chunk (conj Chunk071.chunk (conj Chunk072.chunk (conj Chunk073.chunk (conj Chunk074.chunk (conj Chunk075.chunk (conj Chunk076.chunk (conj Chunk077.chunk (conj Chunk078.chunk (conj Chunk079.chunk (conj Chunk080.chunk (conj Chunk081.chunk (conj Chunk082.chunk (conj Chunk083.chunk (conj Chunk084.chunk (conj Chunk085.chunk (conj Chunk086.chunk (conj Chunk087.chunk (conj Chunk088.chunk (conj Chunk089.chunk (conj Chunk090.chunk (conj Chunk091.chunk (conj Chunk092.chunk (conj Chunk093.chunk (conj Chunk094.chunk (conj Chunk095.chunk (conj Chunk096.chunk (conj Chunk097.chunk (conj Chunk098.chunk (conj Chunk099.chunk (conj Chunk100.chunk (conj Chunk101.chunk (conj Chunk102.chunk (conj Chunk103.chunk (conj Chunk104.chunk (conj Chunk105.chunk (conj Chunk106.chunk (conj Chunk107.chunk (conj Chunk108.chunk (conj Chunk109.chunk (conj Chunk110.chunk (conj Chunk111.chunk (conj Chunk112.chunk (conj Chunk113.chunk (conj Chunk114.chunk (conj Chunk115.chunk (conj Chunk116.chunk (conj Chunk117.chunk (conj Chunk118.chunk (conj Chunk119.chunk (conj Chunk120.chunk (conj Chunk121.chunk (conj Chunk122.chunk (conj Chunk123.chunk (conj Chunk124.chunk (conj Chunk125.chunk (conj Chunk126.chunk (conj Chunk127.chunk (I))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
  - reflexivity.
  - vm_compute. reflexivity.
  - apply Nat.ltb_lt. reflexivity.
  - apply Nat.leb_le. reflexivity.
  - vm_compute. reflexivity.
  - apply Z.leb_le. reflexivity.
Qed.

Print Assumptions a_first_a_safe_proved.
