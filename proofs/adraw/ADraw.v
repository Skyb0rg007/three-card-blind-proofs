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

Definition bounds : list int := [0; 91089; 120703; 159297; 186463; 223113; 253702; 277970; 319136; 346123; 373802; 411160; 436087; 469983; 501537; 525496; 563072; 591444; 614780; 654513; 681548; 704104; 745927; 771777; 802549; 836944; 861614; 896909; 927512; 951488; 990179; 1018261; 1041688; 1082581; 1109363; 1138491; 1175076; 1200315; 1235728; 1266940; 1291569; 1331097; 1359262; 1383384; 1425589; 1452225; 1486773; 1519326; 1544384; 1579588; 1605036; 1655847; 1716545; 1768735; 1821156; 1868847; 1911445; 1956185; 2002646; 2045767; 2085255; 2126780; 2170668; 2209934; 2246252; 2282874; 2320916; 2360143; 2394614; 2429848; 2465160; 2501471; 2537200; 2571286; 2606292; 2642158; 2678160; 2712090; 2746943; 2783052; 2818359; 2852595; 2887613; 2923538; 2958483; 2992902; 3028624; 3064176; 3098753; 3133741; 3169616; 3204542; 3239720; 3275107; 3310618; 3345769; 3380954; 3416820; 3451939; 3487399; 3523816; 3559305; 3594862; 3637293; 3704737; 3761837; 3828283; 3905453; 3985422; 4065742; 4153154; 4236757; 4322411; 4410925; 4500473; 4589622; 4679551; 4768727; 4864222; 4966415; 5061454; 5171029; 5299352; 5403754; 5500674; 5595088; 5690790; 5785443; 5879511]%uint63.

Theorem a_first_a_safe_proved : a_first_a_safe.
Proof.
  apply (table_safe_a K Hb ott tt M fuel C1 C2 CV N bounds (20)%Z (0)%Z).
  - exact (conj Chunk000.chunk (conj Chunk001.chunk (conj Chunk002.chunk (conj Chunk003.chunk (conj Chunk004.chunk (conj Chunk005.chunk (conj Chunk006.chunk (conj Chunk007.chunk (conj Chunk008.chunk (conj Chunk009.chunk (conj Chunk010.chunk (conj Chunk011.chunk (conj Chunk012.chunk (conj Chunk013.chunk (conj Chunk014.chunk (conj Chunk015.chunk (conj Chunk016.chunk (conj Chunk017.chunk (conj Chunk018.chunk (conj Chunk019.chunk (conj Chunk020.chunk (conj Chunk021.chunk (conj Chunk022.chunk (conj Chunk023.chunk (conj Chunk024.chunk (conj Chunk025.chunk (conj Chunk026.chunk (conj Chunk027.chunk (conj Chunk028.chunk (conj Chunk029.chunk (conj Chunk030.chunk (conj Chunk031.chunk (conj Chunk032.chunk (conj Chunk033.chunk (conj Chunk034.chunk (conj Chunk035.chunk (conj Chunk036.chunk (conj Chunk037.chunk (conj Chunk038.chunk (conj Chunk039.chunk (conj Chunk040.chunk (conj Chunk041.chunk (conj Chunk042.chunk (conj Chunk043.chunk (conj Chunk044.chunk (conj Chunk045.chunk (conj Chunk046.chunk (conj Chunk047.chunk (conj Chunk048.chunk (conj Chunk049.chunk (conj Chunk050.chunk (conj Chunk051.chunk (conj Chunk052.chunk (conj Chunk053.chunk (conj Chunk054.chunk (conj Chunk055.chunk (conj Chunk056.chunk (conj Chunk057.chunk (conj Chunk058.chunk (conj Chunk059.chunk (conj Chunk060.chunk (conj Chunk061.chunk (conj Chunk062.chunk (conj Chunk063.chunk (conj Chunk064.chunk (conj Chunk065.chunk (conj Chunk066.chunk (conj Chunk067.chunk (conj Chunk068.chunk (conj Chunk069.chunk (conj Chunk070.chunk (conj Chunk071.chunk (conj Chunk072.chunk (conj Chunk073.chunk (conj Chunk074.chunk (conj Chunk075.chunk (conj Chunk076.chunk (conj Chunk077.chunk (conj Chunk078.chunk (conj Chunk079.chunk (conj Chunk080.chunk (conj Chunk081.chunk (conj Chunk082.chunk (conj Chunk083.chunk (conj Chunk084.chunk (conj Chunk085.chunk (conj Chunk086.chunk (conj Chunk087.chunk (conj Chunk088.chunk (conj Chunk089.chunk (conj Chunk090.chunk (conj Chunk091.chunk (conj Chunk092.chunk (conj Chunk093.chunk (conj Chunk094.chunk (conj Chunk095.chunk (conj Chunk096.chunk (conj Chunk097.chunk (conj Chunk098.chunk (conj Chunk099.chunk (conj Chunk100.chunk (conj Chunk101.chunk (conj Chunk102.chunk (conj Chunk103.chunk (conj Chunk104.chunk (conj Chunk105.chunk (conj Chunk106.chunk (conj Chunk107.chunk (conj Chunk108.chunk (conj Chunk109.chunk (conj Chunk110.chunk (conj Chunk111.chunk (conj Chunk112.chunk (conj Chunk113.chunk (conj Chunk114.chunk (conj Chunk115.chunk (conj Chunk116.chunk (conj Chunk117.chunk (conj Chunk118.chunk (conj Chunk119.chunk (conj Chunk120.chunk (conj Chunk121.chunk (conj Chunk122.chunk (conj Chunk123.chunk (conj Chunk124.chunk (conj Chunk125.chunk (conj Chunk126.chunk (conj Chunk127.chunk (I))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
  - reflexivity.
  - vm_compute. reflexivity.
  - apply Nat.ltb_lt. reflexivity.
  - apply Nat.leb_le. reflexivity.
  - vm_compute. reflexivity.
  - apply Z.leb_le. reflexivity.
Qed.

Print Assumptions a_first_a_safe_proved.
