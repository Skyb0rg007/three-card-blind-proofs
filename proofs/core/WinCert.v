(** * Certificates for B's wins

    The least-fixed-point counterpart of [Checker.v]. A certificate entry
    [lookup s r = Some v] claims that B, on [v] life, wins from the turn
    start [s] within rank [r]. [check_win] re-searches one turn of the real
    model from the entry, as [check_node] does, but a turn start reached
    below the entry must be covered by an entry of strictly smaller rank,
    which an untrusted [below] names. Ranks make B's win well founded: by
    strong induction on them, every checked entry is a real win
    ([certified_win]).

    The abstraction is [Checker.R] (B is the protagonist here as well), so
    the simulation facts of [Saturation.v] carry over unchanged. *)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.
From TCB.Spec Require Import Model Game.
From TCB.Proofs Require Import Mono Checker Saturation.

(** A's move lists agree under [R], so A has a move in the real state
    whenever it has one in the certificate's. *)
Lemma moves_theirs : forall H s t, R H s t -> to_move s = PA -> huge_event H s = false ->
  moves t = moves s.
Proof.
  intros H s t HR Hm Hh. apply (moves_eq H s t HR Hh);
    intros [E1 E2]; unfold to_move in Hm; rewrite E1, E2 in Hm; discriminate.
Qed.

Section WinCert.

Variables H ott tt : nat.
Variable lookup : state -> nat -> option nat.
Variable below : state -> nat -> option nat.
Variable hint : state -> move -> bool.

Fixpoint check_win (r fuel : nat) (root : bool) (s : state) : bool :=
  match fuel with
  | 0 => false
  | S f =>
      match winner s with
      | Some PB => true
      | Some PA => false
      | None =>
          if negb root && is_turn_start s then
            match below (key H tt s) r with
            | Some r' =>
                if r' <? r then
                  match lookup (key H tt s) r' with
                  | Some v => v <=? s.(sideB).(life)
                  | None => false
                  end
                else false
            | None => false
            end
          else if huge_event H s then false
          else
            let next m := let s' := step s m in if too_many ott s' then false else check_win r f false s' in
            match to_move s with
            | PB => some_move (fun m => if hint s m then next m else false) (moves s)
            | PA => match moves s with [] => false | ms => all_moves next ms end
            end
      end
  end.

(** Every entry checks, possibly as a position where A has more life
    ([d]), as in [Checker.cert_ok]. *)
Hypothesis cert_ok : forall s r v, lookup s r = Some v ->
  exists d fuel, check_win r fuel true (entry (bump PA d s) v) = true.

Lemma check_win_winner : forall r f root s, check_win r f root s = true -> winner s <> Some PA.
Proof.
  intros r [| f] root s Hc; [discriminate |]. cbn in Hc.
  destruct (winner s) as [[] |]; congruence.
Qed.

Section Rank.

Variable r : nat.
Hypothesis IH : forall r', r' < r -> forall s v t, lookup s r' = Some v -> R H (entry s v) t -> wins PB t.

Lemma check_win_wins : forall f root s t, check_win r f root s = true -> R H s t -> wins PB t.
Proof.
  induction f as [| f IHf]; intros root s t Hc HR; [discriminate |].
  cbn [check_win] in Hc.
  destruct (winner s) as [[] |] eqn:Hw.
  - discriminate.
  - apply wins_over. rewrite (R_winner H s t HR). exact Hw.
  - destruct (negb root && is_turn_start s) eqn:Ht.
    + destruct (below (key H tt s) r) as [r' |]; [| discriminate].
      destruct (r' <? r) eqn:Hr; [| discriminate]. apply Nat.ltb_lt in Hr.
      destruct (lookup (key H tt s) r') as [v |] eqn:Hl; [| discriminate].
      apply Nat.leb_le in Hc.
      apply (IH r' Hr (key H tt s) v t Hl).
      eapply R_trans; [| exact HR]. eapply R_key; [exact HR | exact Hc].
    + destruct (huge_event H s) eqn:Hh; [discriminate |].
      assert (Hwt : winner t = None) by (rewrite (R_winner H s t HR); exact Hw).
      destruct (to_move s) eqn:Hm.
      * (* A to move: every real move is a certificate move *)
        destruct (moves s) as [| m0 ms] eqn:Hms; [discriminate |].
        rewrite <- Hms, all_moves_forallb in Hc. rewrite forallb_forall in Hc.
        pose proof (moves_theirs H s t HR Hm Hh) as Emt.
        apply wins_theirs.
        -- exact Hwt.
        -- rewrite (R_to_move H s t HR). exact Hm.
        -- intros m Hin. rewrite Emt in Hin.
           specialize (Hc m Hin). destruct (too_many ott (step s m)); [discriminate |].
           apply (IHf false (step s m)); [exact Hc |].
           apply sim_step; [exact HR | exact Hin | exact Hh | eapply check_win_winner; exact Hc].
      * (* B to move: the hinted move is real *)
        rewrite some_move_existsb in Hc. apply existsb_exists in Hc as [m [Hin Hc]].
        destruct (hint s m); [| discriminate]. destruct (too_many ott (step s m)); [discriminate |].
        apply (wins_mine PB t m).
        -- exact Hwt.
        -- rewrite (R_to_move H s t HR). exact Hm.
        -- apply (sim_mine H s t m HR Hm Hw Hh Hin).
        -- apply (IHf false (step s m)); [exact Hc |].
           apply sim_step; [exact HR | exact Hin | exact Hh | eapply check_win_winner; exact Hc].
Qed.

End Rank.

Theorem cert_wins : forall r s v t, lookup s r = Some v -> R H (entry s v) t -> wins PB t.
Proof.
  induction r as [r IH] using lt_wf_ind.
  intros s v t Hl HR. destruct (cert_ok _ _ _ Hl) as (d & fuel & Hf).
  apply (wins_opp_bump PA d t).
  apply (check_win_wins r IH fuel true (entry (bump PA d s) v) (bump PA d t) Hf).
  rewrite entry_bump. apply R_bump. exact HR.
Qed.

End WinCert.

(** If every entry checks and some entry for the opening's key asks for at
    most B's starting 20 life, B wins from the opening. *)
Theorem certified_win_opening : forall H ott tt lookup below hint p r v,
  (forall s r v, lookup s r = Some v ->
     exists d fuel, check_win H ott tt lookup below hint r fuel true (entry (bump PA d s) v) = true) ->
  lookup (key H tt (init p)) r = Some v -> v <= 20 -> wins PB (init p).
Proof.
  intros H ott tt lookup below hint p r v Hok Hl Hv.
  apply (cert_wins H ott tt lookup below hint Hok r _ v _ Hl).
  apply (R_key H tt (init p) (init p) v (R_init H p)).
  destruct p; exact Hv.
Qed.
