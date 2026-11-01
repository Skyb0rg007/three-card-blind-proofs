(** * The claims of [spec/Claims.v], proved

    Each claim rests on a certificate: a table the solver computed, every
    entry of which the checker of [Checker.v] (safety) or [WinCert.v] (wins)
    accepts. The checkers are proved sound for any table at all, so the
    tables themselves need no trust. What the theorems below take as a
    hypothesis is only that the check passed: the solver driver runs the
    extracted checkers over every entry ([solver/certify.ml]). *)

From TCB.Spec Require Import Model Game Claims.
From TCB.Proofs Require Import GameFacts Checker Saturation WinCert.

(** B wins going first: [certify-win DIR B] on the ranked B-win table. *)
Theorem b_first_b_wins_proved : forall H ott tt lookup below hint fuel r v,
  (forall s r v, lookup s r = Some v ->
     check_win H ott tt lookup below hint r fuel true (entry s v) = true) ->
  lookup (key H tt (init PB)) r = Some v -> v <= 20 ->
  b_first_b_wins.
Proof. intros. eapply certified_win_opening; eassumption. Qed.

(** B doesn't lose going second: [certify DIR A] on the B-safe table. *)
Theorem a_first_b_safe_proved : forall H ott tt lookup hint fuel v,
  (forall s v, lookup s = Some v ->
     check_node H ott tt lookup hint fuel true (entry s v) = true) ->
  lookup (key H tt (init PA)) = Some v -> v <= 20 ->
  a_first_b_safe.
Proof. intros. eapply certified_opening; eassumption. Qed.

Theorem a_first_a_cannot_win_proved : a_first_b_safe -> a_first_a_cannot_win.
Proof. intros Hs Hw. exact (wins_not_safe PA _ Hw Hs). Qed.

Print Assumptions b_first_b_wins_proved.
Print Assumptions a_first_b_safe_proved.
