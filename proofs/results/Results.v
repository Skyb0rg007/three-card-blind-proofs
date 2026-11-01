(** * The claims of [spec/Claims.v], proved

    Each claim rests on a certificate: a table of positions computed by the
    solver, in [proofs/bfirst] and [proofs/afirst]. Rocq runs the checker of
    [WinCert.v] (wins) or [Checker.v] (safety) on every entry, in [vm_compute]
    ([Chunk*.v]). The checkers are proved sound for any table at all
    ([Packed.v] ties them to the packed tables), so the tables need no trust. *)

From TCB.Spec Require Import Model Game Claims.
From TCB.Proofs Require Import GameFacts Progress.
From TCB.BFirst Require BFirst.
From TCB.AFirst Require AFirst.

Theorem never_stuck_holds : never_stuck.
Proof. exact moves_ne. Qed.

Theorem b_first_b_wins_holds : b_first_b_wins.
Proof. exact BFirst.b_first_b_wins_proved. Qed.

Theorem a_first_b_safe_holds : a_first_b_safe.
Proof. exact AFirst.a_first_b_safe_proved. Qed.

Theorem a_first_a_cannot_win_holds : a_first_a_cannot_win.
Proof. intro Hw. exact (wins_not_safe PA _ Hw a_first_b_safe_holds). Qed.

Print Assumptions never_stuck_holds.
Print Assumptions b_first_b_wins_holds.
Print Assumptions a_first_b_safe_holds.
Print Assumptions a_first_a_cannot_win_holds.
