From mathcomp Require Import all_ssreflect all_algebra.
Require Import Coq.Lists.List.
Import ListNotations.

(* Prove that 3 is prime. *)
Lemma prime3 : prime 3.
Proof.
rewrite /prime.
split.
Qed.

(* Main lemma: 3 does not divide 2^n. *)
Lemma pow2_not_div_by_3 (n : nat) : ~~ (3 %| 2^n).
Proof.
elim: n => [|n IH].
- (* Base case: 2^0 = 1, so 3 does not divide 1 *)
  by rewrite expn0 dvdn1.
- (* Inductive step: 2^(n+1) = 2 * 2^n *)
  rewrite expnS.
  (* Case analysis on whether 3 divides 2 * 2^n *)
  case_eq (3 %| (2 * 2^n)).
  + (* If 3 divides 2 * 2^n, then by prime_dvd_mul, 3 divides 2 or 3 divides 2^n *)
    intros.
    assert ((3 %| 2 * 2 ^ n) = (3 %| 2) || (3 %| 2 ^ n)) by (apply (@Euclid_dvdM 2 (2^n) 3 prime3)).
    rewrite H in H0. clear H.
    rewrite H0. clear H0.
    rewrite negb_or.
    case_eq (3 %| 2 ^ n).
    intros.
    rewrite H in IH.
    apply IH.
    intros.
    simpl.
    exact is_true_true.
    intros.
    simpl.
    exact is_true_true.
Qed.

Variant MIU :=
  | M
  | I
  | U.

Variant Move :=
  | R1
  | R2
  | R3
  | R4.

Definition apply : Move -> list MIU -> list MIU := fun m x => match m with
  (* Rule 1: Add a U to the end of any string ending in I *)
  | R1 => [] (* TO DO: Replace this with actual implementation of rule *)

  (* Rule 2: Double the string after the M *)
  | R2 => [] (* TO DO: Replace this with actual implementation of rule *)

  (* Rule 3: Replace any III with a U *)
  | R3 => [] (* TO DO: Replace this with actual implementation of rule *)

  (* Rule 4: Remove any UU *)
  | R4 => [] (* TO DO: Replace this with actual implementation of rule *)
end.

Theorem no_solution_exists : ~exists (ms : list Move), fold_right apply [M; I] ms = [M; U].
Proof.
  intro.
  admit.
Admitted.
