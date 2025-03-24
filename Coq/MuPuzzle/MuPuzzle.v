Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Le.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.micromega.Lia.

Open Scope nat_scope.

Require Import CoqUtilLib.ListFunctions.
Require Import CoqUtilLib.ListFunctions.
Require Import FreeMonoid.MonoidConcat.

(******************************************************************************)
(* The MIU system *)

Variant MIU :=
  (* It's trivial to see M is preserved by all rules and it complicates the rules
    trying to account for an M not at the start.

    For this reason, I'm leaving the M implied as being at the start of all MIU lists.
  *)
  | I
  | U.

Variant Move :=
  | R1
  | R2
  | R3
  | R4.

(* Auxiliary functions for the rules *)

Definition rule_1 (l : list MIU) : list MIU :=
  match last l U with
  | I => l ++ [U]
  | _ => l
  end.

Definition rule_2 (l : list MIU) : list MIU :=
  l ++ l.

Fixpoint rule_3 (l : list MIU) : list MIU :=
  match l with
  | I :: I :: I :: t => U :: t         (* Replace first occurrence of III with U *)
  | x :: t => x :: rule_3 t
  | [] => []                          
  end.

Fixpoint rule_4 (l : list MIU) : list MIU :=
  match l with
  | U :: U :: t => t                  (* Remove first occurrence of UU *)
  | x :: t => x :: rule_4 t
  | [] => []                          
  end.

(* The function apply dispatches the given move. For R1 we append a U if the last
   symbol is I; otherwise the string is unchanged. *)
Definition apply (m : Move) (l : list MIU) : list MIU :=
  match m with
  | R1 => rule_1 l
  | R2 => rule_2 l
  | R3 => rule_3 l
  | R4 => rule_4 l
  end.

(* Count the number of I's in a string *)
Fixpoint i_count (l : list MIU) : nat :=
  match l with
  | I :: t => 1 + i_count t
  | _ :: t => i_count t
  | [] => 0
  end.

(******************************************************************************)
(* Invariant proofs *)

(* A simple auxiliary lemma: appending [U] does not change the I-count *)
Lemma i_count_app_U: forall l, i_count (l ++ [U]) = i_count l.
Proof.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

(* A simple auxiliary lemma: appending [U] does not change the I-count *)
Lemma i_count_apps_U: forall l1 l2, i_count (l1 ++ [U] ++ l2) = i_count l1 + i_count l2.
Proof.
  induction l1, l2.
  - reflexivity.
  - reflexivity.
  - intros.
    simpl.
    rewrite <- plus_n_O.
    rewrite i_count_app_U.
    reflexivity.
  - admit.
    (* rewrite <- plus_n_O.
    rewrite i_count_app_U.
    reflexivity. *)
Admitted.

Lemma i_count_app_I: forall l, i_count (l ++ [I]) = i_count l + 1.
Proof.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    case a.
    reflexivity.
    reflexivity.
Qed.

(* A simple auxiliary lemma: consing I increments I-count *)
Lemma i_count_app_comm: forall l1 l2, i_count (l1 ++ l2) = i_count (l2 ++ l1).
Proof.
  induction l1, l2.
  - reflexivity.
  - rewrite app_nil_r.
    reflexivity.
  - rewrite app_nil_r.
    reflexivity.
  - 
    rewrite ListFunctions.cons_append.
    rewrite <- app_assoc.
    rewrite (ListFunctions.cons_append _ m l2).
    rewrite <- app_assoc.
    case a.
    unfold i_count.

    admit.
Admitted.

(* A simple auxiliary lemma: consing I increments I-count *)
Lemma i_count_app_plus: forall l1 l2, i_count (l1 ++ l2) = i_count l1 + i_count l2.
Proof.
  induction l1, l2.
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite app_nil_r.
    rewrite <- plus_n_O.
    reflexivity.
  - 
    rewrite ListFunctions.cons_append.
    rewrite <- app_assoc.
    rewrite (ListFunctions.cons_append _ m l2).
    rewrite <- app_comm_cons.
    rewrite ListFunctions.cons_append.
    admit.
    (* rewrite IHl.
    reflexivity. *)
Admitted.

(* A simple auxiliary lemma: consing I increments I-count *)
Lemma i_count_cons_I: forall l, i_count (I :: l) = 1 + i_count l.
Proof.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    case a.
    reflexivity.
    reflexivity.
Qed.

(* A simple auxiliary lemma: consing I increments I-count *)
Lemma i_count_cons_I_equivalent_to_app_I: forall l, i_count (I :: l) = i_count (l ++ [I]).
Proof.
  intros.
  rewrite i_count_app_I.
  rewrite i_count_cons_I.
  rewrite Nat.add_comm.
  reflexivity.
Qed.

(* Rule R1 simply adds a U at the end when the last symbol is I, so it preserves i_count. *)
Theorem rule_1_preserves_i_count : forall (l : list MIU), i_count (apply R1 l) = i_count l.
Proof.
  intros l.
  destruct l as [|a l'].
  - simpl.
    reflexivity.
  - unfold apply.
    unfold rule_1.
    destruct (last (a :: l') U) eqn:Hl.
    + (* last symbol is I *)
      rewrite i_count_app_U.
      reflexivity.
    + (* last symbol is U *)
      reflexivity.
Qed.

(* The standard MIU invariant is that in any derivable string the number of I's is not divisible by 3.
   In symbols, starting from [M; I] we always have ~(3 %| i_count s).
   For rule R2, one shows that if l = prefix ++ suffix with prefix ending in M,
   then i_count l = i_count suffix (since i_count prefix = 0) and rule R2 yields
   prefix ++ suffix ++ suffix, i.e. 2*(i_count suffix). Since 2 is invertible mod 3,
   3 ∤ i_count l  implies 3 ∤ (2 * i_count l).
   
   Rule R3 subtracts 3 I's (if it replaces III with U), and rule R4 does not affect I's.
   We state these facts as lemmas (proof details omitted and left as admit). *)

Lemma rule_2_doubles_i_count: forall l, i_count (rule_2 l) = 2 * i_count l.
Proof.
  intros.
  unfold rule_2.
  rewrite i_count_app_plus.
  unfold mult.
  rewrite <- plus_n_O.
  reflexivity.
Qed.

Lemma apply_R2_doubles_i_count: forall l, i_count (apply R2 l) = 2 * i_count l.
Proof.
  intros.
  case l.
  - reflexivity.
  - intros.
    unfold apply.
    rewrite <- rule_2_doubles_i_count.
    reflexivity.
Qed.

Lemma rule_3_subtracts_3_from_i_count_if_large: forall l, 3 <= i_count l -> i_count (apply R3 l) = i_count l - 3.
Proof.
  admit.
Admitted.

Lemma rule_3_does_nothing_to_i_count_if_small: forall l, i_count l <= 3 -> i_count (apply R3 l) = i_count l.
Proof.
  admit.
Admitted.

Lemma rule_2_preserves_invariant: forall l, ((i_count l mod 3) =? 0) = ((i_count (apply R2 l) mod 3) =? 0).
Proof.
  intros.
  rewrite rule_2_doubles_i_count.
  rewrite <- Nat.Div0.mul_mod_idemp_l.
  replace (2 mod 3) with 2 by reflexivity.
  replace (i_count l mod 3 =? 0) with ((2 * i_count l) mod 3 =? 0).
  - reflexivity.
  - induction l.
    + reflexivity.
    + case a.
      (* * simp *)
      admit.
Admitted.

Lemma rule_3_preserves_invariant: forall l,
  ((i_count l) mod 3 =? 0) =
  ((i_count (apply R3 l)) mod 3 =? 0).
Proof.
  (* intros l.
  (* Proof: Replacing III by U subtracts 3 from the I‑count.
     Since subtracting a multiple of 3 does not affect divisibility by 3, the invariant holds. *)
  
  assert (3 <> i_count l).
  {
    intro.
    rewrite H0 in H. clear H0.
    assert (i_count l %| i_count l = true) by apply (dvdnn (i_count l)).
    rewrite H0 in H. clear H0.
    discriminate.
  }
  
  pose proof (le_total 3 (i_count l)).
  
  rewrite rule_3_subtracts_3_from_i_count_if_possible.
  rewrite dvdn_subl.
  apply H.

  assert (3 = i_count l -> ~(3 = i_count l) -> False).
  {
    intros H_eq H_neq.
    unfold not in H_neq.
    apply H_neq in H_eq.
    exact H_eq.
  }

  destruct H0.

  apply Nat.le_antisymm in H0.

  Search (_ %| _).
  case_eq l.
  - intros.
    rewrite H0 in H.
    simpl in H.
    simpl.
    apply H.
  - intros.
    rewrite H0 in H.
    simpl in H.
    simpl. *)

  admit.
Admitted.

Lemma rule_4_preserves_invariant: forall l,
  ((i_count l) mod 3 =? 0) =
  ((i_count (apply R4 l)) mod 3 =? 0).
Proof.
  intros l.
  (* Proof: Rule R4 removes UU, which does not affect the I‑count. *)
  admit.
Admitted.

(* We then conclude that every move preserves the invariant: *)
Lemma move_preserves_invariant: forall m l,
  ((i_count l) mod 3 =? 0) =
  ((i_count (apply m l)) mod 3 =? 0).
Proof.
  intros m l.
  destruct m.
  - rewrite rule_1_preserves_i_count. reflexivity.
  - rewrite rule_2_preserves_invariant. reflexivity.
  - rewrite rule_3_preserves_invariant. reflexivity.
  - rewrite rule_4_preserves_invariant. reflexivity.
Qed.

(* In our system the initial string is [M; I]. Notice that i_count [M; I] = 1,
   and 1 is not divisible by 3. *)
Lemma initial_invariant: ((i_count [I]) mod 3 =? 0) = false.
Proof.
  simpl.
  reflexivity.
Qed.

(* By induction on a sequence of moves, the invariant is maintained. *)
Lemma invariant_moves: forall ms,
  ((i_count (fold_right apply [I] ms)) mod 3 =? 0) = false.
Proof.
  induction ms.
  - simpl; apply initial_invariant.
  - simpl.
    admit.
    (* apply move_preserves_invariant.
    apply IHms. *)
Admitted.

(******************************************************************************)
(* Final theorem: No solution exists *)

Theorem no_solution_exists : ~ exists (ms : list Move), fold_right apply [I] ms = [U].
Proof.
  intro H.
  destruct H as [ms Hms].
  (* By the invariant, fold_right apply [M; I] ms has an I‑count not divisible by 3. *)
  pose proof (invariant_moves ms) as Hinv.
  rewrite Hms in Hinv.
  (* But i_count [M; U] = i_count (M :: [U]) = 0, and 0 is divisible by 3. *)
  simpl in Hinv.
  discriminate.
Qed.
