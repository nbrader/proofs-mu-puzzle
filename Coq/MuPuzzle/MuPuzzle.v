Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Le.
Require Import ArithRing Ring.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Plus.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Open Scope nat_scope.

Require Import CoqUtilLib.ListFunctions.
Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidFree.
Require Import FreeMonoid.StructMagma.
Require Import FreeMonoid.StructSemigroup.
Require Import FreeMonoid.StructMonoid.

(******************************************************************************)
(* The MIU system *)

Variant MIU :=
  (* It's trivial to see M is preserved by all rules and it complicates the rules
    trying to account for an M not at the start.

    For this reason, I'm leaving the M implied as being at the start of all MIU lists.
  *)
  | I
  | U.

Definition MIU_eqb (a b : MIU) : bool :=
match a, b with
| I, I => true
| U, U => true
| _, _ => false
end.

Fixpoint list_eqb {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: t1, x2 :: t2 => eqb x1 x2 && list_eqb eqb t1 t2
  | _, _ => false
  end.

Lemma list_eqb_eq :
  forall (A : Type) (eqb : A -> A -> bool),
    (forall x y, eqb x y = true <-> x = y) ->
    forall l1 l2,
      list_eqb eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb Heq.
  induction l1 as [| x1 t1 IH]; intros [| x2 t2]; simpl.
  - split; auto.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - rewrite Bool.andb_true_iff.
    rewrite Heq.
    rewrite IH.
    split.
    + intros [H1 H2]. subst. reflexivity.
    + intros H. inversion H. split; auto.
Qed.

Lemma MIU_eqb_spec : forall x y : MIU, MIU_eqb x y = true <-> x = y.
Proof.
  intros x y.
  split.
  - (* -> direction *)
    destruct x, y; simpl; try discriminate; reflexivity.
  - (* <- direction *)
    intros ->.
    destruct y; simpl; reflexivity.
Qed.

Inductive Move :=
  | R1 : Move
  | R2 : Move
  | R3 : nat -> Move
  | R4 : nat -> Move.

(* Auxiliary functions for the rules *)

Definition rule_1 (l : list MIU) : list MIU :=
  match last l U with
  | I => l ++ [U]
  | _ => l
  end.

Definition rule_2 (l : list MIU) : list MIU :=
  l ++ l.

Definition rule_3 (n : nat) (l : list MIU) : list MIU :=
  if list_eqb MIU_eqb (take_n 3 (drop_n n l)) [I; I; I]
  then take_n n l ++ [U] ++ drop_n (n + 3) l
  else l.

Definition rule_4 (n : nat) (l : list MIU) : list MIU :=
  if list_eqb MIU_eqb (take_n 2 (drop_n n l)) [U; U]
  then take_n n l ++ drop_n (n + 2) l
  else l.

(* The function apply dispatches the given move. For R1 we append a U if the last
   symbol is I; otherwise the string is unchanged. *)
Definition apply (m : Move) (l : list MIU) : list MIU :=
  match m with
  | R1 => rule_1 l
  | R2 => rule_2 l
  | R3 n => rule_3 n l
  | R4 n => rule_4 n l
  end.

(* Monoid Stuff *)
Instance nat_Magma : Magma nat := {
  m_op := plus
}.

Instance nat_Semigroup : Semigroup nat := {
  sg_assoc := Nat.add_assoc
}.

Instance nat_Monoid : Monoid nat := {
  mn_id := 0;
  mn_left_id := Nat.add_0_l;
  mn_right_id := Nat.add_0_r
}.

Module MIUBasis <: BasisType.
  Definition Basis := MIU.
End MIUBasis.

Module MIUFreeMonoid := FreeMonoidModule MIUBasis.

(* Define a function to count I's *)
Definition i_count (l : list MIU) : nat := MIUFreeMonoid.foldMap nat_Monoid (fun x => match x with I => 1 | U => 0 end) l.

(******************************************************************************)
(* Invariant proofs *)

(* A simple auxiliary lemma: appending [U] does not change the I-count *)
Lemma i_count_app_U : forall l, i_count (l ++ [U]) = i_count l.
Proof.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma i_count_app_I : forall l, i_count (l ++ [I]) = i_count l + 1.
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

Instance list_MIU_Magma : Magma (list MIU) := MIUFreeMonoid.FreeMonoid_Magma.
Instance list_MIU_Semigroup : Semigroup (list MIU) := MIUFreeMonoid.FreeMonoid_Semigroup.
Instance list_MIU_Monoid : Monoid (list MIU) := MIUFreeMonoid.FreeMonoid_Monoid.

Require Import MonoidHom.

(* Now prove the lemma using the universal property *)
Lemma i_count_foldMap_plus_mor : forall l1 l2, i_count (m_op l1 l2) = i_count l1 + i_count l2.
Proof.
  intros l1 l2.
  pose proof (MIUFreeMonoid.foldMap_mor nat_Monoid (fun x => match x with I => 1 | U => 0 end)).
  rewrite homo_preserves_op.
  reflexivity.
Qed.

Lemma i_count_plus_mor : forall l1 l2, i_count (l1 ++ l2) = i_count l1 + i_count l2.
Proof.
  intros l1 l2.
  apply i_count_foldMap_plus_mor.
Qed.

Lemma i_count_cons_U : forall l, i_count (U :: l) = i_count l.
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
Lemma i_count_cons_I : forall l, i_count (I :: l) = 1 + i_count l.
Proof.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    case a.
    reflexivity.
    reflexivity.
Qed.

Lemma i_count_cons_I_equivalent_to_app_I : forall l, i_count (I :: l) = i_count (l ++ [I]).
Proof.
  intros.
  rewrite i_count_app_I.
  rewrite i_count_cons_I.
  rewrite Nat.add_comm.
  reflexivity.
Qed.

Lemma i_count_cons_U_equivalent_to_app_U : forall l, i_count (U :: l) = i_count (l ++ [U]).
Proof.
  intros.
  rewrite i_count_app_U.
  rewrite i_count_cons_U.
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

Lemma rule_2_doubles_i_count : forall l, i_count (rule_2 l) = 2 * i_count l.
Proof.
  intros.
  unfold rule_2.
  rewrite i_count_plus_mor.
  unfold mult.
  rewrite <- plus_n_O.
  reflexivity.
Qed.

Lemma ex_comm : forall x : nat,
  (exists z : nat, 2 * x = 3 * z) <-> (exists z : nat, 2 * x = z * 3).
Proof.
  intros x. split; intros [z H]; exists z; rewrite H; apply Nat.mul_comm.
Qed.

Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.BinInt.

Definition nat_prime (n : nat) := prime (Z_of_nat n).

Theorem nat_prime_3 : nat_prime 3.
Proof.
  apply prime_alt; split.
  - lia.
  - intros d H1 H2.
    assert (d = 2) by lia.
    rewrite H in H2.
    assert (3 mod 2 <> 0) by discriminate.
    apply Zdivide_mod in H2.
    contradiction.
Qed.

Require Import Coq.ZArith.ZArith.

Lemma nat_divide_to_Z_divide :
  forall x : nat, Nat.divide 3 (2 * x) -> Z.divide (Z.of_nat 3) (Z.of_nat 2 * Z.of_nat x).
Proof.
  intros x [k Hk].  (* destruct the Nat.divide witness *)
  exists (Z.of_nat k).
  rewrite <- inj_mult.
  rewrite Hk.
  apply inj_mult.
Qed.

Lemma three_does_not_divide_two : ~ (3 | 2)%Z.
Proof.
  intros [k Hk].
  lia.
Qed.

Open Scope nat_scope.

Lemma helper : forall x : nat,
  ~ (exists z : nat, x = z * 3) ->
  ~ (exists z : nat, 2 * x = z * 3).
Proof.
  intros x Hx [z Hz].
  destruct nat_prime_3.
  (* 3 | 2 * x *)
  assert (Nat.divide 3 (2 * x)) by (exists z; exact Hz).
  (* suppose 3 ∤ x *)
  assert (~ Nat.divide 3 x).
  {
    intros [z' Ez].
    apply Hx.
    exists z'.
    exact Ez.
  }
  pose proof prime_mult.
  assert ((Z.of_nat 3 | Z.of_nat 2) \/ (Z.of_nat 3 | Z.of_nat x)).
  {
    apply prime_mult.
    apply nat_prime_3.
    apply nat_divide_to_Z_divide.
    apply H1.
  }
  destruct H4.
  - pose proof three_does_not_divide_two.
    contradiction.
  - apply H2.
    unfold Nat.divide.
    unfold Z.divide in H4.
    destruct H4.
    exists (Z.to_nat x0).
    lia.
Qed.

Lemma mult_by_2_preserves_mod3_nonzero x :
  x mod 3 <> 0 -> (2 * x) mod 3 <> 0.
Proof.
  intros Hx.
  rewrite Nat.mod_divide in *.
  {
    unfold Nat.divide in *.
    apply helper.
    apply Hx.
  }
  discriminate.
  discriminate.
Qed.

Lemma mult_mod_nonzero : forall n,
  S n mod 3 <> 0 -> (2 * S n) mod 3 <> 0.
Proof.
  intros n H.
  apply mult_by_2_preserves_mod3_nonzero in H.
  exact H.
Qed.

Lemma mul2_mod3_bij :
  forall x,
    ((2 * x) mod 3 =? 0) = (x mod 3 =? 0).
Proof.
  intro x.
  case_eq (x mod 3).
  intros.

  (* Turn boolean equalities into Prop ↔: Nat.eqb_eq etc. *)
  rewrite Nat.eqb_eq.
  (* m mod n = 0 ↔ n | m *)
  rewrite Nat.mod_divide.
  - unfold Nat.divide.
    apply ex_comm.
    apply Nat.Div0.mod_divides.
    rewrite Nat.Div0.mul_mod.
    rewrite H.
    simpl.
    reflexivity.
  - discriminate.
  - intros.
    rewrite Nat.Div0.mul_mod.
    simpl (S n =? 0).
    apply Nat.eqb_neq.
    pose proof (O_S n).
    rewrite <- H in H0.
    apply not_eq_sym in H0. clear H.
    case_eq (x mod 3).
    + intros.
      contradiction.
    + intros.
      apply mult_mod_nonzero.
      rewrite <- H.
      rewrite Nat.Div0.mod_mod.
      apply H0.
Qed.

Lemma rule_2_preserves_invariant : forall l, ((i_count l mod 3) =? 0) = ((i_count (rule_2 l) mod 3) =? 0).
Proof.
  intros.
  rewrite rule_2_doubles_i_count.
  replace (i_count l mod 3 =? 0) with ((2 * i_count l) mod 3 =? 0).
  - reflexivity.
  - induction l.
    + reflexivity.
    + case a.
      * rewrite i_count_cons_I_equivalent_to_app_I.
        rewrite i_count_plus_mor.
        replace (i_count [I]) with 1 by reflexivity.
        apply mul2_mod3_bij.
      * rewrite i_count_cons_U_equivalent_to_app_U.
        rewrite i_count_plus_mor.
        replace (i_count [U]) with 0 by reflexivity.
        replace (i_count l + 0) with (i_count l) by ring.
        apply IHl.
Qed.

(* Lemma stating that applying rule_3 either subtracts exactly 3 I's or leaves the i_count unchanged *)
Lemma rule_3_subtracts_3_or_0 : forall (n : nat) (l : list MIU),
  i_count (rule_3 n l) = i_count l \/
  i_count (rule_3 n l) + 3 = i_count l.
Proof.
  intros n l.
  unfold rule_3.
  case_eq (list_eqb MIU_eqb (take_n 3 (drop_n n l)) [I; I; I]).
  - intros.
    right.
    rewrite i_count_plus_mor.
    rewrite i_count_plus_mor.
    simpl (i_count [U]).
    replace (0 + i_count (drop_n (n + 3) l)) with (i_count (drop_n (n + 3) l)) by lia.
    replace (i_count (take_n n l) + i_count (drop_n (n + 3) l) + 3) with (i_count (take_n n l) + (i_count (drop_n (n + 3) l) + 3)) by lia.
    replace (i_count (drop_n (n + 3) l) + 3) with (3 + i_count (drop_n (n + 3) l)) by lia.
    replace (3) with (i_count [I; I; I]) at 1 by reflexivity.
    rewrite <- (i_count_plus_mor).
    replace ([I; I; I] ++ drop_n (n + 3) l) with (drop_n n l).
    + rewrite <- (i_count_plus_mor).
      rewrite take_n_app_drop_n_id.
      reflexivity.
    + assert ([I; I; I] = take_n 3 (drop_n n l)).
      {
        apply list_eqb_eq in H.
        - symmetry.
          apply H.
        - intros.
          apply MIU_eqb_spec.
      }
      rewrite H0. clear H0.
      assert (drop_n (n + 3) l = drop_n 3 (drop_n n l)).
      {
        rewrite drop_m_drop_n_id.
        replace (n + 3) with (3 + n) by lia.
        reflexivity.
      }
      rewrite H0. clear H0.
      rewrite take_n_app_drop_n_id.
      reflexivity.
  - intros.
    left.
    reflexivity.
Qed.

Lemma rule_3_preserves_invariant : forall (n : nat), forall l,
  ((i_count l) mod 3 =? 0) =
  ((i_count (rule_3 n l)) mod 3 =? 0).
Proof.
  intros.
  pose proof (rule_3_subtracts_3_or_0 n l).
  destruct H.
  - rewrite H.
    reflexivity.
  - rewrite <- H. clear H.
    rewrite Nat.Div0.add_mod.
    rewrite Nat.Div0.mod_same.
    rewrite Nat.add_0_r.
    rewrite Nat.Div0.mod_mod.
    reflexivity.
Qed.

Lemma rule_4_preserves_i_count : forall (n : nat), forall l, i_count l = i_count (rule_4 n l).
Proof.
  intros n l.
  unfold rule_4.
  case_eq (list_eqb MIU_eqb (take_n 2 (drop_n n l)) [U; U]).
  - intros.
    rewrite i_count_plus_mor.
    replace (i_count (drop_n (n + 2) l)) with (0 + i_count (drop_n (n + 2) l)) by lia.
    replace 0 with (i_count [U; U]) at 1 by reflexivity.
    rewrite <- i_count_plus_mor.
    replace ([U; U]) with (take_n 2 (drop_n n l)).
    + assert (drop_n (n + 2) l = drop_n 2 (drop_n n l)).
      {
        rewrite drop_m_drop_n_id.
        replace (n + 2) with (2 + n) by lia.
        reflexivity.
      }
      rewrite H0. clear H0.
      rewrite take_n_app_drop_n_id.
      rewrite <- i_count_plus_mor.
      rewrite take_n_app_drop_n_id.
      reflexivity.
    + apply list_eqb_eq in H.
      * apply H.
      * intros.
        apply MIU_eqb_spec.
  - intros.
    reflexivity.
Qed.

(* We then conclude that every move preserves the invariant: *)
Lemma move_preserves_invariant : forall m l,
  ((i_count l) mod 3 =? 0) =
  ((i_count (apply m l)) mod 3 =? 0).
Proof.
  intros m l.
  destruct m.
  - rewrite rule_1_preserves_i_count. reflexivity.
  - rewrite rule_2_preserves_invariant. reflexivity.
  - rewrite (rule_3_preserves_invariant n). reflexivity.
  - rewrite (rule_4_preserves_i_count n). reflexivity.
Qed.

(* In our system the initial string is [M; I]. Notice that i_count [M; I] = 1,
   and 1 is not divisible by 3. *)
Lemma initial_invariant: ((i_count [I]) mod 3 =? 0) = false.
Proof.
  simpl.
  reflexivity.
Qed.

(* By induction on a sequence of moves, the invariant is maintained. *)
Lemma invariant_moves : forall ms, ((i_count (fold_right apply [I] ms)) mod 3 =? 0) = false.
Proof.
  intros.
  induction ms.
  - simpl; apply initial_invariant.
  - replace (fold_right apply [I] (a :: ms)) with (apply a (fold_right apply [I] (ms))) by reflexivity.
    rewrite <- (move_preserves_invariant a (fold_right apply [I] ms)).
    apply IHms.
Qed.

(******************************************************************************)
(* Final theorem: No solution exists *)

Definition no_solution_exists_proof : ~ (exists ms : list Move, fold_right apply [I] ms = [U])
  := fun H : exists ms : list Move, fold_right apply [I] ms = [U] =>
      match H with
        | ex_intro _ ms property =>
                 let invariant : (i_count (fold_right apply [I] ms) mod 3 =? 0) = false
                        := invariant_moves ms
              in let assumed : (i_count [U] mod 3 =? 0) = false
                        := eq_ind (fold_right apply [I] ms) (fun l : list MIU => (i_count l mod 3 =? 0) = false) invariant [U] property
              in let absurd_eq : true = false
                        := assumed
              in let absurd : False
                        := eq_ind true (fun e : bool => if e then True else False) Logic.I false absurd_eq
              in absurd
      end.

Theorem no_solution_exists : ~ exists (ms : list Move), fold_right apply [I] ms = [U].
Proof.
  exact (no_solution_exists_proof).
Qed.
