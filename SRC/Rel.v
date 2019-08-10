(* Chap 11 Rel *)
(* PROPERTIES OF RELATIONS *)
Set Warnings "-notation-overridden,-parsing".
From SRC Require Export IndProp.

(* Chap 11.1 Relations *)
Definition relation (X: Type) := X -> X -> Prop.

Print le.
Check le: nat -> nat -> Prop.
Check le: relation nat.

(* Chap 11.2 Basic Properties *)
(* Chap 11.2.1 Partial Functions *)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2: X, R x y1 -> R x y2 -> y1 = y2.

Check next_nat : relation nat.

Theorem next_nat_partial_function:
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros.
  inversion H.
  inversion H0.
  reflexivity.
Qed.

Theorem le_not_a_partial_function:
  ~ (partial_function le).
Proof.
  unfold not.
  unfold partial_function.
  intros.
  assert (0 = 1) as Nonsense.
  { apply H with (x := 0).
    apply le_n.
    apply le_S, le_n. }
  discriminate Nonsense.
Qed.

(* Exercise total_relation_not_partial *)
Print total_relation.

Theorem total_relation_not_partial:
  ~ (partial_function total_relation).
Proof.
  unfold not. unfold partial_function.
  intros.
  assert (0 = 1) as Nonsense.
  { apply H with (x := 1).
    apply re_S_0, re_0_0.
    apply re_n_S, re_S_0, re_0_0.
  }
  discriminate.
Qed.

(* Exercise empty_relation_partial *)
Print empty_relation.

Theorem empty_relation_partial:
  partial_function empty_relation.
Proof.
  unfold partial_function.
  intros.
  inversion H.
Qed.

(* Chap 11.2.2 Reflexive Relations *)
Definition reflexive {X: Type} (R: relation X) :=
  forall a: X, R a a.

Theorem le_reflexive:
  reflexive le.
Proof.
  unfold reflexive.
  intros.
  apply le_n.
Qed.

(* Chap 11.2.3 Transitive Relations *)
Definition transitive {X: Type} (R: relation X) :=
  forall a b c: X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans:
  transitive le.
Proof.
  unfold transitive.
  intros.
  induction H0.
  - apply H.
  - apply le_S, IHle.
Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold transitive.
  intros.
  unfold lt in *.
  apply le_S in H.
  apply (le_trans (S a) (S b) c).
  - apply H.
  - apply H0.
Qed.

(* Exercise le_trans_hard_way *)
Theorem lt_trans':
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  - apply le_S, Hnm.
  - apply le_S, IHHm'o.
Qed.

(* Exercise lt_trans'' *)
Theorem lt_trans'':
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  - inversion Hmo.
  - apply le_S.
    inversion Hmo.
    + rewrite <- H0, Hnm. 
      apply le_n.
    + apply IHo', H0.
Qed.

Theorem le_Sn_le: forall n m, S n <= m -> n <= m.
Proof.
  intros.
  apply le_trans with (S n).
  - apply le_S, le_n.
  - apply H.
Qed.

(* Exercise le_S_n *)
Theorem le_S_n: forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros.
  inversion H.
  - apply le_n.
  - apply le_Sn_le in H1. apply H1.
Qed.

(* Exercise le_Sn_n *)
Theorem le_Sn_n: forall n,
  ~ (S n <= n).
Proof.
  unfold not.
  intros.
  induction n.
  - inversion H.
  - apply IHn. apply le_S_n, H.
Qed.

(* Chap 11.2.4 Symmetric and Antisymmetric Relations *)
Definition symmetric {X: Type} (R: relation X) :=
  forall a b: X, (R a b) -> (R b a).

(* Exercise le_not_symmetric *)
Theorem le_not_symmetric:
  ~ (symmetric le).
Proof.
  unfold symmetric.
  unfold not. 
  intros.
  assert (1 <= 0) as Nonsense.
  { apply (H 0 1). apply le_S, le_n. }
  inversion Nonsense.
Qed.

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b: X, (R a b) -> (R b a) -> a = b.

(* Exercise le_antisymmetric *)
Theorem le_antisymmetric:
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros a.
  induction a.
  - intros. inversion H.
    + reflexivity.
    + inversion H0. rewrite H3 in H2. discriminate.
  - intros. inversion H.
    + reflexivity.
    + rewrite <- H2 in H0. inversion H0.
      * reflexivity.
      * apply f_equal. apply IHa.
        rewrite <- H2 in H.
        apply le_S_n, H.
        apply le_S_n, H0.
Qed.

(* Exercise le_step *)
Theorem le_step: forall n m p,
  n < m -> m <= S p -> n <= p.
Proof.  
  unfold lt.
  intros.
  apply le_S_n.
  apply (le_trans (S n) m (S p)).
  apply H.
  apply H0.
Qed.

(* Chap 11.2.5 Equivalence Relations *)
Definition equivalence {X: Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(* Chap 11.2.6 Partial Orders and Preorders *)
Definition order {X: Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X: Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order:
  order le.
Proof.
  unfold order.
  split.
  - apply le_reflexive.
  - split.
    + apply le_antisymmetric.
    + apply le_trans.
Qed.

(* Chap 11.3 Reflexive, Transitive Closure *)
Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
  | rt_step x y (H: R x y): clos_refl_trans R x y
  | rt_refl x: clos_refl_trans R x x
  | rt_trans x y z (Hxy: clos_refl_trans R x y) (Hyz: clos_refl_trans R y z):
      clos_refl_trans R x z.

Theorem next_nat_closure_is_le: forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros. split.
  - intros.
    induction H.
    + apply rt_refl.
    + apply rt_trans with m.
      apply IHle.
      apply rt_step.
      apply nn.
  - intros.
    induction H.
    + inversion H. apply le_S, le_n.
    + apply le_n.
    + apply (le_trans x y z).
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2.
Qed.

Inductive clos_refl_trans_1n {A: Type} (R: relation A) (x: A): A -> Prop :=
  | rt1n_refl: clos_refl_trans_1n R x x
  | rt1n_trans (y z: A) (Hxy: R x y) (Hrest: clos_refl_trans_1n R y z):
      clos_refl_trans_1n R x z.

Lemma rsc_R: forall (X: Type) (R: relation X) (x y: X),
  R x y -> clos_refl_trans_1n R x y.
Proof.
  intros.
  apply (rt1n_trans R x y y).
  apply H.
  apply rt1n_refl.
Qed.

(* Exercise rsc_trans *)
Lemma rsc_trans:
  forall (X: Type) (R: relation X) (x y z: X),
    clos_refl_trans_1n R x y -> clos_refl_trans_1n R y z ->
    clos_refl_trans_1n R x z.
Proof.
  intros.
  induction H.
  - apply H0.
  - apply (rt1n_trans R x y z).
    apply Hxy.
    apply IHclos_refl_trans_1n, H0.
Qed.

(* Exercise rtc_rsc_coincide *)
Theorem rtc_rsc_coincide:
  forall (X: Type) (R: relation X) (x y: X),
    clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  intros. split.
  - intros.
    induction H.
    + apply rsc_R, H.
    + apply rt1n_refl.
    + apply (rsc_trans X R x y z).
      apply IHclos_refl_trans1. apply IHclos_refl_trans2.
  - intros.
    induction H.
    + apply rt_refl.
    + apply (rt_trans R x y z).
      apply rt_step.
      apply Hxy.
      apply IHclos_refl_trans_1n.
Qed.