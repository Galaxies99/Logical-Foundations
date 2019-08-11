(* Chap 9 ProofObjects *)
(* The Curry-Howard Correspondence *)
Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.

Print even.

Check ev_SS.

Print ev_4.

Check (ev_SS 2 (ev_SS 0 ev_0)).

Theorem ev_4': even 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

(* Chap 9.1 Proof Scripts *)
Theorem ev_4'': even 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Definition ev_4''': even 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Print ev_4.
Print ev_4'.
Print ev_4''.
Print ev_4'''.

Theorem ev_8: even 8.
Proof.
  apply (ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))).
Qed.

Definition ev_8': even 8 :=
  (ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))).

(* Chap 9.2 Quantifiers, Implications, Functions *)
Theorem ev_plus4: forall n, even n -> even (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4': forall n, even n -> even (4 + n) :=
  fun (n: nat) => fun (H: even n) => ev_SS (S (S n)) (ev_SS n H).

Definition ev_plus2: Prop :=
  forall n, forall (E: even n), even (n + 2).

Definition ev_plus2': Prop :=
  forall n, forall (_: even n), even (n + 2).

Definition ev_plus2'': Prop :=
  forall n, even n -> even (n + 2).

(* Chap 9.3 Programming with Tactics *)
Definition add1: nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n.
Show Proof.
Defined.

Print add1.

(* Chap 9.4 Logical Connectives as Inductive Types *)
Module Props.

(* Chap 9.4.1 Conjunction *)
Module And.

Inductive and (P Q: Prop) : Prop :=
  | conj: P -> Q -> and P Q.

End And.

Print prod.

Lemma and_comm: forall P Q: Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.

Definition and_comm'_aux P Q (H: P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q: P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

(* Exercise conj_fact *)
Definition conj_fact: forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R: Prop) (H1: P /\ Q) (H2: Q /\ R) =>
  match H1, H2 with
  | conj p q, conj q' r => conj p r
  end.

(* Chap 9.4.2 Disjunction *)
Module Or.

Inductive or (P Q: Prop) : Prop :=
  | or_introl: P -> or P Q
  | or_intror: Q -> or P Q.

End Or.

(* Exercise op_commut'' *)
Definition or_comm: forall P Q, P \/ Q -> Q \/ P :=
  fun (P Q: Prop) (H: P \/ Q) =>
  match H with
  | or_introl P => or_intror P
  | or_intror P => or_introl P
  end.

(* Chap 9.4.3 Existential Quantification *)
Module Ex.

Inductive ex {A: Type} (P: A -> Prop) :=
  | ex_intro: forall x: A, P x -> ex P.

End Ex.

Check ex (fun n => even n).

Definition some_nat_is_even: exists n, even n :=
  ex_intro even 4 (ev_SS 2 (ev_SS 0 ev_0)).

(* Exercise ex_ev_Sn *)
Definition ex_ev_Sn: ex (fun n => even (S n)) :=
  ex_intro (fun n => even (S n)) 1 (ev_SS 0 ev_0).

(* Chap 9.4.4 True and False *)
Inductive True : Prop :=
  | I: True.

Inductive False: Prop := .

End Props.

(* Chap 9.5 Equality *)
Module MyEquality.

Inductive eq {X: Type}: X -> X -> Prop :=
  | eq_refl: forall x, eq x x.

Notation "x == y" := (eq x y)
  (at level 70, no associativity) : type_scope.

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.

Definition four': 2 + 2 == 1 + 3 := eq_refl 4.

Definition singleton: forall (X: Type) (x: X),
  [] ++ [x] == x :: [] :=
  fun (X: Type) (x: X) => eq_refl [x].

(* Exercise equality__leibniz_equality *)
Lemma equality__leibniz_equality: forall (X: Type) (x y: X),
  x == y -> forall P: X -> Prop, P x -> P y.
Proof.
  intros X x y.
  intros.
  inversion H.
  rewrite H2 in H0.
  apply H0.
Qed.

(* Exercise leibniz_equality__equality *)
Lemma leibniz_equality__equality: forall (X: Type) (x y: X),
  (forall P: X -> Prop, P x -> P y) -> x == y.
Proof.
  intros.
  assert(I: x = x -> x = y).
  { apply H. }
  replace y with x.
  apply eq_refl.
  apply I.
  reflexivity.
Qed.

End MyEquality.
