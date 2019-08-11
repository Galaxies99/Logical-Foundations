(* Chap 10 IndPrinciples *)
Set Warnings "-notation-overridden,-parsing".
From LF Require Export ProofObjects.

(* Chap 10.1 Basics *)
Check nat_ind.

Theorem mult_0_r': forall n: nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros. simpl. apply H.
Qed.

(* Exercise plus_one_r' *)
Theorem plus_one_r': forall n: nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros. simpl. rewrite H. reflexivity.
Qed.

Inductive yesno: Type :=
  | yes
  | no.

Check yesno_ind.

(* Exercise rgb *)
Inductive rgb : Type :=
  | red
  | green
  | blue.

(* rgb_ind: forall P: rgb -> Prop, P red -> P green -> P blue -> forall y: rgb, P y *)
Check rgb_ind.

Inductive natlist : Type :=
  | nnil
  | ncons (n: nat) (l: natlist).

Check natlist_ind.

(* Exercise natlist1 *)
Inductive natlist1 : Type :=
  | nnil1
  | nsnoc1 (l: natlist1) (n: nat).
(*
  natlist1_ind: 
  forall P : natlist1 -> Prop,
    P nnil1 ->
    (forall l : natlist1, P l -> forall n : nat, P (nsnoc1 l n)) ->
    forall n : natlist1, P n
*)
Check natlist1_ind.

(* Exercise byntree_ind *)
Inductive byntree : Type :=
  | bempty
  | bleaf (yn: yesno)
  | nbranch (yn: yesno) (t1 t2: byntree).

(*
  byntree_ind:
  forall P : byntree -> Prop,
  P bempty ->
  (forall (yn: yesno), P (bleaf yn))
  (forall (yn: yesno) (t1: byntree), P t1 ->
   forall (t2: byntree), P t2 -> P (nbranch yn t1 t2)) ->
  forall b: byntree P b
*)

Check byntree_ind.

(* Exercise ex_set *)
Inductive ExSet : Type :=
  | con1 (b: bool)
  | con2 (n: nat) (e: ExSet).

Check ExSet_ind.

(* Chap 10.2 Polymorphism *)
Check list_ind.

(* Exercise tree *)
Inductive tree (X: Type) : Type :=
  | leaf (x: X)
  | node (t1 t2: tree X).

(*
  tree_ind:
  forall (X: Type) (P: tree X -> Prop),
  (forall (x: X), P (leaf X x)) ->
  (forall (x: X) (t1: tree X) -> P t1 ->
   forall (t2: tree X) -> P t2 ->
   P (node X t1 t2)) ->
  (forall t: tree X, P t)
*)
Check tree_ind.

(* Exercise mytype *)
Inductive mytype (X: Type) : Type :=
  | constr1 (x: X)
  | constr2 (n: nat)
  | constr3 (m: mytype X) (n: nat).

Check mytype_ind.

(* Exercise foo *)
Inductive foo (X Y: Type) : Type :=
  | bar (x: X)
  | baz (y: Y)
  | quux (f1: nat -> foo X Y).

Check foo_ind.

(* Exercise foo' *)
Inductive foo' (X: Type) : Type :=
  | C1 (l: list X) (f: foo' X)
  | C2.

(*
  forall (X: Type) (P: foo' X -> Prop),
  ( forall (l: list X) (f: foo' X),
    P f -> P (C1 X l f) ) ->
  P (C2 X) ->
  forall f1: foo' X, P f1
*)
Check foo'_ind.

(* Chap 10.3 Induction Hypotheses *)
Definition P_m0r (n: nat) : Prop :=
  n * 0 = 0.

Definition P_m0r': nat -> Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'': forall n: nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n IHn.
    unfold P_m0r in *.
    simpl.
    apply IHn.
Qed.

(* Chap 10.4 More on the induction Tactic *)
Theorem plus_assoc': forall n m p: nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm': forall n m: nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - intros m. rewrite <- plus_n_O. reflexivity.
  - intros m. simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem plus_comm'': forall n m: nat,
  n + m = m + n.
Proof.
  induction m as [| m'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite <- IHm'. rewrite <- plus_n_Sm. reflexivity.
Qed.

(* Exercise plus_explicit_prop *)
Check plus_assoc.
Definition plus_assoc_def (n m p: nat) : Prop :=
  n + (m + p) = n + m + p.

Theorem plus_assoc'': forall (n m p: nat), plus_assoc_def n m p.
Proof.
  intros.
  induction n.
  - reflexivity.
  - unfold plus_assoc_def in *. simpl. rewrite -> IHn. reflexivity.
Qed.

Definition plus_comm_def (n m: nat) : Prop :=
  n + m = m + n.

Theorem plus_comm''': forall n m: nat,
  plus_comm_def n m.
Proof.
  induction n.
  - unfold plus_comm_def. intros. rewrite <- plus_n_O. reflexivity.
  - unfold plus_comm_def in *. intros. simpl. rewrite IHn. rewrite <- plus_n_Sm. reflexivity.
Qed.

(* Chap 10.5 Induction Principles in Prop *)
Check even_ind.

Theorem ev_ev': forall n, even n -> even' n.
Proof.
  apply even_ind.
  - apply even'_0.
  - intros m Hm IH.
    apply (even'_sum 2 m).
    + apply even'_2.
    + apply IH.
Qed.

Inductive le (n: nat) : nat -> Prop :=
  | le_n: le n n
  | le_S m (H: le n m): le n (S m).

Notation "m <= n" := (le m n).

(* Chap 10.6 Formal vs. Informal Proofs by Induction *)
(* Skipped *)