(* Chap 2 Sort *)
From VFA Require Import Perm.

(* Chap 2.1 The Insertion-Sort Program *)
Fixpoint insert (i: nat) (l: list nat) :=
  match l with
  | nil => i :: nil
  | h :: t => if i <=? h then i :: h :: t
              else h :: (insert i t)
  end.

Fixpoint sort (l: list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => insert h (sort t)
  end.

Example sort_pi: sort [3;1;4;1;5;9;2;6;5;3;5] 
  = [1;1;2;3;3;4;5;5;5;6;9].
Proof. reflexivity. Qed.

Eval compute in insert 7 [1; 3; 4; 8; 12; 14; 18].

(* Chap 2.2 Specification of Correctness *)
Inductive sorted: list nat -> Prop :=
  | sorted_nil: sorted nil
  | sorted_1: forall x, sorted (x :: nil)
  | sorted_cons: forall x y l, x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Definition sorted' (al: list nat) :=
  forall i j, i < j < length al -> nth i al 0 <= nth j al 0.

Definition is_a_sorting_algorithm (f: list nat -> list nat) :=
  forall al, Permutation al (f al) /\ sorted (f al).

(* Chap 2.3 Proof of Correctness *)
(* Exercise insert_perm *)
Lemma insert_perm: forall x l, Permutation (x :: l) (insert x l).
Proof.
  intros.
  induction l; auto.
  simpl.
  bdestruct (x <=? a).
  - auto.
  - rewrite perm_swap.
    apply perm_skip, IHl.
Qed.

(* Exercise sort_perm *)
Lemma insert_same_perm: forall a l1 l2,
  Permutation l1 l2 ->
  Permutation (insert a l1) (insert a l2).
Proof.
  intros.
  assert (Permutation (a :: l1) (insert a l1)). { apply insert_perm. }
  assert (Permutation (a :: l2) (insert a l2)). { apply insert_perm. }
  apply Permutation_sym in H0.
  apply Permutation_trans with (a :: l1).
  apply H0.
  apply Permutation_trans with (a :: l2).
  apply perm_skip, H.
  apply H1.
Qed.

Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
  intros.
  induction l; auto.
  simpl.
  apply Permutation_trans with (l' := insert a l).
  apply insert_perm.
  apply insert_same_perm.
  apply IHl.
Qed.

(* Exercise insert_sorted *)
Lemma insert_sorted: forall a l, sorted l -> sorted (insert a l).
Proof.
  intros.
  induction H.
  - simpl. constructor.
  - simpl. 
    bdestruct (a <=? x); constructor; 
    try constructor;
    try omega; auto.
  - simpl in *.
    bdestruct (a <=? x).
    + bdestruct (a <=? y);
      constructor; auto;
      constructor; auto.
    + bdestruct (a <=? y);
      constructor; try omega; auto.
Qed.

(* Exercise sort_sorted *)
Theorem sort_sorted: forall l, sorted (sort l).
Proof.
  induction l; try constructor.
  simpl. apply insert_sorted.
  apply IHl.
Qed.

Theorem insertion_sort_correct:
  is_a_sorting_algorithm sort.
Proof.
  split.
  apply sort_perm.
  apply sort_sorted.
Qed.

(* Chap 2.4 Making Sure the Specification is Right *)
(* Exercise sorted_sorted' *)
Lemma sorted_sorted': forall al, sorted al -> sorted' al.
Proof.
  intros.
  unfold sorted'.
  induction H;
  try (intros; simpl in *;
       assert (i = 0 /\ j = 0) by omega;
       destruct H0;
       rewrite H0, H1;
       auto).
  destruct i, j.
  + auto.
  + intros. 
    apply le_trans with y; auto.
    destruct j; auto.
    simpl.
    apply IHsorted with (i := 0) (j := S j).
    simpl in *. omega.
  + omega.
  + intros.
    apply IHsorted with (i := i) (j := j).
    simpl in *. omega.
Qed.

(* Exercise sorted'_sorted *)
Lemma sorted'_sorted: forall al, sorted' al -> sorted al.
Proof.
  intros al.
  induction al; try constructor.
  intros. unfold sorted' in *.
  destruct al; constructor.
  - apply H with (i := 0) (j := 1).
    simpl. omega.
  - apply IHal. intros.
    apply H with (i := S i) (j := S j).
    simpl in *. omega.
Qed.

(* Chap 2.5 Proving Correctness from the Alternate Spec *)
(* Exercuse Forall_nth *)
Lemma Forall_nth:
  forall {A: Type} (P: A -> Prop) d (al: list A),
    Forall P al <-> (forall i, i < length al -> P (nth i al d)).
Proof.
  (* Fill in here *)
Admitted.

(* Exercise insert_sorted' *)
Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
  (* Fill in here *)
Admitted.

(* Exercise sort_sorted' *)
Theorem sort_sorted': forall l, sorted' (sort l).
Proof.
  (* Fill in here *)
Admitted.

