(* Chap 8 Maps *)
(* Chap 8.1 The Coq Standard Library *)
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

(* Chap 8.2 Identifiers *)
Definition eqb_string (x y: string) : bool :=
  if string_dec x y then true else false.

Theorem eqb_string_refl: forall s: string,
  true = eqb_string s s.
Proof.
  intros. unfold eqb_string.
  destruct (string_dec s s).
  - reflexivity.
  - destruct n. reflexivity.
Qed.

Theorem eqb_string_true_iff: forall x y: string,
  eqb_string x y = true <-> x = y.
Proof.
  intros.
  unfold eqb_string.
  destruct (string_dec x y).
  - subst. split. reflexivity. reflexivity.
  - split.
    + intros contra. discriminate.
    + intros H. rewrite H in n. destruct n. reflexivity.
Qed.

Theorem eqb_string_false_iff: forall x y: string,
  eqb_string x y = false <-> x <> y.
Proof.
  intros.
  rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false.
  reflexivity.
Qed.

Theorem false_eqb_string: forall x y: string,
  x <> y -> eqb_string x y = false.
Proof.
  intros x y.
  apply eqb_string_false_iff.
Qed.

(* Chap 8.3 Total Maps *)
Definition total_map (A: Type) := string -> A.

Definition t_empty {A: Type} (v: A): total_map A :=
  (fun _ => v).

Definition t_update {A: Type} (m: total_map A) (x: string) (v: A) :=
  fun x' => if eqb_string x x' then v else m x'.

Definition examplemap1 := t_update (t_update (t_empty false) "foo" true) "bar" true.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

Definition examplemap' :=
  ( "bar" !-> true; "foo" !-> true; _ !-> false ).

(* Exercise t_apply_empty *)
Lemma t_apply_empty: forall (A: Type) (x: string) (v: A),
  (_ !-> v) x = v.
Proof.
  intros.
  unfold t_empty.
  reflexivity.
Qed.

(* Exercise t_update_eq *)
Lemma t_update_eq: forall (A: Type) (m: total_map A) x v,
  (x !-> v; m) x = v.
Proof.
  intros.
  unfold t_update.
  rewrite <- eqb_string_refl.
  reflexivity.
Qed.

(* Exercise t_update_neq *)
Theorem t_update_neq: forall (A: Type) (m: total_map A) x1 x2 v,
  x1 <> x2 -> (x1 !-> v; m) x2 = m x2.
Proof.
  intros. unfold t_update.
  apply false_eqb_string in H.
  rewrite H.
  reflexivity.
Qed.

(* Exercise t_update_shadow *)
Lemma t_update_shadow: forall (A: Type) (m: total_map A) x v1 v2,
  (x !-> v2; x !-> v1; m) = (x !-> v2; m).
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros.
  destruct (eqb_string x x0) eqn: Hstr.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise eqb_stringP *)
Lemma eqb_stringP: forall x y: string,
  reflect (x = y) (eqb_string x y).
Proof.
  intros. 
  apply iff_reflect.
  symmetry. apply eqb_string_true_iff.
Qed.

(* Exercise t_update_same *)
Theorem t_update_same: forall (A: Type) (m: total_map A) x,
  (x !-> m x; m) = m.
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros.
  destruct (eqb_stringP x x0).
  - rewrite e. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute: forall (A: Type) (m: total_map A) v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1; x2 !-> v2; m) = (x2 !-> v2; x1 !-> v1; m).
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality_dep.
  intros.
  destruct (eqb_stringP x1 x).
  - destruct (eqb_stringP x2 x).
    + rewrite e, e0 in H. destruct H. reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

(* Chap 8.4 Partial maps *)
Definition partial_map (A: Type) := total_map (option A).

Definition empty {A: Type}: partial_map A :=
  t_empty None.

Definition update {A: Type} (m: partial_map A) (x: string) (v: A) :=
  (x !-> Some v; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

Example examplemap2 :=
  ("Church" |-> true; "Turing" |-> false).

Lemma apply_empty: forall (A: Type) (x: string),
  @empty A x = None.
Proof.
  intros.
  unfold empty.
  apply t_apply_empty.
Qed.

Lemma update_eq: forall (A: Type) (m: partial_map A) x v,
  (x |-> v; m) x = Some v.
Proof.
  intros.
  unfold update.
  apply t_update_eq.
Qed.

Theorem update_neq: forall (A: Type) (m: partial_map A) x1 x2 v,
  x2 <> x1 -> (x2 |-> v; m) x1 = m x1.
Proof.
  intros A m x1 x2 v.
  unfold update.
  apply t_update_neq.
Qed.

Lemma update_shadow: forall (A: Type) (m: partial_map A) x v1 v2,
  (x |-> v2; x |-> v1; m) = (x |-> v2; m).
Proof.
  intros A m x v1 v2.
  unfold update.
  apply t_update_shadow.
Qed.

Theorem update_same: forall (A: Type) (m: partial_map A) x v,
  m x = Some v -> (x |-> v; m) = m.
Proof.
  intros A m x v H.
  unfold update.
  rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute: forall (A: Type) (m: partial_map A) x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1; x2 |-> v2; m) = (x2 |-> v2; x1 |-> v1; m).
Proof.
  intros A m x1 x2 v1 v2.
  unfold update.
  apply t_update_permute.
Qed.
