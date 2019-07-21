(* Chap 2 Proof by Induction *)
From SRC Require Export Basics.

(* Chap 2.1 Proof by Induction *)

Theorem plus_n_O: forall n: nat, n = n + 0.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem minus_diag: forall n,
  minus n n = 0.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

(* Exercise basic_induction *)

Theorem mult_0_r: forall n: nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m: nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_comm : forall n m: nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n.
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p: nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

(* Exercise double_plus *)
Fixpoint double (n: nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus: forall n, double n = n + n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. rewrite -> plus_n_Sm. reflexivity.
Qed.

(* Exercise evenb_S *)
Theorem evenb_S: forall n: nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n.
  induction n.
  - reflexivity.
  - rewrite IHn. 
    rewrite negb_involutive.
    reflexivity.
Qed.

(* Chap 2.2 Proofs Within Proofs *)
Theorem mult_0_plus' : forall n m: nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange: forall n m p q: nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n). 
  {
    rewrite -> plus_comm.
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.

(* Chap 2.3 Formal vs. Informal Proof *)
(* Skipped *)


