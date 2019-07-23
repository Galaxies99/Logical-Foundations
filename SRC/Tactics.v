(* Chap 5 Tactics *)
Set Warnings "-notation-overridden,-parsing".
From SRC Require Export Poly.

(* Chap 5.1 The apply Tactic *)
Theorem silly1: forall (n m o p: nat),
  n = m -> [n;o] = [n;p] -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.
(* Note: 
   here, we could finish with "rewrite -> eq2. reflexivity." as we have done 
   several times before. We can achieve the same effect in a single step by 
   using the apply tactic instead
   if the statement being applied is an implication, then the premises of this
   implication will be added to the list of subgoals needing to be proved. *)

Theorem silly2: forall (n m o p: nat),
  n = m -> (forall (q r: nat), q = r -> [q;o] = [r;p]) -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.
Qed.

Theorem silly2a: forall (n m: nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. 
Qed.

(* Exercise silly_ex *)
Theorem silly_ex: (forall n, evenb n = true -> oddb (S n) = true) -> evenb 3 = true -> oddb 4 = true.
Proof.
  intros eq1 eq2.
  apply eq1. apply eq2.
Qed.

Theorem silly3: forall (n: nat), true = (n =? 5) -> (S (S n)) =? 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H.
Qed.

Theorem rev_exercise1: forall (l l': list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros l l' H.
  rewrite -> H.
  symmetry.
  apply rev_involutive.
Qed.

(* Chap 5.2 The apply with Tactic *)
Example trans_eq_example : forall (a b c d e f: nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. 
Qed.

Theorem trans_eq: forall (X: Type) (n m o: X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o.
  intros H1 H2.
  rewrite -> H1, H2.
  reflexivity.
Qed.

Example trans_eq_example': forall (a b c d e f: nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c;d]).
  apply eq1. apply eq2.
Qed.

(* Exercise apply_with_exercise *)
Example trans_eq_exercise: forall (n m o p: nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with (m := m).
  apply eq2.
  apply eq1.
Qed.

(* Chap 5.3 The injection and discriminate Tactics *)
Theorem S_injective: forall (n m: nat),
  S n = S m -> n = m.
Proof.
  intros n m H.
  assert (H2: n = pred (S n)).
  { reflexivity. }
  rewrite -> H2.
  rewrite -> H.
  reflexivity.
Qed.

Theorem S_injective': forall (n m: nat),
  S n = S m -> n = m.
Proof.
  intros n m H.
  injection H.
  intros H2.
  apply H2.
Qed.
(* Note: By writing injection H at this point, we are asking Coq to generate
   all equations that it can infer from H using the injectivity of constructors.
   Each such equation is added as a premise to the goal. *) 

Theorem injection_ex1: forall (n m o: nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H.
  injection H.
  intros H2 H3.
  rewrite -> H2, H3.
  reflexivity.
Qed.

Theorem injection_ex2: forall (n m: nat),
  [n] = [m] -> n = m.
Proof.
  intros n m H.
  injection H as H'.
  apply H'.
Qed.

(* Exercise injection_ex3 *)
Example injection_ex3: forall (X: Type) (x y z: X) (l j: list X),
  x :: y :: l = z :: j -> y :: l = x :: j -> x = z.
Proof.
  intros X x y z l j H1 H2.
  injection H1 as H3 H4.
  apply H3.
Qed.

Theorem eqb_0_l: forall n: nat,
  0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n.
  - intros H. reflexivity.
  - simpl. intros H. discriminate H.
Qed.
(* Note: If we use discriminate on this hypothesis, Coq confirms that 
   the subgoal we are working on is impossible and removes it from further 
   consideration. *)

Theorem discriminate_ex1: forall (n: nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n H.
  discriminate H.
Qed.

Theorem discriminate_ex2: forall (n m: nat),
  false = true -> [n] = [m].
Proof.
  intros n m H.
  discriminate H.
Qed.

(* Exercise discriminate_ex3 *)
Example discriminate_ex3: forall (X: Type) (x y z: X) (l j: list X),
  x :: y :: l = [] -> x = z.
Proof.
  intros X x y z l j H.
  discriminate H.
Qed.

Theorem f_equal: forall (A B: Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof.
  intros A B f x y eq.
  rewrite eq.
  reflexivity.
Qed.

(* Chap 5.4 Using Tactics on Hypotheses *)
Theorem S_inj: forall (n m: nat) (b: bool),
  (S n) =? (S m) = b -> n =? m = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.

Theorem silly3': forall (n: nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H. 
  symmetry in H.
  apply H.
Qed.

(* Exercise plus_n_n_injective *)
Theorem plus_n_n_injective: forall n m,
  n + n = m + m -> n = m.
Proof.
  intros n.
  induction n.
  - simpl. intros m eq.
    destruct m.
    + reflexivity.
    + discriminate eq.
  - simpl. intros m eq.
    destruct m.
    + discriminate eq.
    + apply f_equal. apply IHn. 
      rewrite <- plus_n_Sm in eq. 
      rewrite <- plus_n_Sm in eq.
      injection eq as H.
      apply H.
Qed.

(* Chap 5.5 Varying the Induction Hypothesis *)
Theorem double_injective: forall n m,
  double n = double m -> n = m.
Proof.
  intros n. induction n.
  - simpl. intros m eq.
    destruct m.
    + reflexivity.
    + discriminate eq.
  - simpl. intros m eq.
    destruct m.
    + discriminate eq.
    + apply f_equal. apply IHn. injection eq as goal. apply goal.
Qed.
(* Note: sometimes, we should not intros everything at the beginning. *)

Theorem eqb_true: forall n m,
  n =? m = true -> n = m.
Proof.
  intros n.
  induction n.
  - intros m eq.
    destruct m.
    + reflexivity.
    + discriminate eq.
  - intros m eq.
    destruct m.
    + discriminate eq.
    + apply f_equal. apply IHn. simpl in eq. apply eq.
Qed.

Theorem double_injective_take2: forall n m,
  double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n. (* Note: put n back to the goal *)
  induction m.
  - intros n eq. destruct n.
    + reflexivity.
    + discriminate eq.
  - intros n eq. destruct n.
    + discriminate eq.
    + apply f_equal. apply IHm. injection eq as H. apply H.
Qed.

Theorem eqb_id_true: forall x y,
  eqb_id x y = true -> x = y.
Proof.
  intros m n. 
  destruct m as [m']. 
  destruct n as [n'].
  simpl. intros H.
  assert (H': m' = n'). { apply eqb_true. apply H. }
  rewrite H'. reflexivity.
Qed.

(* Exercise gen_dep_practice *)
Theorem nth_error_after_last: forall (n: nat) (X: Type) (l: list X),
  length l = n -> nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l.
  - intros n H. destruct n.
    + reflexivity.
    + discriminate H.
  - intros n H. destruct n.
    + discriminate H.
    + simpl. apply IHl. injection H as H'. apply H'.
Qed.

(* Chap 5.6 Unfolding Definitions *)
Definition square n := n * n.

Lemma square_mult: forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square. 
  rewrite -> mult_assoc, mult_assoc.
  assert (H: n * m * n = n * n * m). { rewrite -> mult_comm. rewrite -> mult_assoc. reflexivity. }
  rewrite H. reflexivity.
Qed.

Definition foo (x: nat) := 5.
Fact silly_fact_1: forall m, foo m + 1 = foo (m + 1) + 1.
Proof. 
  intros m.
  simpl.
  reflexivity. 
Qed.
(* Note: here simpl. has a function of unfold, but just for easy cases. *)

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2: forall m, bar m + 1 = bar (m + 1) + 1.
Proof. 
  intros m.
  simpl.
  unfold bar.
  destruct m.
  - reflexivity. 
  - reflexivity.
Qed.
(* Note: here simpl. does nothing! only unfold can do something useful. *)

(* Chap 5.7 Using destruct on Compound Expressions *)
Definition sillyfun (n: nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false: forall (n: nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3).
  - reflexivity.
  - destruct (n =? 5).
    + reflexivity.
    + reflexivity.
Qed.

(* Exercise combine_split *)
Theorem combine_split: forall X Y (l: list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [|p l].
  - intros l1 l2 H.
    injection H as H1 H2.
    rewrite <- H1.
    reflexivity.
  - intros l1 l2 H.
    destruct p as [x y].
    injection H as H1 H2.
    destruct (split l).
    * rewrite <- H1.
      rewrite <- H2.
      simpl.
      rewrite IHl.
      reflexivity.
      reflexivity.
Qed.

Definition sillyfun1 (n: nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd: forall (n: nat),
  sillyfun1 n = true -> oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn: Heqe3.
  - apply eqb_true in Heqe3. rewrite -> Heqe3. reflexivity.
  - destruct (n =? 5) eqn: Heqe5.
    + apply eqb_true in Heqe5. rewrite -> Heqe5. reflexivity.
    + discriminate eq.
Qed.

(* Exercise destruct_eqn_practice *)
Theorem bool_fn_applied_thrice: forall (f: bool -> bool) (b: bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f b) eqn: H1.
  - destruct b. 
    + rewrite H1. apply H1.
    + destruct (f true) eqn: H2.
      * apply H2.
      * apply H1.
  - destruct b.
    + destruct (f false) eqn: H2.
      * apply H1.
      * apply H2.
    + rewrite -> H1. apply H1.
Qed.

(* Chap 5.8 Review *)
(*
  intros: move hypotheses/variables from goal to context
  reflexivity: finish the proof (when the goal looks like e = e)
  apply: prove goal using a hypothesis, lemma, or constructor
  apply... in H: apply a hypothesis, lemma, or constructor to a hypothesis in the context
                (forward reasoning)
  apply... with...: explicitly specify values for variables that cannot be determined by 
                    pattern matching
  simpl: simplify computations in the goal
  simpl in H: ... or a hypothesis
  rewrite: use an equality hypothesis (or lemma) to rewrite the goal
  rewrite ... in H: ... or a hypothesis
  symmetry: changes a goal of the form t=u into u=t
  symmetry in H: changes a hypothesis of the form t=u into u=t
  unfold: replace a defined constant by its right-hand side in the goal
  unfold... in H: ... or a hypothesis
  destruct... as...: case analysis on values of inductively defined types
  destruct... eqn:...: specify the name of an equation to be added to the context, 
                       recording the result of the case analysis
  induction... as...: induction on values of inductively defined types
  injection: reason by injectivity on equalities between values of inductively defined types
  discriminate: reason by disjointness of constructors on equalities between values of 
                inductively defined types
  assert (H: e) (or assert (e) as H): introduce a "local lemma" e and call it H
  generalize dependent x: move the variable x (and anything else that depends on it) from 
                          the context back to an explicit hypothesis in the goal formula
*)

(* Chap 5.9 Additional Exercises *)
(* Exercise eqb_sym *)
From SRC Require Export Induction.

Theorem eqb_sym: forall (n m: nat),
  (n =? m) = (m =? n).
Proof.
  intros n m.
  destruct (n =? m) eqn: Heq.
  - apply eqb_true in Heq. 
    rewrite -> Heq. 
    apply eqb_refl.
  - destruct (m =? n) eqn: Heq2.
    + apply eqb_true in Heq2. 
      rewrite -> Heq2 in Heq. 
      rewrite <- eqb_refl in Heq.
      discriminate Heq.
    + reflexivity.
Qed.

(* Exercise eqb_sym_informal *)
(* Skipped *)

(* Exercise eqb_trans *)
Theorem eqb_trans: forall n m p,
  n =? m = true -> m =? p = true -> n =? p = true.
Proof.
  intros n m p H1 H2.
  apply eqb_true in H1.
  apply eqb_true in H2.
  rewrite <- H1 in H2.
  destruct (n =? p) eqn: Heq.
  - reflexivity.
  - simpl in Heq. 
    rewrite H2 in Heq. 
    rewrite <- eqb_refl in Heq.
    discriminate Heq.
Qed.

(* Exercise split_combine *)
Theorem split_combine: forall (X Y: Type) l1 l2 (l: list (X * Y)), 
  length l1 = length l2 -> combine l1 l2 = l -> split l = (l1, l2).
Proof. Admitted.
(* Question *)

(* Exercise filter_exercise *)
Theorem filter_exercise: forall (X: Type) (test: X -> bool) (x: X) (l lf: list X),
  filter test l = x :: lf -> test x = true.
Proof.
  intros X test x l lf H.
  induction l as [|y l].
  - simpl in H.
    discriminate H.
  - simpl in H.
    destruct (test y) eqn: H1.
    + injection H as H2. 
      rewrite -> H2 in H1. 
      apply H1.
    + rewrite <- IHl.
      * reflexivity.
      * apply H.
Qed.

(* Exercise forall_exists_challenge *)
Fixpoint forallb {X: Type} (test: X -> bool) (l: list X) : bool :=
  match l with
  | nil => true
  | h :: t =>
    match (test h) with
    | false => false
    | true => forallb test t
    end
  end.

Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X: Type} (test: X -> bool) (l: list X) : bool :=
  match l with
  | nil => false
  | h :: t =>
    match (test h) with
    | true => true
    | false => existsb test t
    end
  end.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb evenb [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X: Type} (test: X -> bool) (l: list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).

Example test_existsb'_1 : existsb' (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb'_2 : existsb' (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb'_3 : existsb' oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb'_4 : existsb' evenb [] = false.
Proof. reflexivity. Qed.

Theorem existsb_existsb': forall (X: Type) (test: X -> bool) (l: list X),
  existsb test l = existsb' test l.
Proof.
  intros X test l.
  unfold existsb'.
  induction l.
  - reflexivity.
  - simpl.
    destruct (test x) eqn: H.
    + simpl. reflexivity.
    + simpl. rewrite <- IHl. reflexivity.
Qed.

