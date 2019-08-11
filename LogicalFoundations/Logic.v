(* Chap 6 Logic *)
Set Warnings "-notation-overridden,-parsing".
From LF Require Export Tactics.

Check 3 = 3.
Check forall n m: nat, n + m = m + n.
Check 2 = 2.
Check forall n: nat, n = 2.
Check 3 = 4.

Theorem plus_2_2_is_4: 2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true: plus_fact.
Proof. reflexivity. Qed.

Definition is_three (n: nat) : Prop := n = 3.
Check is_three.

Definition injective {A B} (f: A -> B) :=
  forall x y: A, f x = f y -> x = y.

Lemma succ_inj: injective S.
Proof.
  intros n m H.
  injection H as H1.
  apply H1.
Qed.

Check @eq.

(* Chap 6.1 Logical Connectives *)
(* Chap 6.1.1 Conjunction *)
Example and_example: 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro: forall A B: Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  split.
  - apply HA.
  - apply HB.
Qed.

Example and_example': 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise and_exercise *)
Example and_exercise: forall n m: nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  split.
  - induction n.
    + reflexivity.
    + discriminate H.
  - induction m.
    + reflexivity.
    + rewrite plus_comm in H. 
      discriminate H.
Qed.

Lemma and_example2: forall n m: nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite -> Hn, Hm.
  reflexivity.
Qed.

Lemma and_example2': forall n m: nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite -> Hn, Hm.
  reflexivity.
Qed.

Lemma and_example2'': forall n m: nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite -> Hn, Hm.
  reflexivity.
Qed.

Lemma and_example3: forall n m: nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H': n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn.
  reflexivity.
Qed.

Lemma proj1: forall P Q: Prop, P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.
Qed.

(* Exercise proj2 *)
Lemma proj2: forall P Q: Prop, P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ.
Qed.

Theorem and_commut: forall P Q: Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.

(* Exercise and_assoc *)
Theorem and_assoc: forall P Q R: Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Check and.

(* Chap 6.1.2 Disjunction *)
Lemma or_example: forall n m: nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O. reflexivity.
Qed.

Lemma or_intro: forall A B: Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ: forall n: nat, n = 0 \/ n = S (pred n).
Proof.
  intros n.
  induction n.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* Chap 6.1.3 Falsehood and Negation *)
Module MyNot.

Definition not (P: Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

End MyNot.

Theorem ex_falso_quodlibet: forall P: Prop,
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.
(* Note: If we get False into the proof context, we can use destruct 
         on it to complete any goal. *)

(* Exercise not_implies_our_not *)
Fact not_implies_our_not: forall P: Prop, 
  ~P -> (forall Q: Prop, P -> Q).
Proof.
  intros P HP' Q HP.
  destruct HP'.
  apply HP.
Qed.

Notation "x <> y" := (~(x = y)).

Theorem zero_not_one: 0 <> 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra.
Qed.

Theorem not_False: ~False.
Proof.
  unfold not.
  intros H.
  apply H.
Qed.

Theorem contradiction_implies_anything: forall P Q: Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNP].
  destruct HNP.
  apply HP.
Qed.

Theorem double_neg: forall P: Prop,
  P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros G.
  apply G.
  apply H.
Qed.

(* Exercise double_neg_inf *)
(* skipped *)

(* Exercise contrapositive *)
Theorem contrapositive: forall (P Q: Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H0.
  unfold not.
  intros H1 H2.
  apply H1, H0, H2.
Qed.

(* Exercise not_both_true_and_false *)
Theorem not_both_true_and_false: forall P: Prop,
  ~(P/\~P).
Proof.
  intros P.
  unfold not.
  intros [H1 H2].
  apply H2, H1.
Qed.

(* Exercise informal_not_PNP *)
(* Skipped *)

Theorem not_true_is_false: forall b: bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false': forall b: bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    exfalso.
    apply H. reflexivity.
  - reflexivity.
Qed.

(* Chap 6.1.4 Truth *)
Lemma True_is_true: True.
Proof. apply I. Qed.

(* Chap 6.1.5 Logical Equivalence *)
Module MyIff.

Definition iff (P Q: Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q).

End MyIff.

Theorem iff_sym: forall P Q: Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - apply HBA.
  - apply HAB.
Qed.

Lemma not_true_iff_false: forall b,
  b <> true <-> b = false.
Proof.
  intros b.
  split.
  - apply not_true_is_false.
  - intros H. rewrite H. unfold not. intros H'.
    discriminate H'.
Qed.

(* Exercise or_distributes_over_and *)
Theorem or_distributes_over_and: forall P Q R: Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [HP | [HQ HR]].
    + split.
      * left. apply HP.
      * left. apply HP.
    + split.
      * right. apply HQ.
      * right. apply HR.
  - intros [[HP1 | HQ] [HP2 | HR]].
    + left. apply HP1.
    + left. apply HP1.
    + left. apply HP2.
    + right. split.
      * apply HQ.
      * apply HR.
Qed.

From Coq Require Import Setoids.Setoid.

Lemma mult_eq_0: forall n m,
  n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  destruct n.
  - left. reflexivity.
  - right.
    destruct m.
    + reflexivity.
    + exfalso. discriminate H.
Qed.

Lemma mult_0: forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc: forall P Q R: Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros [HP | [HQ | HR]].
    + left. left. apply HP.
    + left. right. apply HQ.
    + right. apply HR.
  - intros [[HP | HQ] | HR].
    + left. apply HP.
    + right. left. apply HQ.
    + right. right. apply HR.
Qed.

Lemma mult_0_3:
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

(* Existential Quantification *)
Lemma four_is_even: exists n: nat, 4 = n + n.
Proof.
  exists 2.
  reflexivity.
Qed.

Lemma exists_example_2: forall n,
  (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

(* Exercise dist_not_exists *)
Theorem dist_not_exists: forall (X: Type) (P: X -> Prop),
  (forall x, P x) -> ~(exists x, ~P x).
Proof.
  intros X P H.
  unfold not.
  intros [x H0].
  apply H0.
  apply H.
Qed.

(* Exercise dist_exists_or *)
Theorem dist_exists_or: forall (X: Type) (P Q: X -> Prop),
  (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q [x [HP | HQ]].
  - left. exists x. apply HP.
  - right. exists x. apply HQ.
Qed.

(* Chap 6.2 Programming with Propositions *)
Fixpoint In {A: Type} (x: A) (l: list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.
Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map: forall (A B: Type) (f: A -> B) (l: list A) (x: A),
  In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l.
  - simpl. intros [].
  - simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl. apply H.
Qed.

(* Exercise In_map_iff *)
Lemma In_map_iff: 
  forall (A B: Type) (f: A -> B) (l: list A) (y: B), In y (map f l)
  <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. 
  split.
  - intros H. 
    induction l.
    + simpl. simpl in H. exfalso. apply H.
    + simpl. 
      destruct H as [HA | HB].
      * exists x. split.
        { apply HA. }
        { left. reflexivity. }
      * destruct IHl. 
        apply HB. 
        exists x0.
        { 
          destruct H as [HC HD]. split.
          { apply HC. } 
          { right. apply HD. }
        }
  - intros [x [HA HB]].
    induction l.
    + simpl. simpl in HB. apply HB.
    + simpl. simpl in HB.
      destruct HB as [HC | HD].
      * left. rewrite <- HC in HA. apply HA.
      * right. apply IHl. apply HD.
Qed.
(* Question: too long !!! *)

Lemma In_app_iff: forall A l l' (a: A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a.
  split.
  - intros H.
    induction l.
    + simpl in H. right. apply H.
    + simpl in H. 
      destruct H as [HA | HB].
      * simpl. left. left. apply HA.
      * simpl. rewrite <- or_assoc. 
        right. apply IHl. apply HB.
  - intros H.
    induction l.
    + simpl in H. simpl.
      destruct H.
      * apply ex_falso_quodlibet. apply H.
      * apply H.
    + simpl in H. simpl.
      destruct H as [[HA | HB] | HC].
      * left. apply HA.
      * right. apply IHl. left. apply HB.
      * right. apply IHl. right. apply HC.
Qed.

(* Exercise All *)
Fixpoint All {T: Type} (P: T -> Prop) (l: list T) : Prop :=
  match l with
  | [] => True
  | h :: t => (P h) /\ (All P t)
  end.

Lemma All_In:
  forall T (P: T -> Prop) (l: list T), (forall x, In x l -> P x) 
  <-> All P l.
Proof.
  intros T P l.
  split.
  - intros H.
    induction l.
    + simpl. reflexivity.
    + simpl. simpl in H.
      split.
      * apply H. left. reflexivity.
      * apply IHl. intros y. intros H'.
        apply H. right. apply H'.
  - intros H.
    induction l.
    + simpl. intros x. apply ex_falso_quodlibet.
    + simpl. intros x0 H'.
      destruct H'.
      * simpl in H. rewrite <- H0. apply H.
      * simpl in H. apply IHl. apply H. apply H0.
Qed.

(* Exercise combine_odd_even *)
Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun (n: nat) => if oddb n then Podd n else Peven n.

Theorem combine_odd_even_intro:
  forall (Podd Peven: nat -> Prop) (n: nat),
         (oddb n = true -> Podd n) ->
         (oddb n = false -> Peven n) ->
         combine_odd_even Podd Peven n.
Proof.
  intros Podd Pven n H1 H2.
  unfold combine_odd_even.
  destruct (oddb n).
  - apply H1. reflexivity.
  - apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd:
  forall (Podd Peven: nat -> Prop) (n: nat),
         combine_odd_even Podd Peven n ->
         oddb n = true -> Podd n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  rewrite H2 in H1.
  apply H1.
Qed.

Theorem combine_odd_even_elim_even:
  forall (Podd Peven: nat -> Prop) (n: nat),
         combine_odd_even Podd Peven n ->
         oddb n = false -> Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  rewrite H2 in H1.
  apply H1.
Qed.

(* Chap 6.3 Applying Theorems to Arguments *)
Check plus_comm.

Lemma plus_comm3: forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert(H: y + z = z + y).
  { apply plus_comm. }
  rewrite H.
  reflexivity.
Qed.

Lemma plus_comm3': forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Lemma in_not_nil:
  forall A (x: A) (l: list A), In x l -> l <> [].
Proof.
  intros A x l H.
  unfold not.
  intro H1.
  destruct l.
  - simpl in H. apply H.
  - discriminate H1.
Qed.

Lemma in_not_nil_42: forall l: list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

Lemma in_not_nil_42_take2: forall l: list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Lemma in_not_nil_42_take3: forall l: list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

Lemma in_not_nil_42_take4: forall l: list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Lemma in_not_nil_42_take5: forall l: list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Example lemma_application_ex:
  forall {n: nat} {ns: list nat}, In n (map (fun m => m * 0) ns) -> n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H) as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite Hm. reflexivity.
Qed.

(* Chap 6.4 Coq vs. Set Theory *)
(* Chap 6.4.1 Functional Extensionality *)
Example function_equality_ex1:
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

(* 
Note: the principle of functional extensionality (Coq do not provide)
  (forall x, f x = g x) -> f = g.
 *)

Axiom functional_extensionality: forall {X Y: Type} {f g: X -> Y},
  (forall x: X, f x = g x) -> f = g.

Example function_equality_ex2:
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros x.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2.

(* Exercise tr_rev_correct *)
Fixpoint rev_append {X} (l1 l2: list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l: list X) : list X := rev_append l [].

Lemma tr_rev_correct_lemma: 
  forall X (l1 l2: list X), rev_append l1 l2 = rev l1 ++ l2.
Proof.
  intros X l1.
  induction l1.
  - intros l2.
    simpl. reflexivity.
  - intros l2.
    simpl. rewrite <- app_assoc.
    simpl. apply IHl1.
Qed.

Lemma tr_rev_correct: forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  unfold tr_rev.  
  intros l.
  destruct l.
  - reflexivity.
  - simpl. apply tr_rev_correct_lemma. 
Qed.

(* Chap 6.4.2 Propositions and Booleans *)
Example even_42_bool: evenb 42 = true.
Proof. reflexivity. Qed.
Example even_42_prop: exists k, 42 = double k.
Proof. exists 21. reflexivity. Qed.

Theorem evenb_double: forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

From LF Require Export Induction.
Theorem evenb_double_conv: forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  intros n.
  induction n.
  - simpl. exists 0. reflexivity.
  - destruct (evenb n) eqn: H.
    + rewrite evenb_S. rewrite H. simpl.
      destruct IHn as [k H'].
      exists k. rewrite H'. reflexivity.
    + rewrite evenb_S. rewrite H. simpl.
      destruct IHn as [k H'].
      exists (S k). simpl. rewrite <- H'.
      reflexivity.
Qed.

Theorem even_bool_prop: forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros H. destruct H as [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Theorem eqb_eq: forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

Definition is_even_prime n :=
  if n =? 2 then true
  else false.

Example even_1000: exists k, 1000 = double k.
Proof. exists 500. reflexivity. Qed.

Example even_1000': evenb 1000 = true.
Proof. reflexivity. Qed.

Example even_1000'': exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

Example not_even_1001: evenb 1001 = false.
Proof. reflexivity. Qed.  

Example not_even_1001': ~(exists k, 1001 = double k).
Proof.
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

Lemma plus_eqb_example: forall n m p: nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

(* Exercise logical_connectives *)
Lemma andb_true_iff: forall b1 b2: bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2.
  split.
  - intros H.
    destruct b1.
    + simpl in H. split.
      * reflexivity.
      * apply H.
    + simpl in H. discriminate H.
  - intros [HA HB].
    rewrite HA, HB.
    reflexivity.
Qed.

Lemma orb_true_iff: forall b1 b2: bool,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2.
  split.
  - intros H.
    destruct b1.
    + left. reflexivity.
    + simpl in H. right. apply H.
  - intros [HA | HB].
    + rewrite HA. reflexivity.
    + rewrite HB. 
      destruct b1.
      * reflexivity.
      * reflexivity.
Qed.

Theorem eqb_neq: forall x y: nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y.
  split.
  - intros H. unfold not. 
    destruct (x =? y) eqn: H'.
    + discriminate H.
    + intros H''. rewrite H'' in H'. rewrite <- eqb_refl in H'. discriminate H'.
  - intros H. unfold not in H.
    destruct (x =? y) eqn: H'.
    + rewrite eqb_eq in H'.
      destruct H. apply H'.
    + reflexivity.
Qed.

(* Exercise eqb_list *)
Fixpoint eqb_list {A: Type} (eqb: A -> A -> bool) (l1 l2: list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ => false
  | _, [] => false
  | h1 :: t1, h2 :: t2 => (eqb h1 h2) && (eqb_list eqb t1 t2)
  end.

Lemma eqb_list_true_iff:
  forall A (eqb: A -> A -> bool), (forall a1 a2, eqb a1 a2 = true <-> a1 = a2)
  -> (forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2).
Proof.
  intros A eqb H1.
  intros l1.
  split.
  - generalize dependent l2.
    induction l1.
    + intros l2 H2. simpl in H2.
      destruct l2.
      * reflexivity.
      * discriminate H2.
    + intros l2 H2.
      destruct l2.
      * discriminate H2.
      * simpl in H2. 
        destruct (eqb x x0) eqn: H3.
        { apply H1 in H3. apply IHl1 in H2. rewrite H3. rewrite H2. reflexivity. }
        { simpl in H2. discriminate H2. }
  - generalize dependent l2.
    induction l1.
    + intros l2 H2.
      destruct l2.
      * reflexivity.
      * discriminate H2.
    + intros l2 H2.
      destruct l2.
      * discriminate H2.
      * simpl. injection H2 as H3 H4. apply H1 in H3. apply IHl1 in H4. rewrite H3, H4. reflexivity. 
Qed.

(* Exercise All_forallb *)
Theorem forallb_true_iff: forall X test (l: list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l.
  split.
  - induction l.
    + simpl. reflexivity.
    + simpl. 
      destruct (test x) eqn: H1.
      * intros H2. apply IHl in H2. 
        split.
        { reflexivity. }
        { apply H2. }
      * intros H2. discriminate H2.
  - induction l.
    + simpl. reflexivity.
    + simpl.
      destruct (test x) eqn: H1.
      * intros H2. destruct H2 as [H3 H4]. apply IHl in H4. apply H4.
      * intros H2. destruct H2 as [H3 H4]. discriminate H3.
Qed.

(* Chap 6.4.3 Classical vs. Constructive Logic *)
Definition excluded_middle := forall P: Prop,
  P \/ ~P.

Theorem restricted_excluded_middle: forall P b,
  (P <-> b = true) -> P \/ ~P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. unfold not. intros contra. discriminate contra.
Qed.

Theorem restricted_excluded_middle_eq: forall n m: nat,
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry. apply eqb_eq.
Qed.

(* Exercise excluded_middle_irrefutable *)
Theorem excluded_middle_irrefutable: forall P: Prop,
  ~~ (P \/ ~P).
Proof.
  intros P.
  unfold not.
  intros H1. apply H1.
  right. intros H2. apply H1. left. apply H2.
Qed.

(* Theorem not_exists_dist *)
Theorem not_exists_dist: excluded_middle -> 
  forall (X: Type) (P: X -> Prop), ~(exists x, ~ P x) -> (forall x, P x).
Proof.
  intros H1 X P H2 x.
  assert (H: P x \/ ~ (P x)). { apply H1. }
  destruct H as [H3 | H4].
  - apply H3.
  - unfold not in H2, H4. apply ex_falso_quodlibet. apply H2. exists x. apply H4.
Qed.

(* Exercise classical_axioms *)
Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination :=
  forall P: Prop, ~~P -> P.

Definition de_morgan_not_and_not :=
  forall P Q: Prop, ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or :=
  forall P Q: Prop, (P -> Q) -> (~P \/ Q).

Lemma excluded_middle_to_peirce:
  excluded_middle -> peirce.
Proof. 
  intro EM.
  unfold peirce.
  intros.
  assert (IP: P \/ (~P)).
  { apply EM. }
  tauto.
Qed.

Lemma peirce_to_double_negation_elimination:
  peirce -> double_negation_elimination.
Proof.
  intro PE.
  unfold double_negation_elimination.
  intros.
  assert(I: ((P -> False) -> P) -> P).
  { apply PE. }
  tauto.
Qed.

Lemma double_negation_elimination_to_de_morgan_not_and_not:
  double_negation_elimination -> de_morgan_not_and_not.
Proof.
  intro DNE.
  unfold de_morgan_not_and_not.
  intros.
  assert(IPQ: ~~ (P \/ Q) -> (P \/ Q)). 
  { apply DNE. }
  tauto.
Qed.

Lemma de_morgan_not_and_not_to_implies_to_or:
  de_morgan_not_and_not -> implies_to_or.
Proof.
  intro DMNAN.
  unfold implies_to_or.
  intros.
  assert(I: ~(~~P /\ ~Q) -> (~P) \/ Q).
  { apply DMNAN. }
  tauto.
Qed.

Lemma implies_to_or_to_excluded_middle:
  implies_to_or -> excluded_middle.
Proof.
  intros ITO.
  unfold excluded_middle.
  intros.
  assert (I: (P -> P) -> (~P \/ P)). 
  { apply ITO. }
  tauto.
Qed.