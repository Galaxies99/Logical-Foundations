(* Chap 1 Basics *)
(* Chap 1.1 Data and Functions *)
(* Days of the week *)
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d: day) : day := 
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

(* Booleans *)
Inductive bool : Type :=
  | true
  | false.

Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | false => false
  | true => b2
  end.

Definition orb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1: bool) (b2: bool) : bool := negb (b1 && b2).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1: bool) (b2: bool) (b3: bool) : bool := (b1 && b2 && b3).

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* Types *)
Check true.
Check (negb true).
Check negb.

(* New Types from Old *)
Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p: rgb).

Definition monochrome (c: color) : bool :=
  match c with
  | black => true
  | white => true
  | primary q => false
  end.

Definition isred (c: color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.
(* Note: _ is a shorthand for primary applied 
   to any rgb constructor except red. *)

(* Tuples *)
Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3: bit).

Check (bits B1 B0 B1 B0).

Definition all_zero (nb: nybble) : bool := 
  match nb with
  | (bits B0 B0 B0 B0) => true
  | _ => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
Compute (all_zero (bits B0 B0 B0 B0)).


(* Modules *)
(* Note: like namespace in Cpp *)

Module NatPlayground.

(* Numbers *)
Inductive nat : Type :=
  | O
  | S (n: nat).

Inductive nat' : Type :=
  | stop
  | tick (foo: nat').
(* Note: these shows that O and S have no 
   special meanings, they are just symbols. *)

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n: nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n: nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n: nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n: nat) (m: nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m: nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.
(* Note: (n m: nat) equals to (n: nat) (m: nat) *)

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m: nat) : nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

Fixpoint exp (base power: nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

(* Exercise factorial *)
Fixpoint factorial (n: nat) : nat :=
  match n with
  | O => S O
  | S n' => mult (S n') (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
  (at level 50, left associativity)
  : nat_scope.
Notation "x - y" := (minus x y)
  (at level 50, left associativity)
  : nat_scope.
Notation "x * y" := (mult x y)
  (at level 40, left associativity)
  : nat_scope.

Check ((0 + 1) + 1).

Fixpoint eqb (n m: nat) : bool :=
  match n with
  | O =>
    match m with
    | O => true
    | _ => false
    end
  | S n' =>
    match m with
    | O => false
    | S m' => eqb n' m'
    end
  end.

Fixpoint leb (n m: nat) : bool :=
  match n with
  | O => true
  | S n' =>
    match m with
    | O => false
    | S m' => leb n' m'
    end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise ltb *)

Definition ltb (n m : nat) : bool :=
  (leb n m) && (negb (eqb n m)).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Chap 1.2 Proof by Simplification *)
Theorem plus_O_n: forall n: nat, 0 + n = n.
Proof.
  intros n.
  simpl.   (* Note: sometimes we don't need simpl. *)
  reflexivity.
Qed.

Theorem plus_1_l: forall n: nat, 1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_0_l: forall n:nat, 0 * n = 0.
Proof.
  intros n.
  reflexivity.
Qed.
(* Note: _l means on the left (is L not one) *)

(* Chap 1.3 Proof by rewriting *)
Theorem plus_id_example: forall n m: nat,
  n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_exercise: forall n m o: nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

Theorem mult_0_plus: forall n m: nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. 
Qed.

(* Exercise: mult_S_1 *)
Theorem mult_S_1: forall n m: nat,
  m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity.
Qed.

(* Chap 1.4 Proof by Case Analysis *)
Theorem plus_1_neq_0: forall n: nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  destruct n.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive: forall b: bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative: forall b c, andb b c = andb c b.
Proof.
  intros b c.
  destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb3_exchange:
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d.
  destruct b.
  - destruct c.
    + destruct d.
      * reflexivity.
      * reflexivity.
    + destruct d.
      * reflexivity.
      * reflexivity.
  - reflexivity.
Qed.

Theorem plus_1_neq_0': forall n: nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.
(* Note: means exactly same as:
  intros n'.
  destruct n' as [|n].*)

Theorem andb_commutative'':
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise andb_true_elim2 *)
Theorem andb_true_elim2: forall b c: bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct c.
  - reflexivity.
  - intros H. 
    rewrite <- H. 
    rewrite -> andb_commutative. 
    reflexivity.
Qed.

(* Exercise zero_nbeq_plus_1 *)
Theorem zero_nbeq_plus_1: forall n: nat,
  0 =? (n + 1) = false.
Proof.
  intros n.
  destruct n.
  - reflexivity.
  - reflexivity.
Qed.

(* Chap 1.5 More Exercises *)

Theorem identity_fn_applied_twice:
  forall (f: bool -> bool), 
  (forall (x: bool), f x = x) -> forall (b: bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem andb_eq_orb:
  forall (b c: bool),
  (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct b.
  - simpl. intros H. rewrite -> H. reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | A (n: bin)
  | B (n: bin).

Fixpoint incr (m: bin) : bin :=
  match m with
  | Z => B Z
  | A n => B n
  | B n => A (incr n)
  end.

Example test_bin_inc1: incr Z = B Z.
Proof. reflexivity. Qed.
Example test_bin_inc2: incr (A (A (B Z))) = (B (A (B Z))).
Proof. reflexivity. Qed.
Example test_bin_inc3: incr (B (B (B Z))) = (A (A (A (B Z)))).
Proof. reflexivity. Qed.

Fixpoint bin_to_nat' (m: bin) : nat :=
  match m with
  | Z => O
  | A m => plus (bin_to_nat' m) (bin_to_nat' m)
  | B m => plus (plus (bin_to_nat' m) (bin_to_nat' m)) (S O)
  end.
(* Original Form: too stupid. *)

Fixpoint bin_to_nat (m: bin) : nat :=
  match m with
  | Z => 0
  | A m => 2 * (bin_to_nat m)
  | B m => 1 + 2 * (bin_to_nat m)
  end.

Example test_bin_to_nat1: bin_to_nat (A (A (A (B Z)))) = 8.
Proof. reflexivity. Qed.
Example test_bin_to_nat2: bin_to_nat (B (A (B Z))) = 5.
Proof. reflexivity. Qed.