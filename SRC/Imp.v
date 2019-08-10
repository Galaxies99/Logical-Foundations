(* Chap 12 Imp *)
(* SIMPLE IMPERATIVE PROGRAMS *)
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.
From SRC Require Import Maps.

(* Chap 12.1 Arithmetic and Boolean Expressions *)
(* Chap 12.1.1 Syntax *)
Module AExp.

Inductive aexp : Type :=
  | ANum (n: nat)
  | APlus (a1 a2: aexp)
  | AMinus (a1 a2: aexp)
  | AMult (a1 a2: aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2: aexp)
  | BLe (a1 a2: aexp)
  | BNot (b: bexp)
  | BAnd (b1 b2: bexp).

(* Chap 12.1.2 Evaluation *)
Fixpoint aeval (a: aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof.
  simpl. reflexivity.
Qed.

Fixpoint beval (b: bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

(* Chap 12.1.3 Optimization *)
Fixpoint optimize_0plus (a: aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2) (APlus (ANum 0) (APlus (ANum 0) (ANum 1)))) = APlus (ANum 2) (ANum 1).
Proof.
  simpl. reflexivity.
Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros.
  induction a.
  - simpl. reflexivity.
  - destruct a1 eqn: Ea1.
    + destruct n eqn: En.
      * simpl. apply IHa2.
      * simpl. rewrite <- IHa2. reflexivity.
    + simpl in *. rewrite IHa1.
      rewrite <- IHa2. reflexivity.
    + simpl in *. rewrite IHa1. rewrite IHa2. reflexivity.
    + simpl in *. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite <- IHa1, IHa2. reflexivity.
  - simpl. rewrite <- IHa1, IHa2. reflexivity.
Qed.

(* Chap 12.2 Coq Automation *)
(* Chap 12.2.1 Tacticals *)
(* Chap 12.2.1.1 The try Tactical *)
Theorem silly1: forall ae, aeval ae = aeval ae.
Proof. try reflexivity. Qed.

Theorem silly2: forall (P: Prop), P -> P.
Proof.
  intros.
  try reflexivity.
  apply H.
Qed.

(* Chap 12.2.1.2 The ; Tactical (Simple Form) *)
Lemma foo: forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma foo': forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n; simpl; reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros.
  induction a;
  try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  - reflexivity.
  - destruct a1 eqn: Ea1;
    try (simpl in *; rewrite IHa1; rewrite IHa2; reflexivity).
    + destruct n eqn: En; simpl; rewrite IHa2; reflexivity.
Qed.

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
  try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
  try reflexivity.
  - destruct a1; try (simpl in *; rewrite IHa1; rewrite IHa2; reflexivity).
    + destruct n; simpl; rewrite IHa2; reflexivity.
Qed.

(* Chap 12.2.1.3 The ; Tactical (General Form) *)

(* Chap 12.2.1.4 The repeat Tactical *)
Theorem In10: In 10 [1;2;3;4;5;6;7;8;9;10].
Proof. repeat (try (left; reflexivity); right). Qed.

Theorem In10': In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try(left; reflexivity)).
Qed.

(* Exercise optimize_0plus_b_sound *)
Fixpoint optimize_0plus_b (b: bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot b1
  | BAnd b1 b2 => BAnd b1 b2
  end.

Theorem optimize_0plus_b_sound: forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros.
  induction b; simpl;
  try (rewrite optimize_0plus_sound);
  try (rewrite optimize_0plus_sound);
  reflexivity.
Qed.

(* Exercise optimize *)
Fixpoint optimize_and_false (b: bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot (optimize_and_false b1)
  | BAnd b1 b2 =>
    match b1 with
    | BTrue => b2
    | BFalse => BFalse
    | _ => BAnd (optimize_and_false b1) (optimize_and_false b2)
    end
  end.

Theorem optimize_and_false_sound: forall b,
  beval (optimize_and_false b) = beval b.
Proof.
  intros.
  induction b; simpl;
  try (rewrite optimize_0plus_sound);
  try (rewrite optimize_0plus_sound);
  try (rewrite IHb);
  try (reflexivity).
  - destruct b1; simpl in *;
    try (rewrite IHb1);
    try (rewrite IHb2);
    try (rewrite optimize_0plus_sound);
    try (rewrite optimize_0plus_sound);
    try (reflexivity).
Qed.

(* Chap 12.2.2 Defining New Tactic Notations *)
Tactic Notation "simpl_and_try" tactic(c) :=
  simpl; try c.

(* Chap 12.2.3 The omega Tactic *)
Example silly_presburger_example: forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 -> m <= p.
Proof.
  intros.
  omega.
Qed.

(* Chap 12.2.4 A Few More Handy Tactics *)
(*
  clear H: Delete hypothesis H from the context.
  subst x: For a variable x, find an assumption x = e or e = x in the context, 
    replace x with e throughout the context and current goal, and clear the 
    assumption.
  subst: Substitute away all assumptions of the form x = e or e = x (where x is
    a variable).
  rename... into...: Change the name of a hypothesis in the proof context. For 
    example, if the context includes a variable named x, then rename x into y 
    will change all occurrences of x to y.
  assumption: Try to find a hypothesis H in the context that exactly matches the
    goal; if one is found, behave like apply H.
  contradiction: Try to find a hypothesis H in the current context that is logically
    equivalent to False. If one is found, solve the goal.
  constructor: Try to find a constructor c (from some Inductive definition in the 
    current environment) that can be applied to solve the current goal. If one is 
    found, behave like apply c.
*)

(* Chap 12.3 Evaluation as a Relation *)
Module aevalR_first_try.
Inductive aevalR: aexp -> nat -> Prop :=
  | E_ANum n: aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat): aevalR e1 n1 -> aevalR e2 n2 -> aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat): aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat): aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMult e1 e2) (n1 * n2).

Module TooHardToRead.
Inductive aevalR: aexp -> nat -> Prop :=
  | E_ANum n: aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat) (H1: aevalR e1 n1) (H2: aevalR e2 n2):
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat) (H1: aevalR e1 n1) (H2: aevalR e2 n2):
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat) (H1: aevalR e1 n1) (H2: aevalR e2 n2):
      aevalR (AMult e1 e2) (n1 * n2).
End TooHardToRead.

Notation "e 鈥榎\' n" := (aevalR e n)
  (at level 50, left associativity) : type_scope.

End aevalR_first_try.

Reserved Notation "e '\\' n" (at level 90, left associativity).

Inductive aevalR: aexp -> nat -> Prop :=
  | E_ANum (n: nat): (ANum n) \\ n
  | E_APlus (e1 e2: aexp) (n1 n2: nat): (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat): (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat): (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)
where "e '\\' n" := (aevalR e n): type_scope.

(* Chap 12.3.1 Inference Rule Notation *)
(* Exercise beval_rules *)
(* Skipped *)

(* Chap 12.3.2 Equivalence of the Definitions *)
Theorem aeval_iff_aevalR: forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  intros. split.
  - intros.
    induction H; simpl;
    try (rewrite IHaevalR1, IHaevalR2);
    try (reflexivity).
  - intros.
    generalize dependent n.
    induction a; simpl; intros; subst.
    + apply E_ANum.
    + apply E_APlus.
      apply IHa1; reflexivity.
      apply IHa2; reflexivity.
    + apply E_AMinus.
      apply IHa1; reflexivity.
      apply IHa2; reflexivity.
    + apply E_AMult.
      apply IHa1; reflexivity.
      apply IHa2; reflexivity.
Qed.

Theorem aeval_iff_aevalR': forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  split.
  - intros H; induction H; subst; reflexivity.
  - generalize dependent n.
    induction a; simpl; intros; subst; constructor;
    try apply IHa1; try apply IHa2; try reflexivity.
Qed.

(* Exercise bevalR *)
Reserved Notation "e '\\\' n" (at level 90, left associativity).

Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue: BTrue \\\ true
  | E_BFalse: BFalse \\\ false
  | E_BEq (e1 e2: aexp) (n1 n2: nat):
    (e1 \\ n1) -> (e2 \\ n2) -> (BEq e1 e2) \\\ (n1 =? n2)
  | E_BLe (e1 e2: aexp) (n1 n2: nat):
    (e1 \\ n1) -> (e2 \\ n2) -> (BLe e1 e2) \\\ (n1 <=? n2)
  | E_BNot (e: bexp) (b: bool):
    (e \\\ b) -> (BNot e) \\\ (negb b)
  | E_BAnd (e1 e2: bexp) (b1 b2: bool):
    (e1 \\\ b1) -> (e2 \\\ b2) -> (BAnd e1 e2) \\\ (b1 && b2)
where "e '\\\' n" := (bevalR e n): type_scope.

Lemma beval_iff_bevalR: forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  split.
  - intros H; induction H;
    try (apply aeval_iff_aevalR in H; apply aeval_iff_aevalR in H0);
    subst;
    try reflexivity.
  - generalize dependent bv.
    induction b; intros; subst; constructor;
    try apply aeval_iff_aevalR;
    try apply IHb;
    try apply IHb1;
    try apply IHb2;
    reflexivity.
Qed.

End AExp.

(* Chap 12.3.3 Computational vs. Relational Definitions *)
Module aevalR_division.

Inductive aexp: Type :=
  | ANum (n: nat)
  | APlus (a1 a2: aexp)
  | AMinus (a1 a2: aexp)
  | AMult (a1 a2: aexp)
  | ADiv (a1 a2: aexp).

Reserved Notation "e '\\' n"
  (at level 90, left associativity).

Inductive aevalR: aexp -> nat -> Prop :=
  | E_ANum (n: nat): (ANum n) \\ n
  | E_APlus (e1 e2: aexp) (n1 n2: nat): (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat): (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat): (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)
  | E_ADiv (e1 e2: aexp) (n1 n2 n3: nat): (e1 \\ n1) -> (e2 \\ n2) -> (n2 > 0) -> (mult n2 n3 = n1) -> (ADiv e1 e2) \\ n3
where "e '\\' n" := (aevalR e n): type_scope.

End aevalR_division.

Module aevalR_extended.

Reserved Notation "e '\\' n" (at level 90, left associativity).

Inductive aexp: Type :=
  | AAny
  | ANum (n: nat)
  | APlus (a1 a2: aexp)
  | AMinus (a1 a2: aexp)
  | AMult (a1 a2: aexp).

Inductive aevalR: aexp -> nat -> Prop :=
  | E_Any (n: nat) : AAny \\ n
  | E_ANum (n: nat): (ANum n) \\ n
  | E_APlus (e1 e2: aexp) (n1 n2: nat): (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat): (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat): (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)
where "e '\\' n" := (aevalR e n): type_scope.

End aevalR_extended.

(* Chap 12.4 Expressions With Variables *)
(* Chap 12.4.1 State *)
Definition state := total_map nat.

(* Chap 12.4.2 Syntax *)
Inductive aexp: Type :=
  | ANum (n: nat)
  | AId (x: string)
  | APlus (a1 a2: aexp)
  | AMinus (a1 a2: aexp)
  | AMult (a1 a2: aexp).

Definition W: string := "W".
Definition X: string := "X".
Definition Y: string := "Y".
Definition Z: string := "Z".

Inductive bexp: Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2: aexp)
  | BLe (a1 a2: aexp)
  | BNot (b: bexp)
  | BAnd (b1 b2: bexp).

(* Chap 12.4.3 Notations *)
Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.

Delimit Scope imp_scope with imp.
Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.

Definition example_aexp := (3 + (X * 2)) % imp : aexp.
Definition example_bexp := (true && ~ (X <= 4)) % imp : bexp.

Set Printing Coercions.
Print example_bexp.
Unset Printing Coercions.

(* Chap 12.4.4 Evaluation *)
Fixpoint aeval (st: state) (a: aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st: state) (b: bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Example aexp1: aeval (X !-> 5) (3 + (X * 2)) % imp = 13.
Proof. reflexivity. Qed.

Example bexp1: beval (X !-> 5) (true && ~(X <= 4)) % imp = true.
Proof. reflexivity. Qed.

(* Chap 12.5 Commands *)
(* Chap 12.5.1 Syntax *)
Inductive com: Type :=
  | CSkip
  | CAss (x: string) (a: aexp)
  | CSeq (c1 c2: com)
  | CIf (b: bexp) (c1 c2: com)
  | CWhile (b: bexp) (c: com).

Bind Scope imp_scope with com.
Notation "'SKIP'" := CSkip : imp_scope.
Notation "x '::=' a" := (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" := (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.

Definition fact_in_coq: com :=
 (Z ::= X;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END) % imp.

(* Chap 12.5.2 Desugaring notations *)
Unset Printing Notations.
Print fact_in_coq.
Set Printing Notations.

Set Printing Coercions.
Print fact_in_coq.
Unset Printing Coercions.

(* Chap 12.5.3 The Locate command *)
Locate "&&".
Locate ";;".
Locate "WHILE".
Locate aexp.

(* Chap 12.5.4 More Examples *)
Definition plus2: com :=
  X ::= X + 2.

Definition XtimesYinZ : com :=
  Z ::= X * Y.

Definition subtract_slowly_body : com :=
  Z ::= Z - 1 ;;
  X ::= X - 1.

Definition subtract_slowly : com :=
 (WHILE ~(X = 0) DO
    subtract_slowly_body
  END) % imp.

Definition loop : com :=
  WHILE true DO SKIP END.

(* Chap 12.6 Evaluating Commands *)
(* Chap 12.6.1 Evaluation as a Function (Failed Attempt) *)
Open Scope imp_scope.
Fixpoint ceval_fun_no_while (st: state) (c: com) : state :=
  match c with
  | SKIP => st
  | x ::= a1 => (x !-> (aeval st a1); st)
  | c1 ;; c2 => let st' := ceval_fun_no_while st c1 in
                ceval_fun_no_while st' c2
  | TEST b THEN c1 ELSE c2 FI =>
      if (beval st b) then ceval_fun_no_while st c1
      else ceval_fun_no_while st c2
  | WHILE b DO c END => st
  end.

Close Scope imp_scope.

(* Chap 12.6.2 Evaluation as a Relation *)
Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Inductive ceval: com -> state -> state -> Prop :=
  | E_Skip: forall st, st =[ SKIP ]=> st
  | E_Ass: forall st a1 n x, aeval st a1 = n -> st =[ x ::= a1 ]=> (x !-> n; st)
  | E_Seq: forall c1 c2 st st' st'', st =[ c1 ]=> st' -> st' =[ c2 ]=> st'' -> st =[ c1;; c2 ]=> st''
  | E_IfTrue: forall st st' b c1 c2, beval st b = true -> st =[ c1 ]=> st' -> st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse: forall st st' b c1 c2, beval st b = false -> st =[ c2 ]=> st' -> st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse: forall b st c, beval st b = false -> st =[ WHILE b DO c END ]=> st
  | E_WhileTrue: forall st st' st'' b c, beval st b = true -> st =[ c ]=> st' -> st' =[ WHILE b DO c END ]=> st'' -> st =[ WHILE b DO c END ]=> st''
where "st =[ c ]=> st'" := (ceval c st st').

Example ceval_example1:
  empty_st =[
    X ::= 2;;
    TEST X <= 1
      THEN Y ::= 3
      ELSE Z ::= 4
    FI]=> (Z !-> 4; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2).
  - apply E_Ass. simpl. reflexivity.
  - apply E_IfFalse. reflexivity.
    apply E_Ass. reflexivity.
Qed.

(* Exercise ceval_example2 *)
Example ceval_example2:
  empty_st =[
    X ::= 0;; Y ::= 1;; Z ::= 2
  ]=> (Z !-> 2; Y !-> 1; X !-> 0).
Proof.
  apply E_Seq with (X !-> 0).
  - apply E_Ass. reflexivity.
  - apply E_Seq with (Y !-> 1; X !-> 0).
    + apply E_Ass. reflexivity.
    + apply E_Ass. reflexivity.
Qed.

(* Example pup_to_n *)
Definition pup_to_n: com :=
  Y ::= 0;; 
  WHILE (~ (X = 0)) DO
    Y ::= Y + X;;
    X ::= X - 1
  END.

Theorem pup_to_2_ceval:
  (X !-> 2) =[ pup_to_n ]=> (X !-> 0; Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
Proof.
  apply E_Seq with (Y !-> 0; X !-> 2).
  - apply E_Ass. reflexivity.
  - apply E_WhileTrue with (X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
    + reflexivity.
    + apply E_Seq with (Y !-> 2; Y !-> 0; X !-> 2).
      * apply E_Ass. reflexivity.
      * apply E_Ass. reflexivity.
    + apply E_WhileTrue with (X !-> 0; Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
      * reflexivity.
      * apply E_Seq with (Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2); apply E_Ass; reflexivity.
      * apply E_WhileFalse.
        reflexivity.
Qed.

(* Chap 12.6.3 Determinism of Evaluation *)
Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst; try reflexivity.
  - assert (st' = st'0) as EQ1.
    { apply IHE1_1, H1. }
    subst st'0.
    apply IHE1_2, H4.
  - apply IHE1. assumption.
  - rewrite H in H5. discriminate.
  - rewrite H in H5. discriminate.
  - apply IHE1. assumption.
  - rewrite H in H2. discriminate.
  - rewrite H in H4. discriminate.
  - assert (st' = st'0) as EQ1.
    { apply IHE1_1. assumption. }
    subst st'0.
    apply IHE1_2. assumption.
Qed.

(* Chap 12.7 Reasoning About Imp Programs *)
Theorem plus2_spec: forall st n st',
  st X = n -> st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. clear Heval.
  simpl. apply t_update_eq.
Qed.

(* Exercise XtimesYinZ_spec *)
Theorem XtimesYinZ_spec: forall st n m st',
  st X = n -> st Y = m -> st =[ XtimesYinZ ]=> st' ->
  st' Z = n * m.
Proof.
  intros st n m st' HX HY Heval.
  inversion Heval.
  subst. clear Heval.
  simpl. apply t_update_eq.
Qed.

Print total_map.

(* Exercise loop_never_stops *)
Theorem loop_never_stops: forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra.
  unfold loop in contra.
  remember (WHILE true DO SKIP END) % imp as loopdef eqn: Heqloopdef.
  induction contra; try discriminate.
  - inversion Heqloopdef. subst. simpl in H. discriminate.
  - apply IHcontra2. apply Heqloopdef.
Qed.

(* Exercise no_whiles_eqv *)
Open Scope imp_scope.
Fixpoint no_whiles (c: com) : bool :=
  match c with
  | SKIP => true
  | _ ::= _ => true
  | c1 ;; c2 => andb (no_whiles c1) (no_whiles c2)
  | TEST _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END => false
  end.
Close Scope imp_scope.

Inductive no_whilesR: com -> Prop :=
  | no_whiles_Skip: no_whilesR SKIP
  | no_whiles_Ass: forall s n, no_whilesR (s ::= n)
  | no_whiles_Seq: forall e1 e2, no_whilesR e1 -> no_whilesR e2 -> no_whilesR (e1 ;; e2)
  | no_whiles_If: forall e1 e2 b, no_whilesR e1 -> no_whilesR e2 -> no_whilesR (TEST b THEN e1 ELSE e2 FI).

Theorem no_whiles_eqv:
  forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split.
  - intros.
    induction c; 
    try constructor; 
    try inversion H;
    try (apply andb_true_iff in H1; destruct H1 as [H2 H3]);
    try apply IHc1; try apply IHc2;
    try apply H2; try apply H3.
  - intros.
    induction H;
    simpl;
    try (apply andb_true_iff; split);
    try apply IHno_whilesR1;
    try apply IHno_whilesR2;
    try reflexivity.
Qed.

(* Exercise no_whiles_terminating *)
Theorem no_whiles_terminating: forall c st,
  no_whilesR c -> exists st', st =[ c ]=> st'.
Proof.
  intros c.
  induction c; intros.
  - exists st. constructor. 
  - exists (x !-> (aeval st a); st).
    constructor. reflexivity.
  - inversion H. subst.
    apply IHc1 with (st := st) in H2.
    destruct H2 as [st' H2].
    apply IHc2 with (st := st') in H3.
    destruct H3 as [st'' H3].
    exists st''.
    apply (E_Seq c1 c2 st st' st'').
    apply H2. apply H3.
  - inversion H. subst.
    apply IHc1 with (st := st) in H2.
    apply IHc2 with (st := st) in H4.
    destruct H2 as [st1 H1].
    destruct H4 as [st2 H2].
    destruct (beval st b) eqn: Eb.
    + exists st1. apply E_IfTrue. apply Eb. apply H1.
    + exists st2. apply E_IfFalse. apply Eb. apply H2.
  - inversion H.
Qed.


(*** Additional Exercise ***)
(* Exercise stack_complier *)
Inductive sinstr : Type :=
  | SPush (n: nat)
  | SLoad (x: string)
  | SPlus
  | SMinus
  | SMult.

Fixpoint s_execute (st: state) (stack: list nat) (prog: list sinstr) : list nat :=
  match prog with
  | nil => stack
  | progh :: progt => 
    match progh with
    | SPush n => s_execute st (n :: stack) progt
    | SLoad x => s_execute st ((st x) :: stack) progt
    | SPlus => 
      match stack with
      | h1 :: h2 :: t => s_execute st ((h2 + h1) :: t) progt
      | _ => s_execute st stack progt
      end
    | SMinus => 
      match stack with
      | h1 :: h2 :: t => s_execute st ((h2 - h1) :: t) progt
      | _ => s_execute st stack progt
      end
    | SMult => 
      match stack with
      | h1 :: h2 :: t => s_execute st ((h2 * h1) :: t) progt
      | _ => s_execute st stack progt
      end
    end
  end.

Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof. reflexivity. Qed.

Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof. reflexivity. Qed.

Fixpoint s_compile (e: aexp): list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId id => [SLoad id]
  | APlus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SPlus]
  | AMinus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SMinus]
  | AMult e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SMult]
  end.

Example s_compile1 :
  s_compile (X - (2 * Y))%imp
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.

(* Exercise stack_compiler_correct *)
Lemma s_compile_seq: forall st stack prog1 prog2,
  s_execute st stack (prog1 ++ prog2) = s_execute st (s_execute st stack prog1) prog2.
Proof.
  intros st stack prog1.
  generalize dependent st.
  generalize dependent stack.
  induction prog1; intros; simpl; try reflexivity.
  - intros. simpl. 
    destruct a; 
    try apply IHprog1;
    try destruct stack;
    try apply IHprog1;
    try destruct stack;
    try apply IHprog1;
    try apply IHprog1.
Qed.

Lemma s_compile_correct_strong: forall st stack e,
  s_execute st stack (s_compile e) = [ aeval st e ] ++ stack.
Proof.
  intros st stack e.
  generalize dependent stack.
  induction e; intros; simpl;
  try (rewrite s_compile_seq;
       rewrite s_compile_seq;
       rewrite IHe1; 
       rewrite IHe2);
  try reflexivity.
Qed.

Theorem s_compile_correct: forall (st: state) (e: aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros. apply (s_compile_correct_strong st [] e).
Qed.

(* Exercise short_circuit *)
Fixpoint beval' (st: state) (b: bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BNot b1 => negb (beval' st b1)
  | BAnd b1 b2 => 
    if (beval' st b1) then (beval' st b2)
    else false
  end.

Theorem beval'_eq_beval: forall st b,
  beval' st b = beval st b.
Proof.
  intros.
  induction b; try reflexivity.
Qed.

(* Exercise break_imp *)
Module BreakImp.

Inductive com : Type :=
  | CSkip
  | CBreak
  | CAss (x: string) (a: aexp)
  | CSeq (c1 c2: com)
  | CIf (b: bexp) (c1 c2: com)
  | CWhile (b: bexp) (c: com).

Notation "'SKIP'" := CSkip.
Notation "'BREAK'" := CBreak.
Notation "x '::=' a" := (CAss x a) (at level 60).
Notation "c1 ;; c2" := (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := (CWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" := (CIf c1 c2 c3) (at level 80, right associativity).

Inductive result: Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
  (at level 40, st' at next level).

Inductive ceval: com -> state -> result -> state -> Prop :=
  | E_Skip: forall st, st =[ CSkip ]=> st / SContinue
  | E_Break: forall st, st =[ CBreak ]=> st / SBreak
  | E_Ass: forall a1 n x st, aeval st a1 = n -> st =[ x ::= a1 ]=> (x !-> n; st) / SContinue
  | E_SeqBreak: forall c1 c2 st st', st =[ c1 ]=> st' / SBreak -> st =[ c1;; c2 ]=> st' / SBreak
  | E_SeqContinue: forall c1 c2 st st' st'' res, st =[ c1 ]=> st' / SContinue -> st =[ c2 ]=> st'' / res -> st =[ c1;; c2 ]=> st'' / res
  | E_IfTrue: forall b c1 c2 st st' res, beval st b = true -> st =[ c1 ]=> st' / res -> st =[ TEST b THEN c1 ELSE c2 FI ]=> st' / res
  | E_IfFalse: forall b c1 c2 st st' res, beval st b = false -> st =[ c2 ]=> st' / res -> st =[ TEST b THEN c1 ELSE c2 FI ]=> st' / res
  | E_WhileFalse: forall b c st, beval st b = false -> st =[ WHILE b DO c END ]=> st / SContinue
  | E_WhileTrue: forall b c st st' st'', beval st b = true -> st =[ c ]=> st' / SContinue -> st' =[ WHILE b DO c END ]=> st'' / SContinue -> st =[ WHILE b DO c END]=> st'' / SContinue
  | E_WhileBreak: forall b c st st', beval st b = true -> st =[ c ]=> st' / SBreak -> st =[ WHILE b DO c END ]=> st' / SContinue
where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').

Theorem break_ignore: forall c st st' s,
  st =[ BREAK;; c ]=> st' / s -> st = st'.
Proof.
  intros.
  inversion H.
  subst. inversion H5. reflexivity.
  subst. inversion H2.
Qed.

Theorem while_continue: forall b c st st' s,
  st =[ WHILE b DO c END ]=> st' / s -> s = SContinue.
Proof.
  intros.
  inversion H; reflexivity.
Qed.

Theorem while_stops_on_break: forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ WHILE b DO c END ]=> st' / SContinue.
Proof.
  intros.
  constructor.
  apply H.
  apply H0.
Qed.

(* Exercise while_break_true *)
Theorem while_break_true: forall b c st st',
  st =[ WHILE b DO c END ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
  intros.
  remember (WHILE b DO c END) as loop.
  induction H; try inversion Heqloop; subst; clear Heqloop; simpl in *.
  - rewrite H in H0. discriminate.
  - apply IHceval2. reflexivity. apply H0.
  - exists st. apply H1.
Qed.

(* Exercise ceval_deterministic *)
Theorem ceval_deterministic: forall (c: com) st st1 st2 s1 s2,
  st =[ c ]=> st1 / s1 ->
  st =[ c ]=> st2 / s2 ->
  st1 = st2 /\ s1 = s2.
Proof.
  intros.
  generalize dependent st2.
  generalize dependent s2.
  induction H; intros.
  - (* E_Skip *) inversion H0. auto.
  - (* E_Break *) inversion H0. auto.
  - (* E_Ass *) inversion H0. subst. auto.
  - (* E_SeqBreak *) inversion H0; subst. 
    + (* other E_SeqBreak *) auto.
    + (* other E_SeqContinue *)
      assert (st' = st'0 /\ SBreak = SContinue).
      { apply IHceval. apply H3. }
      inversion H1. discriminate.
  - (* E_SeqContinue *) inversion H1; subst.
    + (* other SeqBreak *)
      assert (st' = st2 /\ SContinue = SBreak).
      { apply IHceval1. apply H7. }
      inversion H2. discriminate.
    + (* other SeqContinue *) subst. 
      apply IHceval2, H8.
  - (* E_IfTrue *) inversion H1; subst.
    + (* other E_IfTrue *) apply IHceval, H9.
    + (* other E_IfFalse *) rewrite H8 in H. discriminate.
  - (* E_IfFalse *) inversion H1; subst.
    + (* other E_IfTrue *) rewrite H8 in H. discriminate.
    + (* other E_IfFalse *) apply IHceval, H9.
  - (* E_WhileFalse *) inversion H0; subst; try auto; try (rewrite H3 in H; discriminate).
  - (* E_WhileTrue *) inversion H2; subst.
    + (* other E_WhileFalse *) rewrite H8 in H. discriminate.
    + (* other E_WhileTrue *) apply IHceval2.
      assert (st' = st'0 /\ SContinue = SContinue).
      { apply IHceval1. apply H6. }
      inversion H3. rewrite H4. apply H10.
    + (* other E_WhileBreak *)
      assert (st' = st2 /\ SContinue = SBreak).
      { apply IHceval1. apply H9. }
      inversion H3. discriminate.
  - (* E_WhileBreak *) inversion H1; subst.
    + (* other E_WhileFalse *) rewrite H7 in H. discriminate.
    + (* other E_WhileTrue *)
      assert (st' = st'0 /\ SBreak = SContinue).
      { apply IHceval. apply H5. }
      inversion H2. discriminate.
    + (* other E_WhileBreak *) 
      assert (st' = st2 /\ SBreak = SBreak).
      { apply IHceval. apply H8. }
      inversion H2. auto.
Qed.

End BreakImp.

(* Exercise add_for_loop *)

Module ForImp.

Inductive com : Type :=
  | FSkip
  | FAss (x: string) (a: aexp)
  | FSeq (c1 c2: com)
  | FIf (b: bexp) (c1 c2: com)
  | FWhile (b: bexp) (c: com)
  | FFor (c1: com) (b: bexp) (c2: com) (c3: com).

Notation "'SKIP'" := FSkip.
Notation "x '::=' a" := (FAss x a) (at level 60).
Notation "c1 ;; c2" := (FSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := (FWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" := (FIf c1 c2 c3) (at level 80, right associativity).
Notation "'FOR' '(' c1 ';' b ';' c2 ')' 'DO' c3 'END'" := (FFor c1 b c2 c3) (at level 80, right associativity).

Reserved Notation "st '=[' c ']=>' st'" (at level 40, st' at next level).
Inductive cval: state -> com -> state -> Prop :=
  | F_Skip: forall st, st =[ FSkip ]=> st
  | F_Ass: forall x a st, st =[ FAss x a ]=> (x !-> (aeval st a); st)
  | F_Seq: forall c1 c2 st st' st'', st =[ c1 ]=> st' -> st' =[ c2 ]=> st'' -> st =[ c1;; c2 ]=> st''
  | F_IfTrue: forall b c1 c2 st st', beval st b = true -> st =[ c1 ]=> st' -> st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | F_IfFalse: forall b c1 c2 st st', beval st b = false -> st =[ c2 ]=> st' -> st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | F_WhileFalse: forall b c st, beval st b = false -> st =[ WHILE b DO c END ]=> st
  | F_WhileTrue: forall b c st st' st'', beval st b = true -> st =[ c ]=> st' -> st' =[ WHILE b DO c END ]=> st'' -> st =[ WHILE b DO c END ]=> st''
  | F_For: forall b c1 c2 c3 st st', st =[ c1 ;; WHILE b DO c3 ;; c2 END ]=> st' -> st =[ FOR ( c1; b; c2 ) DO c3 END ]=> st' 
where "st '=[' c ']=>' st'" := (cval st c st').

Definition for_imp_prog : com := 
  (Y ::= (ANum 0);;
    FOR ( X ::= (ANum 1) ; BNot (BEq (AId X) (ANum 0)) ; X ::= AMinus (AId X) (ANum 1) )
    DO Y ::= APlus (AId X) (AId Y) END).

Example for_imp_ex: empty_st =[ for_imp_prog ]=> (X !-> 0; Y !-> 1; X !-> 1; Y !-> 0).
Proof.
  unfold for_imp_prog. 
  apply F_Seq with (Y !-> 0).
  constructor.
  apply F_For.
  apply F_Seq with (X !-> 1; Y !-> 0).
  constructor.
  apply F_WhileTrue with (X !-> 0; Y !-> 1; X !-> 1; Y !-> 0).
  constructor.
  apply F_Seq with (Y !-> 1; X !-> 1; Y !-> 0).
  constructor.
  constructor.
  apply F_WhileFalse.
  constructor.
Qed.
