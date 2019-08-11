(* Chap 16 Auto *)
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import omega.Omega.
From SRC Require Import Maps.
From SRC Require Import Imp.

Ltac inv H := inversion H; subst; clear H.

Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { apply IHE1_1; apply H1. }
    subst st'0.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
  - (* b = true *)
    apply IHE1. assumption.
  - (* b = false *)
    rewrite H in H5. inversion H5.
  (* E_IfFalse *)
  - (* b = true *)
    rewrite H in H5. inversion H5.
  - (* b = false *)
    apply IHE1. assumption.
  (* E_WhileFalse *)
  - (* b = false *)
    reflexivity.
  - (* b = true *)
    rewrite H in H2. inversion H2.
  (* E_WhileTrue *)
  - (* b = false *)
    rewrite H in H4. inversion H4.
  - (* b = true *)
    assert (st' = st'0) as EQ1.
    { apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption. 
Qed.

(* Chap 16.1 The auto Tactic *)
Example auto_example_1: forall P Q R: Prop,
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. assumption.
Qed.

Example auto_example_1': forall P Q R: Prop,
  (P -> Q) -> (Q -> R) -> P -> R.
Proof. auto. Qed.

Example auto_example_2: forall P Q R S T U: Prop,
  (P -> Q) -> (P -> R) ->
  (T -> R) -> (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) -> T -> P -> U.
Proof. auto. Qed.

Example auto_example_3: forall P Q R S T U: Prop,
  (P -> Q) -> (Q -> R) ->
  (R -> S) -> (S -> T) ->
  (T -> U) -> P -> U.
Proof.
  auto.
  auto 6.
Qed.

Example auto_example_4: forall P Q R: Prop,
  Q -> (Q -> R) -> P \/ (Q /\ R).
Proof. auto. Qed.

Lemma le_antisym: forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. omega. Qed.

Example auto_example_6: forall n m p: nat,
  (n <= p -> (n <= m /\ m <= n)) -> n <= p -> n = m.
Proof.
  intros.
  auto using le_antisym.
Qed.

Hint Resolve le_antisym.
Example auto_example_6': forall n m p: nat,
  (n <= p -> (n <= m /\ m <= n)) -> n <= p -> n = m.
Proof. auto. Qed.

Definition is_fortytwo x := (x = 42).
Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof. auto. Abort.

Hint Unfold is_fortytwo.
Example auto_example_7': forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof. auto. Qed.

Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0. auto.
  - (* E_IfTrue *)
    + rewrite H in H5. discriminate.
  - (* E_IfFalse *)
    + rewrite H in H5. discriminate.
  - (* E_WhileFalse *)
    + rewrite H in H2. discriminate.
  - (* E_WhileTrue, b = false *) 
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b = true *) 
    assert (st' = st'0) as EQ1 by auto.
    subst st'0. auto.
Qed.

Theorem ceval_deterministic'_alt: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2...
  - (* E_Seq *)
    assert (st' = st'0) as EQ1...
    subst st'0...
  - (* E_IfTrue *)
    + rewrite H in H5. discriminate.
  - (* E_IfFalse *)
    + rewrite H in H5. discriminate.
  - (* E_WhileFalse *)
    + rewrite H in H2. discriminate.
  - (* E_WhileTrue, b = false *) 
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b = true *) 
    assert (st' = st'0) as EQ1...
    subst st'0...
Qed.

(* Chap 16.2 Searching For Hypotheses *)
Ltac rwinv H1 H2 := rewrite H1 in H2; inv H2.

Theorem ceval_deterministic'': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0. auto.
  - (* E_IfTrue *)
    + rwinv H5 H.
  - (* E_IfFalse *)
    + rwinv H5 H.
  - (* E_WhileFalse *)
    + rwinv H2 H.
  - (* E_WhileTrue, b = false *) 
    rwinv H4 H.
  - (* E_WhileTrue, b = true *) 
    assert (st' = st'0) as EQ1 by auto.
    subst st'0. auto.
Qed.

Ltac find_rwinv :=
  match goal with
    H1: ?E = true,
    H2: ?E = false
    |- _ => rwinv H1 H2
  end.

Theorem ceval_deterministic''': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; try find_rwinv; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0. auto.
  - (* E_WhileTrue, b = true *) 
    assert (st' = st'0) as EQ1 by auto.
    subst st'0. auto.
Qed.

Theorem ceval_deterministic'''': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; try find_rwinv; auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *. auto.
  - (* E_WhileTrue, b = true *) 
    rewrite (IHE1_1 st'0 H3) in *. auto.
Qed.

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _ => rewrite (H1 X H2) in *
  end.

Theorem ceval_deterministic''''': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; try find_rwinv; repeat find_eqn; auto.
Qed.

Module Repeat.

Inductive com : Type :=
  | CSkip
  | CAss (x: string) (a: aexp)
  | CSeq (c1 c2: com)
  | CIf (b: bexp) (c1 c2: com)
  | CWhile (b: bexp) (c: com)
  | CRepeat (c: com) (b: bexp).

Notation "'SKIP'" :=
   CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'REPEAT' c 'UNTIL' b 'END'" :=
  (CRepeat c b) (at level 80, right associativity).

Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40, st' at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st =[ WHILE b DO c END ]=> st''
  | E_RepeatEnd : forall st st' b c,
      st =[ c ]=> st' ->
      beval st' b = true ->
      st =[ REPEAT c UNTIL b END ]=> st'
  | E_RepeatLoop : forall st st' st'' b c,
      st =[ c ]=> st' ->
      beval st' b = false ->
      st' =[ REPEAT c UNTIL b END ]=> st'' ->
      st =[ REPEAT c UNTIL b END ]=> st''
where "st =[ c ]=> st'" := (ceval c st st').

Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
  intros st2 E2; inv E2; try find_rwinv; repeat find_eqn; auto.
  - (* E_RepeatEnd *)
    + find_rwinv.
  - (* E_RepeatLoop *)
     + find_rwinv.
Qed.

Theorem ceval_deterministic': forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
  intros st2 E2; inv E2; repeat find_eqn; try find_rwinv; auto.
Qed.

End Repeat.

(*** eapply & eauto ***)
Example ceval_example1:
  empty_st =[
    X ::= 2;;
    TEST X <= 1
      THEN Y ::= 3
      ELSE Z ::= 4
    FI
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2).
  - apply E_Ass. reflexivity.
  - apply E_IfFalse. reflexivity. apply E_Ass. reflexivity.
Qed.

Example ceval'_example1:
  empty_st =[
    X ::= 2;;
    TEST X <= 1
      THEN Y ::= 3
      ELSE Z ::= 4
    FI
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  eapply E_Seq.
  - apply E_Ass. reflexivity.
  - apply E_IfFalse. reflexivity.
    apply E_Ass. reflexivity.
Qed.

Hint Constructors ceval.
Hint Transparent state.
Hint Transparent total_map.
Definition st12 := (Y !-> 2 ; X !-> 1).
Definition st21 := (Y !-> 1 ; X !-> 2).

Example eauto_example: exists s',
  st21 =[ TEST X <= Y
      THEN Z ::= Y - X
      ELSE Y ::= X + Z
    FI
  ]=> s'.
Proof. eauto. Qed.

(* eauto & eapply is slower,
   we prefer to use auto & apply! *)
