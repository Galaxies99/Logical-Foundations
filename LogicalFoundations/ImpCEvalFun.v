(* Chap 14 ImpCEvalFun *)
(* Chap 14.1 A Broken Evaluator *)
From Coq Require Import omega.Omega.
From Coq Require Import Arith.Arith.
From LF Require Import Imp Maps.

Open Scope imp_scope.
Fixpoint ceval_step1 (st: state) (c: com) : state :=
  match c with
  | SKIP => st
  | l ::= a1 => (l !-> (aeval st a1); st)
  | c1 ;; c2 => 
    let st' := ceval_step1 st c1 in ceval_step1 st' c2
  | TEST b THEN c1 ELSE c2 FI =>
    if (beval st b) then ceval_step1 st c1
    else ceval_step1 st c2
  | WHILE b DO c END => st
  end.
Close Scope imp_scope.

(* Chap 14.2 A Step-Indexed Evaluator *)
Open Scope imp_scope.
Fixpoint ceval_step2 (st: state) (c: com) (i: nat) : state :=
  match i with
  | O => empty_st
  | S i' => 
    match c with
    | SKIP => st
    | l ::= a1 => (l !-> (aeval st a1); st)
    | c1 ;; c2 =>
      let st' := ceval_step2 st c1 i' in ceval_step2 st' c2 i'
    | TEST b THEN c1 ELSE c2 FI =>
      if (beval st b) then ceval_step2 st c1 i'
      else ceval_step2 st c2 i'
    | WHILE b DO c1 END =>
      if (beval st b) then let st' := ceval_step2 st c1 i' in 
                           ceval_step2 st' c i'
      else st
    end
  end.
Close Scope imp_scope.

Open Scope imp_scope.
Fixpoint ceval_step3 (st: state) (c: com) (i: nat) : option state :=
  match i with
  | O => None
  | S i' => 
    match c with
    | SKIP => Some st
    | l ::= a1 => Some (l !-> (aeval st a1); st)
    | c1 ;; c2 => 
      match (ceval_step3 st c1 i') with
      | Some st' => ceval_step3 st' c2 i'
      | None => None
      end
    | TEST b THEN c1 ELSE c2 FI =>
      if (beval st b) then ceval_step3 st c1 i'
      else ceval_step3 st c2 i'
    | WHILE b DO c1 END =>
      if (beval st b) then
        match (ceval_step3 st c1 i') with
        | Some st' => ceval_step3 st' c i'
        | None => None
        end
      else Some st
    end
  end.
Close Scope imp_scope.

Notation "'LETOPT' x <== e1 'IN' e2" := (
  match e1 with
  | Some x => e2
  | None => None
  end
) (right associativity, at level 60).

Open Scope imp_scope.
Fixpoint ceval_step (st: state) (c: com) (i: nat) : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
    | SKIP => Some st
    | l ::= a1 => Some (l !-> (aeval st a1); st)
    | c1 ;; c2 => LETOPT st' <== ceval_step st c1 i'
                  IN ceval_step st' c2 i'
    | TEST b THEN c1 ELSE c2 FI =>
      if (beval st b) then ceval_step st c1 i'
      else ceval_step st c2 i'
    | WHILE b DO c1 END =>
      if (beval st b) then LETOPT st' <== ceval_step st c1 i' IN ceval_step st' c i'
      else Some st
    end
  end.
Close Scope imp_scope.

Definition test_ceval (st: state) (c: com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.

Compute 
  (test_ceval empty_st
         (X ::= 2;;
          TEST (X <= 1)
            THEN Y ::= 3
            ELSE Z ::= 4
          FI)).

(* Exercise pup_to_n *)
Definition pup_to_n: com :=
  ( Y ::= 0;;
    WHILE (BNot (BEq X (ANum 0))) DO
      Y ::= Y + X;;
      X ::= X - 1
    END
  ).

Example pup_to_n_1 :
  test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.

(* Exercise peven *)
Definition peven: com :=
  ( Z ::= 1;;
    Y ::= X;;
    WHILE (BAnd (BNot (BEq Y (ANum 0))) (BNot (BEq Z (ANum 0)))) DO
      TEST (BEq (Y + Y) X) THEN Z ::= 0
      ELSE SKIP FI;;
      Y ::= Y - 1
    END;;
    Y ::= 0
   ).

Example peven_test1:
  test_ceval (X !-> 233) peven = Some (233, 0, 1).
Proof. reflexivity. Qed.

Example peven_test2:
  test_ceval (X !-> 200) peven = Some (200, 0, 0).
Proof. reflexivity. Qed.

Example peven_test_stop:
  test_ceval (X !-> 1000) peven = None.
Proof. reflexivity. Qed.

(* Chap 14.3 Relational vs. Step-Indexed Evaluation *)
Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      st =[ c ]=> st'.
Proof.
  intros c st st' H.
  destruct H as [i E].
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i'].
  - (* i = 0 *) intros. discriminate.
  - (* i = S i' *)
    intros c st st' H.
    destruct c; simpl in H; inversion H; subst; clear H.
    + (* SKIP *) constructor.
    + (* ::= *) constructor. reflexivity.
    + (* ;; *) destruct (ceval_step st c1 i') eqn: Heqr1.
      * apply E_Seq with s. apply IHi'. apply Heqr1. apply IHi'. apply H1.
      * discriminate.
    + (* TEST *)
      destruct (beval st b) eqn: Heqr.
      * constructor. apply Heqr. apply IHi', H1.
      * apply E_IfFalse. apply Heqr. apply IHi', H1.
    + (* WHILE *)
      destruct (beval st b) eqn: Heqr.
      * destruct (ceval_step st c i') eqn: Heqr1.
        { apply E_WhileTrue with s. apply Heqr. apply IHi'. apply Heqr1. 
          apply IHi'. apply H1. }
        { discriminate. }
      * injection H1 as H2. subst. apply E_WhileFalse. assumption.
Qed.

(* Exercise ceval_step__ceval_inf *)
(* Skipped *)

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 -> 
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
  induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - (* i1 = 0 *) discriminate.
  - (* i1 = S i1' *)
    destruct i2 as [|i2'].
    inversion Hle.
    assert (Hle': i1' <= i2') by omega.
    destruct c.
    + (* SKIP *) simpl in *. apply Hceval.
    + (* ::= *) simpl in *. apply Hceval.
    + (* ;; *) simpl in *.
      destruct (ceval_step st c1 i1') eqn: Heqst1'o.
      * apply (IHi1' i2') in Heqst1'o.
        rewrite Heqst1'o. simpl in *.
        apply (IHi1' i2') in Hceval; assumption. apply Hle'.
      * discriminate.
    + (* TEST *) simpl in *.
      destruct (beval st b); 
      apply IHi1' with (i2 := i2') in Hceval;
      assumption.
    + (* WHILE *)
      simpl in *.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * apply (IHi1' i2') in Heqst1'o. try assumption.
        rewrite -> Heqst1'o. simpl in *.
        apply (IHi1' i2') in Hceval; assumption. apply Hle'.
      * discriminate.
Qed.

(* Exercise ceval__ceval_step *)
Theorem ceval__ceval_step: forall c st st',
  st =[ c ]=> st' ->
  exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
  + (* E_Skip *)exists 1. reflexivity.
  + (* E_Ass *) exists 1. simpl. subst. reflexivity.
  + (* E_Seq *) destruct IHHce1 as [i1 H1].
    destruct IHHce2 as [i2 H2].
    exists (1 + i1 + i2). simpl.
    destruct (ceval_step st c1 (i1 + i2)) eqn: Hstep.
    * assert (st' = s). 
      { apply (ceval_step_more i1 (i1 + i2)) in H1.
        rewrite H1 in Hstep. inversion Hstep. auto. omega. }
      subst s.
      apply (ceval_step_more i2 (i1 + i2)). omega. apply H2.
    * apply (ceval_step_more i1 (i1 + i2)) in H1. rewrite H1 in Hstep. discriminate. omega.
  + (* E_IfTrue *) destruct IHHce as [i H'].
    exists (1 + i). simpl. rewrite H. apply H'.
  + (* E_IfFalse *) destruct IHHce as [i H'].
    exists (1 + i). simpl. rewrite H. apply H'.
  + (* E_WhileFalse *) exists 1.
    simpl. rewrite H. reflexivity.
  + (* E_WhileTrue *)
    destruct IHHce1 as [i1 H1].
    destruct IHHce2 as [i2 H2].
    exists (1 + i1 + i2).
    simpl. rewrite H.
    destruct (ceval_step st c (i1 + i2)) eqn: Hstep.
    * assert (s = st').
      { apply (ceval_step_more i1 (i1 + i2)) in H1. 
        rewrite H1 in Hstep. inversion Hstep. auto. omega. }
      subst s.
      apply (ceval_step_more i2 (i1 + i2)). omega. apply H2.
    * apply (ceval_step_more i1 (i1 + i2)) in H1. rewrite H1 in Hstep. discriminate. omega.
Qed.

Theorem ceval_and_ceval_step_coincide: forall c st st',
  st =[ c ]=> st' <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

(* Chap 14.4 Determinism of Evaluation Again *)
Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros.
  apply ceval_and_ceval_step_coincide in H.
  apply ceval_and_ceval_step_coincide in H0.
  destruct H as [i1 H1].
  destruct H0 as [i2 H2].
  apply (ceval_step_more i1 (i1 + i2)) in H1.
  apply (ceval_step_more i2 (i1 + i2)) in H2.
  rewrite H1 in H2.
  inversion H2.
  auto. omega. omega.
Qed.
