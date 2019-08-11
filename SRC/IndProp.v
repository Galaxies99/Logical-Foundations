(* Chap 7 IndProp *)
Set Warnings "-notation-overridden,-parsing".
From SRC Require Export Logic.
Require Coq.omega.Omega.

(* Chap 7.1 Inductively Defined Propositions *)
Inductive even: nat -> Prop :=
  | ev_0: even 0
  | ev_SS (n: nat) (H: even n) : even (S (S n)).

Inductive myeven: nat -> Prop :=
  | myev_0: myeven 0
  | myev_SS: forall n, myeven n -> myeven (S (S n)).

Theorem ev_4: even 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Theorem ev_4': even 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

Theorem ev_plus4: forall n, even n -> even (4 + n).
Proof.
  intros n.
  simpl. intros H.
  apply ev_SS, ev_SS, H.
Qed.

(* Exercise ev_double *)
Theorem ev_double: forall n,
  even (double n).
Proof.
  intros.
  induction n.
  - simpl. apply ev_0.
  - simpl. apply ev_SS, IHn.
Qed.

(* Chap 7.2 Using Evidence in Proofs *)
(* Chap 7.2.1 Inversion on Evidence *)
Theorem ev_inversion:
  forall n: nat, even n -> (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros.
  destruct H.
  - left. reflexivity.
  - right. exists n.
    split.
    + reflexivity.
    + apply H.
Qed.

Theorem ev_minus2: forall n,
  even n -> even (pred (pred n)).
Proof.
  intros.
  destruct H.
  - simpl. apply ev_0.
  - simpl. apply H.
Qed.

Theorem evSS_ev: forall n,
  even (S (S n)) -> even n.
Proof.
  intros.
  apply ev_inversion in H.
  destruct H.
  - discriminate H.
  - destruct H as [n' [H1 H2]].
    injection H1 as H1.
    rewrite H1. apply H2.
Qed.

Theorem evSS_ev': forall n,
  even (S (S n)) -> even n.
Proof.
  intros.
  inversion H.
  apply H1.
Qed.

Theorem one_not_even: ~ even 1.
Proof.
  unfold not.
  intros.
  apply ev_inversion in H.
  destruct H.
  - discriminate H.
  - destruct H as [n' [H1 H2]].
    discriminate H1.
Qed.

(* Exercise inversion_practice *)
Theorem SSSSev__even: forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
  intros.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem SSSSev__even': forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
  intros.
  apply evSS_ev, evSS_ev, H.
Qed.

(* Theorem even5_nonsense *)
Theorem even5_nonsense:
  even 5 -> 2 + 2 = 9.
Proof.
  intros H.
  exfalso.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

Theorem inversion_ex1: forall n m o: nat,
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros. inversion H. reflexivity.
Qed.

Theorem inversion_ex2: forall n: nat, 
  S n = O -> 2 + 2 = 5.
Proof.
  intros. inversion H.
Qed.

(* Chap 7.2.2 Induction on Evidence *)
Lemma ev_even: forall n,
  even n -> exists k, n = double k.
Proof.
  intros. 
  induction H.
  - exists 0. reflexivity.
  - destruct IHeven.
    rewrite H0.
    exists (S x).
    simpl. reflexivity.
Qed.

Theorem ev_sum: forall n m, even n -> even m -> even (n + m).
Proof.
  intros.
  induction H.
  - simpl. apply H0.
  - simpl. apply ev_SS, IHeven.
Qed.

Inductive even': nat -> Prop :=
  | even'_0: even' 0
  | even'_2: even' 2
  | even'_sum n m (Hn: even' n) (Hm: even' m): even' (n + m).

Theorem even'_ev: forall n, even' n <-> even n.
Proof.
  intros. split.
  - intros. induction H.
    + apply ev_0.
    + apply ev_SS, ev_0.
    + apply ev_sum. apply IHeven'1. apply IHeven'2.
  - intros. induction H.
    + apply even'_0.
    + assert (I: S (S n) = 2 + n).
      { simpl. reflexivity. }
      rewrite I. apply even'_sum.
      apply even'_2. apply IHeven.
Qed.

Theorem ev_ev__ev: forall n m,
  even (n+m) -> even n -> even m.
Proof.
  intros.
  induction H0.
  simpl in H.
  - apply H.
  - apply IHeven.
    simpl in H.
    apply evSS_ev in H.
    apply H.
Qed.

Lemma plus_twice_eq_double:
  forall n, n + n = double n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite <- IHn.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Theorem ev_plus_plus: forall n m p,
  even (n+m) -> even (n+p) -> even (m+p).
Proof. 
  intros.
  apply ev_ev__ev with (n := n + n).
  rewrite plus_assoc.
  assert(I: n + n + m = n + m + n).
  { rewrite <- plus_assoc. rewrite plus_comm. reflexivity. }
  rewrite I. rewrite <- plus_assoc.
  apply ev_sum.
  apply H.
  apply H0.
  rewrite plus_twice_eq_double.
  apply ev_double.
Qed.

(* Chap 7.3 Inductive Relations *)
Module Playground.

Inductive le: nat -> nat -> Prop :=
  | le_n n: le n n
  | le_S n m (H: le n m): le n (S m).

Notation "m <= n" := (le m n).

Theorem test_le1: 3 <= 3.
Proof. apply le_n. Qed.

Theorem test_le2: 3 <= 6.
Proof. apply le_S, le_S, le_S, le_n. Qed.

Theorem test_le3: (2 <= 1) -> 2 + 2 = 5.
Proof. intros. inversion H. inversion H2. Qed.

End Playground.

Definition lt (n m: nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of: nat -> nat -> Prop :=
  | sq n: square_of n (n * n).

Inductive next_nat: nat -> nat -> Prop :=
  | nn n: next_nat n (S n).

Inductive next_even: nat -> nat -> Prop :=
  | ne_1 n: even (S n) -> next_even n (S n)
  | ne_2 n (H: even (S (S n))): next_even n (S (S n)).

(* Exercise total_relation *)
Inductive total_relation: nat -> nat -> Prop :=
  | re_0_0: total_relation 0 0
  | re_S_0 n (H: total_relation n 0): total_relation (S n) 0
  | re_n_S n m (H: total_relation n m): total_relation n (S m).

(* Exercise empty_relation *)
Inductive empty_relation: nat -> nat -> Prop := .

(* Exercise le_exercises *)
Lemma le_trans: forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  induction H0.
  - apply H.
  - simpl. apply le_S, IHle.
Qed.

Theorem O_le_n: forall n, 0 <= n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - apply le_S, IHn.
Qed.

Theorem n_le_m__Sn_le_Sm: forall n m, n <= m -> S n <= S m.
Proof.
  intros.
  induction H.
  - reflexivity.
  - apply le_S, IHle.
Qed.

Theorem Sn_le_Sm__n_le_m: forall n m, S n <= S m -> n <= m.
Proof.
  intros.
  inversion H.
  - apply le_n.
  - apply (le_trans n (S n)).
    + apply le_S, le_n.
    + apply H1.
Qed.

Theorem le_plus_l: forall a b, a <= a + b.
Proof.
  intros.
  induction b.
  - rewrite <- plus_n_O. apply le_n.
  - rewrite <- plus_n_Sm. apply le_S, IHb.
Qed.

Theorem plus_lt: forall n1 n2 m, n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros.
  induction H.
  - split.
    + apply n_le_m__Sn_le_Sm, le_plus_l.
    + apply n_le_m__Sn_le_Sm.
      rewrite <- plus_comm.
      apply le_plus_l.
  - destruct IHle as [H1 H2].
    split.
    + apply le_S, H1.
    + apply le_S, H2.
Qed.

Theorem lt_S: forall n m, n < m -> n < S m.
Proof.
  unfold lt.
  intros.
  apply le_S, H.
Qed.

Theorem leb_complete: forall n m, n <=? m = true -> n <= m.
Proof.
  intros.
  generalize dependent n.
  induction m.
  - intros. induction n.
    + apply le_n.
    + inversion H.
  - intros. induction n.
    + apply O_le_n.
    + apply n_le_m__Sn_le_Sm, IHm, H.
Qed.

(* This is the version of induction n. *)
Theorem leb_correct: forall n m, n <= m -> n <=? m = true.
Proof.
  intros n.
  induction n.
  - intros. inversion H.
    + reflexivity.
    + reflexivity.
  - intros. inversion H.
    + simpl. rewrite <- leb_refl. reflexivity.
    + simpl. apply IHn. apply le_trans with (n := S n).
      apply le_S, le_n. apply H0.
Qed.

Theorem leb_true_trans: forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros.
  apply leb_correct.
  apply leb_complete in H.
  apply leb_complete in H0.
  apply le_trans with (n := m).
  apply H.
  apply H0.
Qed.
(* Ques: how to use "induction" to proof this? *)

(* Exercise leb_iff *)
Theorem leb_iff: forall n m, n <=? m = true <-> n <= m.
Proof.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Module R.
(* Exercise R_provability, R_fact *)
Inductive R: nat -> nat -> nat -> Prop :=
   | c1: R 0 0 0
   | c2 m n o (H: R m n o): R (S m) n (S o)
   | c3 m n o (H: R m n o): R m (S n) (S o)
   | c4 m n o (H: R (S m) (S n) (S (S o))): R m n o
   | c5 m n o (H: R m n o): R n m o.

Definition fR: nat -> nat -> nat := plus.

Theorem R_equiv_fR: forall m n o, R m n o <-> fR m n = o.
Proof.
  intros. split.
  - intros. induction H.
    + reflexivity.
    + unfold fR. simpl.
      unfold fR in IHR.
      apply f_equal, IHR.
    + unfold fR. rewrite <- plus_n_Sm.
      unfold fR in IHR.
      apply f_equal, IHR.
    + unfold fR. unfold fR in IHR. simpl in IHR.
      injection IHR. intros.
      rewrite <- plus_n_Sm in H0. 
      injection H0 as H0. apply H0.
    + unfold fR. unfold fR in IHR.
      rewrite plus_comm. apply IHR.
  - generalize dependent n. 
    generalize dependent o.
    induction m.
    + intros n. induction n.
      * intros. simpl in H. rewrite H. apply c1.
      * intros. simpl in H. simpl in IHn. rewrite H. apply c3, IHn. reflexivity.
    + intros n. induction n.
      * intros. discriminate H.
      * intros. simpl in H. injection H as H. apply c2. apply IHm, H.
Qed.

End R.

(* Exercise subsequence *)
Inductive subseq {X: Type}: list X -> list X -> Prop :=
  | empty l: subseq [] l
  | remove_one x l1 l2 (H: subseq l1 l2): subseq l1 (x :: l2)
  | remove_both x l1 l2 (H: subseq l1 l2): subseq (x :: l1) (x :: l2).

Theorem subseq_refl: forall X (l: list X), subseq l l.
Proof.
  intros.
  induction l.
  - apply empty.
  - apply remove_both, IHl.
Qed.

Theorem subseq_app: forall X (l1 l2 l3: list X), subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H. 
  - apply empty.
  - simpl. apply remove_one, IHsubseq.
  - simpl. apply remove_both, IHsubseq.
Qed.

Lemma subset_empty_is_empty: forall X (l: list X), subseq l [] -> l = [].
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Theorem subseq_trans: forall X (l1 l2 l3: list X), subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros.
  generalize dependent l1. 
  induction H0.
  - intros. apply subset_empty_is_empty in H.
    rewrite H. apply empty.
  - intros. apply remove_one, IHsubseq, H.
  - intros. inversion H.
    + apply empty.
    + apply remove_one, IHsubseq, H3.
    + apply remove_both, IHsubseq, H3.
Qed.

(* Exercise R_provability2 *)
Module Ex_R.

Inductive R: nat -> list nat -> Prop :=
  | c1: R 0 []
  | c2: forall n l, R n l -> R (S n) (n :: l)
  | c3: forall n l, R (S n) l -> R n l.

Example R_ex1: R 2 [1; 0].
Proof. apply c2, c2, c1. Qed.

Example R_ex2: R 1 [1; 2; 1; 0].
Proof. apply c3, c2, c3, c3, c2, c2, c2, c1. Qed.

(* Example R_ex3: R 6 [3; 2; 1; 0]. This cannot be proved. *)

End Ex_R.

(* Chap 7.4 Case Study: Regular Expressions *) 
Inductive reg_exp {T: Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t: T)
  | App (r1 r2: reg_exp)
  | Union (r1 r2: reg_exp)
  | Star (r: reg_exp).

Inductive exp_match {T}: list T -> reg_exp -> Prop :=
  | MEmpty: exp_match [] EmptyStr
  | MChar x: exp_match [x] (Char x)
  | MApp s1 re1 s2 re2 (H1: exp_match s1 re1) (H2: exp_match s2 re2): exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2 (H1: exp_match s1 re1): exp_match s1 (Union re1 re2)
  | MUnionR s2 re1 re2 (H2: exp_match s2 re2): exp_match s2 (Union re1 re2)
  | MStar0 re: exp_match [] (Star re)
  | MStarApp s1 s2 re (H1: exp_match s1 re) (H2: exp_match s2 (Star re)): exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1: [1] =~ Char 1.
Proof. apply MChar. Qed.

Example reg_exp_ex2: [1; 2] =~ App (Char 1) (Char 2).
Proof. 
  apply (MApp [1] (Char 1) [2] (Char 2)).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3: ~([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l: list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4: [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  apply (MApp [1] _ [2; 3]).
  - apply MChar.
  - apply (MApp [2] _ [3]).
    + apply MChar.
    + apply (MApp [3] _ []).
      * apply MChar.
      * apply MEmpty.
Qed.

Lemma MStar1:
  forall T s (re: @reg_exp T), s =~ re -> s =~ Star re.
Proof.
  intros.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(* Example exp_match_ex1 *)
Lemma empty_is_empty: forall T (s: list T), ~(s =~ EmptySet).
Proof.
  unfold not. intros. inversion H.
Qed.

Lemma MUnion': forall T (s: list T) (re1 re2: @reg_exp T),
  s =~ re1 \/ s =~ re2 -> s =~ (Union re1 re2).
Proof.
  intros. destruct H as [H1 | H2].
  - apply (MUnionL s re1 re2), H1.
  - apply (MUnionR s re1 re2), H2.
Qed.

Lemma MStar': forall T (ss: list (list T)) (re: reg_exp),
  (forall s, In s ss -> s =~ re) -> fold app ss [] =~ Star re.
Proof.
  intros. induction ss.
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
    + apply H. simpl. left. reflexivity.
    + apply IHss. intros. apply H. simpl. right. apply H0.
Qed.

(* Exercise reg_exp_of_list_spec *)
Lemma reg_exp_of_list_spec: forall T (s1 s2: list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof. 
  split.
  - generalize dependent s1.
    induction s2.
    + intros. simpl in H. inversion H. reflexivity.
    + intros. simpl in H. inversion H. apply IHs2 in H4. 
      inversion H3. rewrite H4. simpl. reflexivity.
  - generalize dependent s2.
    induction s1.
    + intros. rewrite <- H. simpl. apply MEmpty.
    + intros. rewrite <- H. simpl.
      replace (x :: s1) with ([x] ++ s1).
      apply MApp.
      * apply MChar. 
      * apply IHs1. reflexivity.
      * simpl. reflexivity.
Qed.

Fixpoint re_chars {T} (re: reg_exp): list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match: forall T (s: list T) (re: reg_exp) (x: T),
  s =~ re -> In x s -> In x (re_chars re).
Proof.
  intros.
  induction H.
  - simpl in H0. simpl. apply H0.
  - simpl in H0. simpl. apply H0.
  - simpl. rewrite In_app_iff in *.
    destruct H0 as [H2 | H3].
    + left. apply IHexp_match1, H2.
    + right. apply IHexp_match2, H3.
  - simpl. rewrite In_app_iff.
    left. apply IHexp_match, H0.
  - simpl. rewrite In_app_iff.
    right. apply IHexp_match, H0.
  - destruct H0.
  - simpl in *. rewrite In_app_iff in *.
    destruct H0 as [H2 | H3].
    + apply IHexp_match1, H2.
    + apply IHexp_match2, H3.
Qed.

(* Exercise re_not_empty *)
Fixpoint re_not_empty {T: Type} (re: @reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char t => true
  | App r1 r2 => (re_not_empty r1) && (re_not_empty r2)
  | Union r1 r2 => (re_not_empty r1) || (re_not_empty r2)
  | Star r => true
  end.

Lemma re_not_empty_correct: forall T (re: @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros.
  split.
  - induction re.
    + intros [s H]. inversion H.
    + reflexivity.
    + reflexivity.
    + intros [s H]. inversion H. simpl.
      apply andb_true_iff. split.
      * apply IHre1. exists s1. apply H3.
      * apply IHre2. exists s2. apply H4.
    + intros [s H]. inversion H.
      * simpl. 
        apply orb_true_iff. left.
        apply IHre1. exists s. apply H2. 
      * simpl.
        apply orb_true_iff. right.
        apply IHre2. exists s. apply H1.
    + reflexivity.
  - induction re.
    + intros. discriminate H.
    + intros. exists []. apply MEmpty.
    + intros. exists [t]. apply MChar.
    + intros. inversion H.
      apply andb_true_iff in H1.
      destruct H1 as [H1 H2].
      induction IHre1. induction IHre2.
      exists (x ++ x0). apply MApp. apply H0. apply H3. apply H2. apply H1.
    + intros. inversion H.
      apply orb_true_iff in H1.
      destruct H1 as [H1 | H2].
      * induction IHre1. exists x. apply MUnionL. apply H0. apply H1.
      * induction IHre2. exists x. apply MUnionR. apply H0. apply H2.
    + intros. exists []. apply MStar0.
Qed.

(* The remember Tactic *)
Lemma star_app: forall T (s1 s2: list T) (re: reg_exp),
  s1 =~ Star re -> s2 =~ Star re -> s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1. 
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - injection Heqre'. 
    intros. simpl. apply H0.
  - injection Heqre'. 
    intros. rewrite <- app_assoc.
    apply MStarApp.
    + apply H1_.
    + apply IHexp_match2.
      * rewrite H. reflexivity.
      * apply H0.
Qed.

(* Exercise exp_match_ex2 *)
Lemma MStar'': forall T (s: list T) (re: reg_exp),
  s =~ Star re ->
  exists ss: list (list T), s = fold app ss [] /\ 
  exists s', In s' ss -> s' =~ re.
Proof.
  intros.
  remember (Star re) as re'.
  induction H.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists []. simpl. split.
    + reflexivity.
    + exists []. intros. exfalso. apply H.
  - inversion Heqre'. 
    apply IHexp_match2 in Heqre'.
    destruct Heqre' as [ss [H3 H4]].
    exists ([s1] ++ ss).
    split.
    + simpl. rewrite <- H3. reflexivity.
    + simpl. exists s1.
      intros. rewrite H2 in H. apply H.
Qed.

(* Exercise pumping *)
Module Pumping.

Fixpoint pumping_constant {T} (re: @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 => pumping_constant re1 + pumping_constant re2
  | Union re1 re2 => pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Fixpoint napp {T} (n: nat) (l: list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m: nat) (l: list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Import Coq.omega.Omega.
Lemma pumping: forall T (re: @reg_exp T) s,
  s =~ re -> pumping_constant re <= length s ->
  exists s1 s2 s3, s = s1 ++ s2 ++ s3 /\ s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. omega.
  - (* MChar *)
    simpl. omega.
  - (* MApp *)
    simpl. intros. 
    rewrite app_length in H.
    apply Nat.add_le_cases in H.
    destruct H as [H | H].
    + apply IH1 in H. destruct H as [s3 [s4 [s5 [H1 [H2 H3]]]]].
      exists s3, s4, (s5 ++ s2). rewrite H1. 
      rewrite <- app_assoc. rewrite <- app_assoc. split.
      * reflexivity.
      * split.
        { apply H2. }
        { intros. rewrite -> app_assoc. rewrite -> app_assoc. 
          rewrite <- app_assoc with (m := (napp m s4)).
          apply MApp. apply H3. apply Hmatch2. }
    + apply IH2 in H. destruct H as [s3 [s4 [s5 [H1 [H2 H3]]]]].
      exists (s1 ++ s3), s4, s5. rewrite H1.
      rewrite <- app_assoc. split.
      * reflexivity.
      * split.
        { apply H2. }
        { intros. rewrite <- app_assoc.
          apply MApp. apply Hmatch1.
          apply H3. }
  - (* MUnionL *)
    simpl. intros.
    apply le_trans with (n := pumping_constant re1) in H.
    + apply IH in H. destruct H as [s2 [s3 [s4 [H1 [H2 H3]]]]].
      exists s2, s3, s4. rewrite H1. split.
      * reflexivity.
      * split.
        { apply H2. }
        { intros. apply MUnionL. apply H3. }
    + apply le_plus_l.
  - (* MUnionR *)
    simpl. intros. 
    rewrite plus_comm in H.
    apply le_trans with (n := pumping_constant re2) in H.
    apply IH in H. destruct H as [s1 [s3 [s4 [H1 [H2 H3]]]]].
    + exists s1, s3, s4. rewrite H1. split.
      * reflexivity.
      * split.
        { apply H2. }
        { intros. apply MUnionR. apply H3. }
    + apply le_plus_l.
  - (* MStar0 *)
    simpl. intros. inversion H.
  - (* MStarApp *)
    simpl. intros. rewrite app_length in H.
    destruct s1.
    + destruct s2.
      * inversion H.
      * simpl in H. simpl in IH2. apply IH2 in H.
        destruct H as [s1 [s3 [s4 [H1 [H2 H3]]]]].
        rewrite H1. simpl. exists s1, s3, s4. split.
        { reflexivity. }
        { split.
          - apply H2.
          - apply H3. }
    + exists [], (x :: s1), s2. split.
      * reflexivity. 
      * split.
        { intro. discriminate. }
        { intro. simpl. apply star_app.
          - induction m.
            + simpl. apply MStar0.
            + remember (x :: s1) as s1'.
              simpl. apply star_app.
              rewrite <- app_nil_r with (l := s1').
              apply MStarApp.
              apply Hmatch1.
              apply MStar0.
              apply IHm.
          - apply Hmatch2. }
Qed.

End Pumping.

(* Chap 7.5 Case Study: Improving Reflection *)
Theorem filter_not_empty_In: forall n l,
  filter (fun x => n =? x) l <> [] -> In n l.
Proof.
  intros n l.
  induction l.
  - simpl. intros. apply H. reflexivity.
  - simpl. destruct (n =? x) eqn: H.
    + intros. rewrite eqb_eq in H.
      left. rewrite H. reflexivity.
    + intros. right. apply IHl. apply H0.
Qed.

Inductive reflect (P: Prop) : bool -> Prop :=
  | ReflectT (H: P): reflect P true
  | ReflectF (H: ~P): reflect P false.

Theorem iff_reflect: forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros. destruct b.
  - apply ReflectT. apply H. reflexivity.
  - apply ReflectF. rewrite H. discriminate.
Qed.

(* Exercise reflect_iff *)
Theorem reflect_iff: forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H.
  induction H.
  - split.
    + reflexivity.
    + intros. apply H.
  - split.
    + intros. apply H in H0. exfalso. apply H0.
    + intros. discriminate H0.
Qed.

Lemma eqbP: forall n m, reflect (n = m) (n =? m).
Proof.
  intros. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

Theorem filter_not_empty_In': forall n l,
  filter (fun x => n =? x) l <> [] -> In n l.
Proof.
  intros n l.
  induction l.
  - simpl. intros. apply H. reflexivity.
  - simpl. destruct (eqbP n x) as [H | H]. 
    + intros. rewrite H. left. reflexivity.
    + intros. right. apply IHl. apply H0.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

(* Exercise eqbP_practice *)
Theorem eqbP_practice: forall n l,
  count n l = 0 -> ~ (In n l).
Proof.
  intros n l.
  induction l.
  - intros. simpl. 
    unfold not. intros H'. apply H'.
  - intros. simpl.
    destruct (eqbP n x) as [H' | H'].
    + rewrite H' in H.
      simpl in H. rewrite <- eqb_refl in H.
      discriminate H.
    + unfold not. intros.
      destruct H0 as [H1 | H2].
      * unfold not in H'. symmetry in H1. 
        apply H' in H1. apply H1.
      * simpl in H. unfold not in IHl. 
        apply IHl in H2.
        apply H2.
        replace (n =? x) with false in H.
        simpl in H. apply H.
        destruct (n =? x).
        { discriminate. } { reflexivity. }
Qed.
(* Ques: too long? *)

(* Chap 7.6 Additional Exercises *)
(* Exercise nostutter_defn *)
Definition check_is_not_head {X: Type} (l: list X) (x: X) : Prop :=
  match l with
  | [] => True
  | h :: t => x <> h
  end.

Inductive nostutter {X: Type} : list X -> Prop :=
  | nostutter_nil: nostutter []
  | nostutter_add x l (H: check_is_not_head l x) (I: nostutter l): nostutter (x :: l).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  repeat constructor; apply eqb_neq; auto.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof.
  repeat constructor; apply eqb_neq; auto.
Qed.

Example test_nostutter_3: nostutter [5].
Proof.
  repeat constructor; apply eqb_false; auto. 
Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof.
  intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H0; auto. 
Qed.


(* Exercise filter_challenge *)
Inductive merge_in_order {X: Type}: list X -> list X -> list X -> Prop :=
  | Empty_MIO: merge_in_order [] [] []
  | MergeLeft: forall l1 l2 l x, merge_in_order l1 l2 l -> merge_in_order (x :: l1) l2 (x :: l)
  | MergeRight: forall l1 l2 l x, merge_in_order l1 l2 l -> merge_in_order l1 (x :: l2) (x :: l).

Theorem merge_filter_only: forall X (l1 l2 l: list X) (test: X -> bool),
  merge_in_order l1 l2 l -> 
  (forall x, In x l1 -> test x = true) ->
  (forall x, In x l2 -> test x = false) ->
  filter test l = l1.
Proof.
  intros.
  induction H.
  - reflexivity.
  - simpl. rewrite -> H0.
    + apply IHmerge_in_order in H1.
      rewrite H1. reflexivity.
      intros. apply H0. simpl. right. apply H2.
    + simpl. left. reflexivity.
  - simpl.
    destruct (test x) eqn: Htest.
    + assert (Hcontra: test x = false).
      { apply H1. simpl. left. reflexivity. }
      rewrite Hcontra in Htest.
      discriminate Htest.
    + apply IHmerge_in_order in H0.
      apply H0.
      intros. apply H1. simpl. right. apply H2.
Qed.

(* Exercise filter_challenge_2 *)
Print subseq.
Theorem filter_behavior: forall X (l sl: list X) (test: X -> bool),
  subseq sl l ->
  forallb test sl = true ->
  length sl <= length (filter test l).
Proof.
  intros X l sl test H1.
  induction H1.
  - intros H2. simpl. apply O_le_n.
  - intros H2. simpl.
    destruct (test x) eqn: Htest.
    + simpl. apply le_S. apply IHsubseq. apply H2.
    + simpl. apply IHsubseq. apply H2.
  - intros H2. simpl.
    destruct (test x) eqn: Htest.
    + simpl. apply n_le_m__Sn_le_Sm. apply IHsubseq.
      simpl in H2. rewrite Htest in H2. apply H2.
    + simpl in H2. rewrite Htest in H2. discriminate H2.
Qed.

(* Exercise palindromes *) 
Inductive pal {X: Type}: list X -> Prop :=
  | Empty_P: pal []
  | One_P: forall c, pal [c]
  | Add_P: forall c l, pal l -> pal (c :: l ++ [c]).

Theorem pal_app_rev: forall X (l: list X), pal (l ++ rev l).
Proof.
  intros.
  induction l.
  - simpl. apply Empty_P.
  - simpl. rewrite app_assoc. apply Add_P, IHl.
Qed.

Theorem pal_rev: forall X (l: list X), pal l -> l = rev l.
Proof.
  intros.
  induction H.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite <- IHpal. reflexivity.
Qed.

(* Exercise palindrome_converse *)
(* 
   First we prove that:
   If the Prop has the following property:
     If a Prop is true for all the numbers less than n, then it's true for n.
   Then we can conclude the Prop is true for all natural numbers n.
*)
Lemma Prop_induction_for_nat: forall (P: nat -> Prop),
  (forall n, (forall m, m < n -> P m) -> P n) ->
  (forall n, P n).
Proof.
  intros. 
  apply H.
  induction n.
  - intros. inversion H0.
  - apply H in IHn as Hn.
    intros.
    inversion H0.
    + apply Hn.
    + apply IHn. unfold lt. apply H2.
Qed.

(* 
   Then we prove a special nat induction way which is:
   The Prop is true for 0 and 1, and if the Prop is true for n, then it's true for (n + 2).
   From this we can conclude that the Prop is true for all n.
   We cannot use simple induction here because even and odd should be split, so we use the
   Prop_induction_for_nat we state before.
*)
Lemma nat_induction: forall (P: nat -> Prop),
  P 0 -> P 1 -> (forall n, P n -> P (n + 2)) ->
  (forall n, P n).
Proof.
  intros.
  apply Prop_induction_for_nat.
  intros m H2.
  destruct m.
  - apply H.
  - destruct m.
    + apply H0.
    + assert (I: S (S m) = m + 2). { rewrite -> plus_comm. reflexivity. }
      rewrite I. apply H1.
      apply H2. unfold lt.
      apply le_S. apply le_n.
Qed.

(*
   Next, we think about Prop connected to the list.
   Because we want to prove palindromes_converse Theorem, so we need to reduce the length
   twice a step. Then we need the following Lemma. It state if we can prove that forall n, 
   lists that have length n satisfy Prop, we can prove all the lists satisfy the Prop.
   This lemma is quite easy to prove though, by connecting n with (length l).
*)
Lemma length_induction: forall X (P: list X -> Prop),
  (forall n l, length l = n -> P l) ->
  forall l, P l.
Proof.
  intros.
  apply H with (n := length l).
  reflexivity.
Qed.

(*
   This is Lemma state that "list l is empty" equals to "list (rev l) is empty"
*)
Lemma rev_empty_eq_empty: forall X (l: list X), rev l = [] <-> l = [].
Proof.
  split.
  - intros. 
    destruct l eqn: Hl.
    + reflexivity.
    + rewrite <- rev_involutive with (l := (x :: l0)).
      rewrite H. reflexivity.
  - intros. rewrite H. reflexivity.
Qed.

(*
   This is a Lemma shows that if a list has length (n + 2), we can get its head and tail
   off the list, then its length becomes n.
*)
Lemma list_length_SS: forall X (l: list X) n,
  (length l = n + 2) -> exists l' x y, l = [x] ++ l' ++ [y] /\ length l' = n.
Proof.
  intros.
  destruct l.
  - rewrite <- plus_comm in H. simpl in H. discriminate.
  - rewrite <- plus_comm in H. simpl in H. injection H as H.
    destruct (rev l) eqn: Hr.
    + assert (Hempty: l = []).
      { apply rev_empty_eq_empty, Hr. }
      rewrite Hempty in H. simpl in H. discriminate.
    + exists (rev l0), x, x0.
      assert(I: l = rev l0 ++ [x0]).
        { rewrite <- rev_involutive with (l := l).
          rewrite Hr. simpl. reflexivity. }
      split.
      * rewrite I. simpl. reflexivity.
      * rewrite -> I in H. 
        rewrite app_length in H. 
        simpl in H.
        rewrite <- plus_n_Sm in H.
        injection H as H.
        rewrite <- plus_n_O in H.
        apply H.
Qed.

(* 
   This is a Lemma shows our induction about palindromes:
   i) Empty list satisfies the Prop
   ii) List which has only one element satisfies.
   iii) If we have a satisfied list l, we can add an element to the list head and add
   add an element to its tail, the new list still satisfies.
   If a Prop satisfies all the point above, then it's true for all the list.

   To prove this, we start with a induction on length using length_induction.
   and we make Pn as our new Prop (nat (here is length) -> Prop).
   i) try to prove Pn 0 is true.
   ii) try to prove Pn 1 is true.
   iii) try to prove if Pn n is true, then Pn (n + 2) is true.
        In this step, we may use the Lemma list_length_SS above to get the head and tail
        of the list and reduce the length by 2, so that we can use Pn n.
   iv) if we prove the things above, then we can prove forall list it is true.
       By introducing the length n of any list, and using nat_induction to prove Pn n is 
       true).
*)
Lemma palindrome_induction: forall X (P: list X -> Prop),
  P [] ->
  (forall x: X, P [x]) ->
  (forall (x y: X) (l: list X), P l -> P (x :: l ++ [y])) ->
  (forall l, P l).
Proof. 
  intros.
  apply length_induction.
  remember (fun n => (forall l, length l = n -> P l)) as Pn.
  assert (Pn0: Pn 0).
  {
    rewrite HeqPn. intros. destruct l0.
    - apply H.
    - simpl in H2. discriminate.
  }
  assert (Pn1: Pn 1).
  {
    rewrite HeqPn. intros.
    destruct l0.
    - apply H.
    - destruct l0.
      + apply H0.
      + simpl in H2. discriminate.
  }
  assert (PnTrans: forall n, Pn n -> Pn (n + 2)).
  {
    rewrite HeqPn.
    intros.
    apply list_length_SS in H3 as H4.
    destruct H4 as [l' [x [y [H4 H5]]]].
    apply H2 in H5.
    rewrite H4. apply H1, H5.
  }
  intros n.
  assert (Pnn: Pn n).
  { apply nat_induction. apply Pn0. apply Pn1. apply PnTrans. }
  rewrite HeqPn in Pnn.
  apply Pnn.
Qed.

Lemma equal_length_eq: forall X (l1 l2: list X),
  l1 = l2 -> length l1 = length l2.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma app_one: forall X (l1 l2: list X) x y, l1 ++ [x] = l2 ++ [y] -> l1 = l2 /\ x = y.
Proof.
  intros.
  generalize dependent l2.
  induction l1.
  - intros. destruct l2.
    + split. reflexivity. inversion H. rewrite H1 in H. reflexivity.
    + apply equal_length_eq in H. injection H as H.
      rewrite app_length in H. simpl in H. rewrite plus_comm in H. discriminate.
  - intros. destruct l2. 
    + apply equal_length_eq in H. injection H as H.
      rewrite app_length in H. simpl in H. rewrite plus_comm in H. discriminate.
    + simpl. inversion H. rewrite H1 in *.
      apply IHl1 in H2. destruct H2 as [H2 H3]. split.
      * rewrite H2. reflexivity.
      * apply H3.
Qed.

Lemma rev_back_eq_front: forall X (l: list X) x,
  rev (l ++ [x]) = x :: rev l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. simpl. reflexivity.
Qed.

(*
   We can use palindrome_induction to prove this theorem, with P := l => l = rev l -> pal l.
   Length 0, and length 1 is easy to prove.
   How about length n + 2? We can use the result of length n to prove that x = y.
*)
Theorem palindrome_converse: forall X (l: list X), l = rev l -> pal l.
Proof.
  intros X l.
  apply palindrome_induction with (P := fun l => l = rev l -> pal l).
  - intros. apply Empty_P.
  - intros. apply One_P.
  - intros. simpl in *.
    replace (x :: l0 ++ [y]) with ((x :: l0) ++ [y]) in *.
    apply app_one in H0.
    destruct H0 as [H1 H2].
    simpl. rewrite H2 in *. apply Add_P.
    apply H. rewrite rev_back_eq_front in H1.
    injection H1 as H1. apply H1.
    simpl. reflexivity.
Qed.

(* Exercise NoDup *)
Inductive NoDup {X: Type}: list X -> Prop :=
  | Empty_ND: NoDup []
  | Add_ND: forall x l, NoDup l -> ~ (In x l) -> NoDup (x :: l).

Definition disjoint {X: Type} (l1 l2: list X) :=
  forall x, In x l1 -> ~ (In x l2).

Example NoDupTest1: NoDup [1;2;3;4].
Proof.
  apply Add_ND. apply Add_ND. apply Add_ND. apply Add_ND. apply Empty_ND.
  - simpl. unfold not. intros. apply H.
  - simpl. unfold not. intros. destruct H as [H | H]. 
    + apply eqb_eq in H. simpl in H. discriminate H.
    + apply H.
  - simpl. unfold not. intros. destruct H as [H | [H | H]].
    + apply eqb_eq in H. discriminate H.
    + apply eqb_eq in H. discriminate H.
    + apply H.
  - simpl. unfold not. intros. destruct H as [H | [H | [H | H]]].
    + apply eqb_eq in H. discriminate H.
    + apply eqb_eq in H. discriminate H.
    + apply eqb_eq in H. discriminate H.
    + apply H.
Qed.

Theorem NoDup_app: forall X (l1 l2: list X),
  NoDup l1 -> NoDup l2 ->
  disjoint l1 l2 ->
  NoDup (l1 ++ l2).
Proof.
  intros X l1 l2.
  intros H1.
  induction H1.
  - intros. simpl. apply H.
  - intros. simpl. apply Add_ND. apply IHNoDup.
    + apply H0.
    + unfold disjoint in *. intros. apply H2. simpl. right. apply H3.
    + unfold not. intros. apply In_app_iff in H3.
      destruct H3 as [H3 | H3].
      * apply H in H3. apply H3.
      * unfold not in H2. apply H2 with (x0 := x).
        { simpl. left. reflexivity. }
        { apply H3. }
Qed.

(* Exercise pigeonhole_principle *)
Lemma in_split: forall (X: Type) (x: X) (l: list X),
  In x l -> exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l.
  induction l.
  - intros. simpl in H. destruct H.
  - intros. simpl in H.
    destruct H as [H | H].
    + exists []. exists l. simpl. rewrite H. reflexivity.
    + apply IHl in H.
      destruct H as [l1 [l2 H]].
      exists (x0 :: l1). exists l2. simpl. rewrite H. reflexivity.
Qed.

Inductive repeats {X: Type}: list X -> Prop :=
  | First_R: forall l x, In x l -> repeats (x :: l)
  | Add_R: forall l x, repeats l -> repeats (x :: l).

Theorem pigeonhole_principle: forall (X: Type) (l1 l2: list X),
  excluded_middle -> (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros X l1.
  induction l1 as [|x l1' IHl1'].
  - intros. simpl in H1. inversion H1.
  - intros. simpl in H1.
    assert(Hex: In x l1' \/ ~ In x l1').
    { apply H. }
    destruct Hex as [Hex | Hex].
    + apply First_R, Hex.
    + apply Add_R.
      assert(I: In x l2). { apply H0. simpl. left. reflexivity. }
      apply in_split in I.
      destruct I as [l1 [l3 I]].
      apply IHl1' with (l2 := l1 ++ l3).
      * apply H.
      * intros.
        rewrite I in H0.
        assert (H': x <> x0). 
        { intros contra. rewrite <- contra in H2. apply Hex in H2. apply H2. }
        assert (H3: In x0 l1' <-> In x0 (x :: l1')).
        { split.
          - intros. simpl. right. apply H3. 
          - intros. destruct H3.
            + apply H' in H3. inversion H3.
            + apply H3. }
        rewrite H3 in H2.
        apply H0 in H2.
        apply In_app_iff in H2.
        apply In_app_iff.
        destruct H2.
        { left. apply H2. }
        { right. simpl in H2.
          destruct H2.
          - apply H' in H2. inversion H2.
          - apply H2.
        }
      * rewrite I in H1. 
        rewrite app_length, plus_comm in H1.
        simpl in H1. unfold lt in *.
        apply le_pred in H1. simpl in H1.
        rewrite app_length, plus_comm.
        apply H1.
Qed.

(* Extended Exercise: A Verified Regular-Expression Matcher *)
Require Export Coq.Strings.Ascii.
Definition string := list ascii.

Lemma provable_equiv_true: forall (P: Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros. apply H.
Qed.

Lemma not_equiv_false: forall (P: Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - intros. apply H in H0. apply H0.
  - intros. exfalso. apply H0.
Qed.

Lemma null_matches_none: forall (s: string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros. inversion H.
Qed.

Lemma empty_matches_eps: forall (s: string), (s =~ EmptyStr) <-> s = [].
Proof.
  intros. split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

Lemma empty_nomatch_ne: forall (a: ascii) (s: string), (a :: s =~ EmptyStr) <-> False.
Proof.
  intros. apply not_equiv_false.
  unfold not. intros.
  inversion H.
Qed.

Lemma char_nomatch_char: forall (a b: ascii) s, b <> a -> (b :: s =~ Char a) <-> False.
Proof.
  intros. apply not_equiv_false.
  unfold not. intros.
  inversion H0. apply H, H4.
Qed.

Lemma char_eps_suffix: forall (a: ascii) s, a :: s =~ Char a <-> s = [].
Proof.
  intros. split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

Lemma app_exists: forall (s: string) re0 re1,
  s =~ App re0 re1 <-> exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    exists s1, s2.
    split.
    + reflexivity.
    + split. apply H3. apply H4.
  - intros. destruct H as [s0 [s1 [H1 [H2 H3]]]].
    rewrite H1. apply MApp. apply H2. apply H3.
Qed.

(* Exercise app_ne *)
Lemma app_nil_l: forall X (l: list X), [] ++ l = l.
Proof. reflexivity. Qed.

Lemma app_ne: forall (a: ascii) s re0 re1,
  a :: s =~ (App re0 re1) <->
  ([] =~ re0 /\ a :: s =~ re1) \/
  (exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1).
Proof.
  intros. split.
  - intros. inversion H.
    destruct s1.
    + left. split. apply H3. apply H4.
    + right. exists s1, s2. simpl in H1. injection H1. intros.
      split. symmetry. apply H5.
      split. rewrite <- H6. apply H3.
      apply H4.
  - intros. destruct H as [H | H].
    + destruct H as [H1 H2].
      rewrite <- app_nil_l with (l := (a :: s)).
      apply MApp. apply H1. apply H2.
    + destruct H as [s0 [s1 [H1 [H2 H3]]]].
      replace (a :: s) with ((a :: s0) ++ s1).
      apply MApp. apply H2. apply H3.
      simpl. rewrite H1. reflexivity.
Qed.

Lemma union_disj: forall (s: string) re0 re1,
  s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros. destruct H as [H1 | H2].
    + apply MUnionL, H1.
    + apply MUnionR, H2.
Qed.

(* Exercise star_ne *)
Lemma star_ne: forall (a: ascii) s re, a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  intros. split.
  - intros.
    remember (Star re) as re'.
    remember (a :: s) as s'.
    induction H.
    + intros. inversion Heqs'.
    + intros. inversion Heqre'.
    + intros. inversion Heqre'.
    + intros. inversion Heqre'.
    + intros. inversion Heqre'.
    + intros. inversion Heqs'.
    + intros.
      destruct s1.
      * simpl in Heqs'.
        apply IHexp_match2 in Heqre'. apply Heqre'. apply Heqs'.
      * simpl in Heqs'.
        injection Heqs' as H1 H2.
        exists s1, s2. split.
        { rewrite H2. reflexivity. }
        { split. rewrite <- H1. injection Heqre' as Hre. rewrite <- Hre. apply H.
                 apply H0.
        }
  - intros. destruct H as [s0 [s1 [H1 [H2 H3]]]].
    rewrite H1. 
    replace (a :: s0 ++ s1) with ((a :: s0) ++ s1).
    apply MStarApp.
    + apply H2.
    + apply H3.
    + reflexivity.
Qed.

Definition refl_matches_eps m :=
  forall re : @reg_exp ascii, reflect ([ ] =~ re) (m re).

(* Exercise match_eps *)
Print reg_exp. 
Fixpoint match_eps (re: @reg_exp ascii) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char t => false
  | App re0 re1 => (match_eps re0) && (match_eps re1)
  | Union re0 re1 => (match_eps re0) || (match_eps re1)
  | Star re => true
  end.

Lemma app_nil_both_nil: forall X (l1 l2: list X),
  l1 ++ l2 = [] <-> l1 = [] /\ l2 = [].
Proof.
  split.
  - intros. induction l1.
    + simpl in H. split. reflexivity. apply H.
    + simpl in H. discriminate H.
  - intros. destruct H as [H1 H2].
    rewrite H1, H2. reflexivity.
Qed.

Lemma match_eps_refl: refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps.
  intros.
  apply iff_reflect.
  split.
  - intros. 
    induction re.
    + inversion H.
    + reflexivity.
    + inversion H.
    + inversion H.
      destruct s1 eqn: Hs1.
      * simpl in *. rewrite H1 in H4.
        apply andb_true_iff.
        split. apply IHre1, H3. apply IHre2, H4.
      * simpl in *.
        discriminate.
    + inversion H. 
      * simpl in *.
        apply orb_true_iff. left. apply IHre1, H2.
      * simpl in *.
        apply orb_true_iff. right. apply IHre2, H1.
    + reflexivity.
  - intros. induction re.
    + discriminate H.
    + apply MEmpty.
    + discriminate H.
    + simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
      apply IHre1 in H1; apply IHre2 in H2.
      assert(H: [] ++ [] =~ App re1 re2).
      { apply MApp. apply H1. apply H2. }
      simpl in H. apply H.
    + simpl in H. apply orb_true_iff in H. destruct H as [H1 | H2].
      * apply IHre1 in H1. apply MUnionL. apply H1.
      * apply IHre2 in H2. apply MUnionR. apply H2.
    + apply MStar0.
Qed.

Definition is_der re (a: ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

Definition derives d := forall a re, is_der re a (d a re).

(* Exercise derive *)
Fixpoint derive (a: ascii) (re: @reg_exp ascii): @reg_exp ascii :=
  match re with
  | EmptySet => EmptySet
  | EmptyStr => EmptyStr
  | Char t => 
      if (nat_of_ascii a) =? (nat_of_ascii t) then EmptyStr 
      else re
  | App re1 re2 => 
      if (match_eps re1) then Union (derive a re2) (App (derive a re1) re2)
      else App (derive a re1) re2
  | Union re1 re2 => Union (derive a re1) (derive a re2)
  | Star re => Star (derive a re)
  end.
(* Not sure about it *)

Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof. reflexivity. Qed.

Example test_der1 : match_eps (derive c (Char c)) = true.
Proof. reflexivity. Qed.

Example test_der2 : match_eps (derive c (Char d)) = false.
Proof. reflexivity. Qed.

Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof. reflexivity. Qed.

Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof. reflexivity. Qed.

Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof. reflexivity. Qed.

Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof. reflexivity. Qed.

Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof. reflexivity. Qed.

(* Exercise derive_corr *)
Lemma derive_corr : derives derive.
Proof.
  unfold derives.
  unfold is_der.
  split.
  - generalize dependent a.
    generalize dependent s.
    induction re.
    + intros. inversion H.
    + intros. subst. inversion H.
    + intros. subst. inversion H.
      simpl. rewrite <- Induction.eqb_refl. apply MEmpty.
    + intros. simpl.
      apply app_ne in H.
      destruct H as [[H1 H2] | [s0 [s1 [H1 [H2 H3]]]]].
      * destruct (match_eps re1) eqn: Hmatch.
        { apply MUnionL. apply IHre2. apply H2. }
        { admit. }
      * destruct (match_eps re1) eqn: Hmatch.
        { admit. }
        { admit. }
    + intros. simpl. inversion H; subst.
      * apply MUnionL. apply IHre1. apply H2.
      * apply MUnionR. apply IHre2. apply H1.
    + intros. simpl.
      apply star_ne in H.
      destruct H as [s1 [s2 [H1 [H2 H3]]]].
      admit.
  - intros.
    generalize dependent s.
    generalize dependent a.
    induction re.
    + intros. inversion H.
    + intros. 

Admitted.

Definition matches_regex m: Prop :=
  forall (s: string) re, reflect (s =~ re) (m s re).

(* Exercise regex_match *)
Fixpoint regex_match (s: string) (reg: @reg_exp ascii) : bool.
Admitted.

(* Exercise regex_refl *)
Theorem regex_refl: matches_regex regex_match.
Proof.
Admitted.

