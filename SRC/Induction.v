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

(* ################################################################# *)
(* More Exercises *)

(** **** Exercise: 3 stars, standard, recommended (mult_comm)

    Use [assert] to help prove this theorem.  You shouldn't need to
    use induction on [plus_swap].
    After that, prove commutativity of multiplication.  (You will probably
    need to define and prove a separate subsidiary theorem to be used
    in the proof of this one.  You may find that [plus_swap] comes in
    handy.) 
*)
Theorem plus_swap: forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  assert (n + m = m + n).
  {
    rewrite -> plus_comm.
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.

Theorem mult_succ: forall m n: nat,
  m + m * n = m * S n.
Proof.
  intros m n.
  induction m.
  - reflexivity.
  - simpl. rewrite <- IHm. rewrite -> plus_swap. reflexivity.
Qed.

Theorem mult_comm: forall m n: nat,
  m * n = n * m.
Proof.
  intros n m.
  induction n.
  - rewrite mult_0_r. reflexivity.
  - simpl. rewrite <- mult_succ. rewrite -> IHn. reflexivity.
Qed.

(** **** Exercise: 3 stars, standard, optional (more_exercises)  

    Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before you hack!) *)
Check leb.

Theorem leb_refl: forall n: nat,
  true = (n <=? n).
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem zero_nbeq_S: forall n: nat,
  0 =? (S n) = false.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem andb_false_r: forall b: bool,
  andb b false = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_ble_compat_l: forall n m p: nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p.
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHp. reflexivity.
Qed.

Theorem S_nbeq_0: forall n: nat,
  (S n) =? 0 = false.
Proof.
  intros n. 
  reflexivity.
Qed.

Theorem mult_1_l: forall n: nat, 1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite <- plus_n_O.
  reflexivity.
Qed.

Theorem all3_spec: forall b c: bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem mult_plus_distr_r: forall n m p: nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. rewrite -> plus_assoc. reflexivity.
Qed.

Theorem mult_assoc: forall n m p: nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. rewrite -> mult_plus_distr_r. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard, optional (eqb_refl)  

    Prove the following theorem.  (Putting the [true] on the left-hand
    side of the equality may look odd, but this is how the theorem is
    stated in the Coq standard library, so we follow suit.  Rewriting
    works equally well in either direction, so we will have no problem
    using the theorem no matter which way we state it.) *)
Theorem eqb_refl: forall n: nat,
  true = (n =? n).
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard, optional (plus_swap')  

    The [replace] tactic allows you to specify a particular subterm to
   rewrite and what you want it rewritten to: [replace (t) with (u)]
   replaces (all copies of) expression [t] in the goal by expression
   [u], and generates [t = u] as an additional subgoal. This is often
   useful when a plain [rewrite] acts on the wrong part of the goal.

   Use the [replace] tactic to do a proof of [plus_swap'], just like
   [plus_swap] but without needing [assert (n + m = m + n)]. *)
Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  replace (n + m) with (m + n).
  - reflexivity.
  - rewrite plus_comm. reflexivity.
Qed.
(* Note: just a test, not official prove, so may be a little dump. *)

(** **** Exercise: 3 stars, standard, recommended (binary_commute)  

    Recall the [incr] and [bin_to_nat] functions that you
    wrote for the [binary] exercise in the [Basics] chapter.  Prove
    that the following diagram commutes:

                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

    That is, incrementing a binary number and then converting it to
    a (unary) natural number yields the same result as first converting
    it to a natural number and then incrementing.
    Name your theorem [bin_to_nat_pres_incr] ("pres" for "preserves").

    Before you start working on this exercise, copy the definitions
    from your solution to the [binary] exercise here so that this file
    can be graded on its own.  If you want to change your original
    definitions to make the property easier to prove, feel free to
    do so! *)
Theorem bin_to_nat_pres_incr: forall n: bin,
  bin_to_nat (incr n) = S (bin_to_nat n).
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_O. rewrite <- plus_n_O. 
    rewrite -> plus_n_Sm.
    rewrite -> plus_n_Sm.
    rewrite -> IHn.
    assert (H: forall t: nat, S t + S t = t + S (S t)).
    {
      intros t.
      destruct t.
      - reflexivity.
      - simpl. rewrite -> plus_n_Sm. reflexivity.
    }
    rewrite -> H.
    reflexivity.
Qed.

(** **** Exercise: 5 stars, advanced (binary_inverse)  

    This is a further continuation of the previous exercises about
    binary numbers.  You may find you need to go back and change your
    earlier definitions to get things to work here.

    (a) First, write a function to convert natural numbers to binary
        numbers. Prove that, if we start with any [nat], convert it to 
        binary, and convert it back, we get the same [nat] we started 
        with.  (Hint: If your definition of [nat_to_bin] involved any 
        extra functions, you may need to prove a subsidiary lemma showing
        how such functions relate to [nat_to_bin].)
    (b) One might naturally expect that we should also prove the
        opposite direction -- that starting with a binary number,
        converting to a natural, and then back to binary should yield
        the same number we started with.  However, this is not the
        case!  Explain (in a comment) what the problem is.
    (c) Define a normalization function -- i.e., a function
        [normalize] going directly from [bin] to [bin] (i.e., _not_ by
        converting to [nat] and back) such that, for any binary number
        [b], converting [b] to a natural and then back to binary yields
        [(normalize b)].  Prove it.  (Warning: This part is a bit
        tricky -- you may end up defining several auxiliary lemmas.
        One good way to find out what you need is to start by trying
        to prove the main statement, see where you get stuck, and see
        if you can find a lemma -- perhaps requiring its own inductive
        proof -- that will allow the main proof to make progress.) Don't
        define thi using nat_to_bin and bin_to_nat! 
*)

Fixpoint nat_to_bin (n: nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat: forall n: nat, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite -> bin_to_nat_pres_incr.
    rewrite -> IHn. reflexivity.
Qed.

Fixpoint normalize (b: bin) : bin :=
  match b with
  | Z => Z
  | A b' =>
    match normalize b' with
    | Z => Z
    | b'' => A b''
    end
  | B b' => B (normalize b')
  end.

Compute normalize (A (B (A (A Z)))).

Lemma normalize_incr_comm: forall b: bin, normalize (incr b) = incr (normalize b).
Proof.
  intros b.
  induction b.
  - reflexivity.
  - simpl. 
    destruct (normalize b).
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl.
    rewrite -> IHb.
    destruct (normalize b).
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Lemma twice_is_A: forall n: nat, nat_to_bin(n + n) = normalize (A (nat_to_bin n)).
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - replace (nat_to_bin (S n + S n)) with (incr (incr (nat_to_bin (n + n)))).
    rewrite IHn. 
    rewrite <- normalize_incr_comm. 
    rewrite <- normalize_incr_comm.
    reflexivity.
    simpl.
    rewrite <- plus_n_Sm. 
    simpl. 
    reflexivity.
Qed.

Lemma normalize_twice_eq_normalize: forall b: bin, normalize (normalize b) = normalize b.
Proof.
  intros b.
  induction b.
  - reflexivity.
  - simpl.
    destruct (normalize b).
    + reflexivity.
    + replace (normalize (A (A b0))) with (
        match normalize (A b0) with 
        | Z => Z
        | A c => A (A c)
        | B c => A (B c)
        end
      ).
      rewrite -> IHb.
      reflexivity.
      simpl. reflexivity.
    + simpl. rewrite <- IHb. simpl. reflexivity.
  - simpl. rewrite IHb. reflexivity.
Qed.


Theorem normalize_eq_bin_nat_bin: forall b: bin, normalize b = nat_to_bin (bin_to_nat b).
Proof.
  intros b.
  induction b.
  - reflexivity.
  - simpl. 
    rewrite <- plus_n_O.
    rewrite -> twice_is_A.
    simpl. rewrite <- IHb.
    rewrite -> normalize_twice_eq_normalize.
    reflexivity.
  - simpl. rewrite -> IHb.
    rewrite <- plus_n_O.
    rewrite -> twice_is_A.
    rewrite <- IHb.
    simpl.
    rewrite -> normalize_twice_eq_normalize.
    destruct (normalize b).
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.


