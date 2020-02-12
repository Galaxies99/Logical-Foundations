(* Chap 4 Poly *)
(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing".
From LF Require Export Lists.

(* Chap 4.1 Polymorphism *)
(* Chap 4.1.1 Polymorphic Lists *)
Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b: bool) (l: boollist).

Inductive list (X: Type) : Type :=
  | nil
  | cons (x: X) (l: list X).

Check list.
Check (nil nat).
Check (cons nat 3 (nil nat)).
Check nil.
Check cons.
Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint repeat (X: Type) (x: X) (count: nat) : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.
Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

(* Exercise mumble_grumble *)
Module MumbleGrumble.
Inductive mumble : Type :=
  | a
  | b (x: mumble) (y: nat)
  | c.

Inductive grumble (X: Type) : Type :=
  | d (m: mumble)
  | e (x: X).

Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
Check c.

End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'.
Check repeat.

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).
(* Note: use holes to tell Coq to infer the missing info. *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.
(* Note: Important!!! Implicit Argument, "Yin Shi Can Shu" in CHN.
         use nil {X}, Coq can infer an X behind nil. *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X: Type} (x: X) (count: nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.
(* Note: arguments in {} is Implicit Argument. *)

Inductive list' {X: Type} : Type := 
  | nil'
  | cons' (x: X) (l: list').

Fixpoint app {X: Type} (l1 l2: list X) : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X: Type} (l: list X) : (list X) :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X: Type} (l: list X) : nat :=
  match l with
  | nil => O
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.
Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.
Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Fail Definition mynil := nil.
(* Note: Fail means that the sentence behind is sure to compile error.
   It will print out the infomation and continue. *)

Definition mynil : list nat := nil.
(* Note: Explicit give an argument (list nat). *)

Check @nil.
Definition mynil' := @nil nat.
(* Note: have prefix @ to make the argument explicit. *)

Notation "x :: y" := (cons x y)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
  (at level 60, right associativity).

(* Exercise poly_exercises *)
Theorem app_nil_r: forall (X: Type), forall (l: list X),
  l ++ [] = l.
Proof.
  intros X l.
  induction l.
  - reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem app_assoc: forall A (l m n: list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l.
  - reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem app_length: forall X (l1 l2: list X),
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros X l1 l2.
  induction l1.
  - reflexivity.
  - simpl. rewrite -> IHl1. reflexivity.
Qed.

(* Exercise more_poly_exercises *)
Theorem rev_app_distr: forall X (l1 l2: list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1.
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1. rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive: forall X (l: list X),
  rev (rev l) = l.
Proof.
  intros X l.
  induction l.
  - reflexivity.
  - simpl. 
    rewrite -> rev_app_distr. 
    simpl. 
    rewrite -> IHl.
    reflexivity.
Qed.

(* Chap 4.1.2 Polymorphic Pairs *)
Inductive prod (X Y: Type) : Type :=
  | pair (x: X) (y: Y).

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
(* Note: type_scope means that it is a type. *)

Definition fst {X Y: Type} (p: X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y: Type} (p: X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y: Type} (lx: list X) (ly: list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.
(* Note: also called zip. *)

(* Exercise combine_checks *)
(* My answer: [(1, false); (2, false)] : list(nat * bool) *)
Compute (combine [1;2] [false;false;true;true]).

(* Exercise split *)
Fixpoint split {X Y: Type} (l: list(X * Y)) : (list X) * (list Y) :=
  match l with
  | [] => pair [] []
  | (x, y) :: t => pair (x :: (fst (split t))) (y :: (snd (split t)))
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

(* Chap 4.1.3 Polymorphic Options *)
Module OptionPlayground.

Inductive option (X: Type) : Type :=
  | Some (x: X)
  | None.

Arguments Some {X} _.
Arguments None {X}.

End OptionPlayground.

Fixpoint nth_error {X: Type} (l: list X) (n: nat) : option X :=
  match l with
  | [] => None
  | a :: l' => if n =? O then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(* Exercise hd_error_poly *)
Definition hd_error {X: Type} (l: list X) : option X :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Check @hd_error.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

(* Chap 4.2 Functions as Data *)
(* Chap 4.2.1 Higher-Order Functions *)
Definition doit3times {X: Type} (f: X -> X) (n: X) : X := f (f (f n)).

Check @doit3times.
Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.
Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

(* Chap 4.2.2 Filter *)
Fixpoint filter {X: Type} (test: X -> bool) (l: list X) : (list X) :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X: Type} (l: list X) : bool :=
  (length l) =? 1.
Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l: list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

(* Chap 4.2.3 Anonymous Functions *)
Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
  filter (fun l => (length l) =? 1) [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

(* Exercise filter_even_gt7 *)
Definition filter_even_gt7 (l: list nat) : list nat :=
  filter (fun n => (evenb n) && (negb (n <=? 7))) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

(* Exercise partition *)
Definition partition {X: Type} (test: X -> bool) (l: list X) : list X * list X :=
  pair (filter test l) (filter (fun x => negb (test x)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

(* Chap 4.2.4 Map *)
Fixpoint map {X Y: Type} (f: X -> Y) (l: list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

(* Exercise map_rev *)

Theorem map_add: forall X Y (f: X -> Y) (l: list X) (x: X),
  map f (l ++ [x]) = map f l ++ [f x].
Proof.
  intros X Y f l x.
  induction l.
  - reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem map_rev: forall X Y (f: X -> Y) (l: list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l.
  - reflexivity.
  - simpl. rewrite -> map_add. rewrite -> IHl. reflexivity.
Qed.

(* Exercise flat_map *)
Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X) : (list Y) :=
  match l with
  | nil => nil
  | h :: t => app (f h) (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.


Definition option_map {X Y: Type} (f: X -> Y) (xo: option X) : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

(* Exercise implicit_args *)
Fixpoint filter' (X: Type) (test: X -> bool) (l: list X) : (list X) :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter' X test t)
    else filter test t
  end.

Fixpoint map' (X Y: Type) (f: X -> Y) (l: list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map' X Y f t)
  end.

(* Chap 4.2.5 Fold *)
Fixpoint fold {X Y: Type} (f: X -> Y -> Y) (l: list X) (b: Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.
(* Note: like a repeat, when it ends, return b, and every times f(h, res) -> res. *)

Check fold andb.

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(* Chap 4.2.6 Functions That Construct Functions *)
Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k: nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Check plus.

(* Chap 4.3 Additional Exercises *)
Module Exercises.

(* Exercise fold_length *)
Definition fold_length {X: Type} (l: list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l.
  induction l.
  - reflexivity.
  - simpl. rewrite <- IHl. reflexivity.
Qed.

(* Exercise fold_map *)
Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun n l' => (f n) :: l') l [].

Theorem fold_map_correct : forall X Y (f: X -> Y) (l: list X), map f l = fold_map f l.
Proof.
  intros X Y f l.
  induction l.
  - reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.

(* Exercise currying *)
Definition prod_curry {X Y Z: Type} (f: X * Y -> Z) (x: X) (y: Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z: Type} (f: X -> Y -> Z) (p: X * Y) : Z := f (fst p) (snd p).

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry: forall (X Y Z: Type) (f: X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  reflexivity.
Qed.
(* Note: here simpl. do nothing, but reflexivity can do everything! *)

Theorem curry_uncurry: forall (X Y Z: Type) (f: (X * Y) -> Z) p,
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f [].
  - reflexivity.
Qed.

(* Exercise nth_error_informal *)
(* Skipped *)

Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition zero : cnat := fun (X: Type) (f: X -> X) (x: X) => x.
Definition one : cnat := fun (X: Type) (f: X -> X) (x: X) => f x.
Definition two : cnat := fun (X: Type) (f: X -> X) (x: X) => f (f x).
Definition three' : cnat := fun (X: Type) (f: X -> X) (x: X) => f (f (f x)).
Definition three : cnat := @doit3times.

(* Exercise church_succ *)
Definition succ (n: cnat) : cnat :=
  fun (X: Type) (f: X -> X) (x: X) => f (n X f x).

Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.
Example succ_2 : succ one = two.
Proof. reflexivity. Qed.
Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

(* Exercise church_plus *)
Definition plus (n m: cnat) : cnat :=
  fun (X: Type) (f: X -> X) (x: X) => n X f (m X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

(* Exercise church_mult *)
Definition mult (n m: cnat) : cnat :=
  fun (X: Type) (f: X -> X)  => n X (m X f).

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.
(* Note: n times, each times f(f(f(...()))) (m times) *)

(* Exercise church_exp *)
Definition exp (n m: cnat) : cnat :=
  fun (X: Type) => m (X -> X) (n X).
(* Note: m times, because of Type is (X -> X), so each time, each f turns out n new f, which means n^m *)

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.
Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

End Church.
End Exercises.