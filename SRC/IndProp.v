(* Chap 7 IndProp *)
Set Warnings "-notation-overridden,-parsing".
From SRC Require Export Logic.
Require Coq.omega.Omega.

(* Chap 7.1 Inductively Defined Propositions *)
Inductive even: nat -> Prop :=
  | ev_0: even 0
  | ev_SS (n: nat) (H: even n) : even (S (S n)).
