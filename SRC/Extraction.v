(* Chap 15 Extraction *)
(* Chap 15.1 Basic Extraction *)
Require Coq.extraction.Extraction.
Extraction Language OCaml.

From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From SRC Require Import ImpCEvalFun.

Extraction "test1.ml" ceval_step.

(* Chap 15.2 Controlling Extraction of Specific Types *)
Extract Inductive bool => "bool" [ "true" "false" ].

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n →
      if n=0 then zero () else succ (n-1))".

Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant eqb => "( = )".

Extract Constant minus => "( - )".

Extraction "test2.ml" ceval_step.

(* Chap 15.3 A Complete Example *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Extract Inductive sumbool => "bool" ["true" "false"].

From SRC Require Import Imp.
From SRC Require Import ImpParser.
From SRC Require Import Maps.
Extraction "test.ml" empty_st ceval_step parse.

(* Chap 15.4 Discussion *)
(* Skipped *)

(* Chap 15.5 Going Further *)
(* End *)
