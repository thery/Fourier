(* Examples *)
From Stdlib Require Import ZArith Reals List.
Require Import QFourier.

From mathcomp Require Import all_ssreflect all_algebra.

Import GRing.Theory Num.Theory.
Open Scope ring_scope.


(* Examples *)
Lemma ex1: forall x1 x2 x3: rat,
  x1 <= x2 -> x1 <= x3 -> x2 + 1%:R * x3 <= x1 -> x3 < 1.
Proof. qfourier. Qed.

Lemma ex2: forall x1 x2 x3: rat,
  3%:R / 4%:R * x1 + 10%:R <= 3%:R / 4%:R * x2 + 10%:R -> 1/2%:R * x2  = 1/2%:R * x3 -> x1 <= x3.
Proof. qfourier. Qed.
