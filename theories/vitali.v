(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.classical Require Import cardinality fsbigop mathcomp_extra.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure lebesgue_integral numfun derive.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section vitali.
Variables (R : realType) (I : eqType).

Definition Ball (C : R * {posnum R}) := ball_ normr C.1 C.2%:num.

Definition Ball5 (C : R * {posnum R}) := Ball (C.1, (C.2%:num *+ 5)%:pos).

Definition bounded (E : set R) := exists (C : R * {posnum R}), E `<=` Ball C.

Lemma vitali (C : I -> R * {posnum R}) :
  exists iot : nat -> I, let D := C \o iot in
  (forall i, exists2 j,
    Ball (C i) `&` Ball (D j) !=set0 &
    (D j).2%:num >= (C i).2%:num * 2^-1) /\
  \bigcup_i (Ball (C i)) `<=` \bigcup_j (Ball5 (D j)).
Proof.
Admitted.

Definition is_vitali_covering (E : set R) (V : I -> R * {posnum R}) :=
  forall x (e : {posnum R}), x \in E ->
    exists2 i, x \in Ball (V i) & (V i).2%:num < e%:num.

Variable mu : {measure set R -> \bar R}.

Local Open Scope measure_scope.
Theorem vitali_covering_theorem (E : set R) (V : I -> R * {posnum R}) :
  is_vitali_covering E V -> bounded E -> exists iot : nat -> I,
    trivIset setT (fun j => Ball (V (iot j))) /\
    mu^* (E `\` \bigcup_k (Ball (V (iot k)))) = 0%E /\
    (forall e : {posnum R}, exists N,
      (mu^* (E `\` \big[setU/set0]_(k < N) (Ball (V (iot k)))) < e%:num%:E)%E).
Proof.
Admitted.

Corollary vitali_covering_theorem2 (E : set R) (V : I -> R * {posnum R}) :
  is_vitali_covering E V -> bounded E -> forall e : {posnum R},
    exists (n : nat) (iot : 'I_n -> I),
      (mu (\big[setU/set0]_(i < n) (Ball (V (iot i)))) < mu^* E + e%:num%:E /\
       mu^* (E `&` \big[setU/set0]_(i < n) (Ball (V (iot i)))) > mu^* E + e%:num%:E)%E.
Proof.
Admitted.

Local Close Scope measure_scope.

End vitali.

Section lebesgue_differentiation.
Variables (R : realType) (mu : {measure set R -> \bar R}) (a b : R) (f : R^o -> R^o).
Hypothesis f_nd : {in `[a, b], {homo f : x y / x <= y}}.

Theorem Lebesgue_differentiation :
  {ae mu, forall x, x \in `[a, b] -> derivable f x 1} /\
  {ae mu, forall x, x \in `[a, b] -> 0 <= derive f x 1} /\
  \int[mu]_(x in `[a, b]) derive f x 1 <= f b - f a.
Proof.
Admitted.

Definition AC (f : R -> R) (a b : R) := forall e : {posnum R},
  exists d : {posnum R}, forall n (ab : 'I_n -> R * R),
    (forall i, `[(ab i).1, (ab i).2]%classic `<=` `[a, b]%classic) /\
    trivIset setT (fun i => `[(ab i).1, (ab i).2]%classic) /\
    \sum_(k < n) ((ab k).2  - (ab k).1) < d%:num ->
    \sum_(k < n) (f (ab k).2  - f (ab k).1) < e%:num.

End lebesgue_differentiation.
