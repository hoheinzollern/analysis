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

Section AC_BV.
Variable R : realType.

Definition AC (f : R -> R) (a b : R) := forall e : {posnum R},
  exists d : {posnum R}, forall n (ab : 'I_n -> R * R),
    (forall i, `[(ab i).1, (ab i).2]%classic `<=` `[a, b]%classic) /\
    trivIset setT (fun i => `[(ab i).1, (ab i).2]%classic) /\
    \sum_(k < n) maxr 0 ((ab k).2  - (ab k).1) < d%:num ->
    \sum_(k < n) maxr 0 (f (ab k).2  - f (ab k).1) < e%:num.

Definition BV (f : R -> R) (a b : R) :=
  exists g h : R -> R,
    {in `[a, b], {homo g : x y / x <= y}} /\
    {in `[a, b], {homo h : x y / x <= y}} /\
    {in `[a, b], f =1 g \- h}.

End AC_BV.

Section vitali.
Variables (R : realType) (I : eqType).
Let mu := @lebesgue_measure R.

Definition Ball (C : R * {posnum R}) := ball_ normr C.1 C.2%:num.

Definition Ball5 (C : R * {posnum R}) := Ball (C.1, (C.2%:num *+ 5)%:pos).

Definition bounded (E : set R) := (mu E < +oo)%E.

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

Local Open Scope measure_scope.
Theorem vitali_covering_theorem (E : set R) (V : I -> R * {posnum R}) :
  is_vitali_covering E V -> bounded E -> exists iot : nat -> I,
    let D := Ball \o V \o iot in
    trivIset setT D /\
    mu^* (E `\` \bigcup_k (D k)) = 0%E /\
    (forall e : {posnum R}, exists N,
      mu^* (E `\` \big[setU/set0]_(k < N) (D k)) < e%:num%:E)%E.
Proof.
Admitted.

Corollary vitali_covering_theorem2 (E : set R) (V : I -> R * {posnum R}) :
  is_vitali_covering E V -> bounded E -> forall e : {posnum R},
    exists n (iot : 'I_n -> I),
    let D := Ball \o V \o iot in
      (mu (\big[setU/set0]_(i < n) (D i)) < mu^* E + e%:num%:E /\
       mu^* (E `&` \big[setU/set0]_(i < n) (D i)) > mu^* E + e%:num%:E)%E.
Proof.
Admitted.

Local Close Scope measure_scope.

End vitali.

Section lebesgue_differentiation.
Variables (R : realType) (a b : R) (f : R^o -> R^o).
Let mu := @lebesgue_measure R.
Hypothesis f_nd : {in `[a, b], {homo f : x y / x <= y}}.

Theorem Lebesgue_differentiation :
  {ae mu, forall x, x \in `[a, b] -> derivable f x 1 /\ 0 <= f^`() x } /\
  \int[mu]_(x in `[a, b]) f^`() x <= f b - f a.
Proof.
Admitted.

End lebesgue_differentiation.

Section Lebesgue_differentiation_corollary.
Variables (R : realType) (a b : R) (f : R^o -> R^o).
Let mu := @lebesgue_measure R.

Corollary Lebesgue_differentiation_corollary :
  BV f a b ->
  {ae mu, forall x, x \in `[a, b] -> derivable f x 1} /\
  mu.-integrable `[a, b] (EFin \o f^`()).
Proof.
Admitted.

End Lebesgue_differentiation_corollary.
