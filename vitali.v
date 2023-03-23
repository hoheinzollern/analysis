(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.classical Require Import cardinality fsbigop mathcomp_extra.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure lebesgue_integral numfun.


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

Lemma vitali (C : I -> R * {posnum R}) :
  exists (i : nat -> I), forall (c : I), exists (d : nat),
    Ball (C c) `&` Ball (C (i d)) !=set0 /\
      ((C c).2%:num) * 2^-1 <= ((C (i d)).2%:num).
Proof.
Admitted.

Definition is_vitali_covering (E : set R) (V : I -> R * {posnum R}) :=
  forall (x : R) (e : {posnum R}), x \in E ->
    exists i, x \in Ball (V i) /\ (V i).2%:num < e%:num.

Definition bounded (E : set R) :=
  exists (C : R * {posnum R}), E `<=` Ball C.

Theorem vitali_covering_theorem (E : set R) (V : I -> R * {posnum R}) :
  is_vitali_covering E V -> bounded E -> exists (i : nat -> I),
    trivIset setT (fun j => V (i j)) 