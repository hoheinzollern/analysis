(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp.classical Require Import boolp classical_sets functions.
From mathcomp.classical Require Import cardinality fsbigop mathcomp_extra.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure lebesgue_integral numfun derive exp trigo.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Inspired by https://math-wiki.com/images/2/2f/88341leb_fund_thm.pdf *)

Section AC_BV.
Variable R : realType.

Definition C1 (a b : R) (f : R^o -> R^o) :=
  (forall x, x \in `[a, b] -> differentiable f x) /\
  {within `[a, b], continuous f^`()}.

Definition AC (a b : R) (f : R -> R) := forall e : {posnum R},
  exists d : {posnum R}, forall n (ab : 'I_n -> R * R),
    (forall i, `[(ab i).1, (ab i).2]%classic `<=` `[a, b]%classic) /\
    trivIset setT (fun i => `[(ab i).1, (ab i).2]%classic) /\
    \sum_(k < n) maxr 0 ((ab k).2  - (ab k).1) < d%:num ->
    \sum_(k < n) maxr 0 (f (ab k).2  - f (ab k).1) < e%:num.

Lemma C1_is_AC (a b : R) (f : R -> R) :
  C1 a b f -> AC a b f.
Proof.
Admitted.

Definition BV (a b : R) (f : R -> R) :=
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
  BV a b f ->
  {ae mu, forall x, x \in `[a, b] -> derivable f x 1} /\
  mu.-integrable `[a, b] (EFin \o f^`()).
Proof.
Admitted.

End Lebesgue_differentiation_corollary.

Section Integral_absolutely_continuous.
Variables (R : realType).
Let mu := @lebesgue_measure R.

Definition L1 (a b : R) := [set f : R -> R | mu.-integrable `[a, b] (EFin \o f)].

Lemma integral_AC (f : R -> R) (a b : R) :
  f \in L1 a b ->
  forall e : {posnum R}, exists d : {posnum R},
    forall E, E `<=` `[a, b] -> measurable E -> (mu E < d%:num%:E)%E ->
      (\int[mu]_(x in E) `| (f x)%:E | < e%:num%:E)%E.
Proof.
Admitted.

Theorem L1_integral_AC (f : R -> R) (a b : R) :
  f \in L1 a b -> AC a b (fun x => \int[mu]_(z in `[a, x]) f z).
Proof.
Admitted.

Lemma L1_integral_0 (f : R -> R) (a b : R) :
  f \in L1 a b -> (forall c, c \in `[a, b] -> \int[mu]_(x in `[a, c]) f x = 0) -> 
    {ae mu, forall x, x \in `[a, b] -> f x = 0}.
Proof.
Admitted.

Corollary L1_integral_eq (f g : R -> R) (a b : R) :
  f \in L1 a b -> g \in L1 a b ->
    (forall c, c \in `[a, b] -> \int[mu]_(x in `[a, c]) f x = \int[mu]_(x in `[a, c]) g x) ->
      {ae mu, forall x, x \in `[a, b] -> f x = g x}.
Proof.
Admitted.

Theorem L1_integral_derive (f : R -> R) (a b : R) :
  {ae mu, forall x, x \in `[a, b] ->
    let F (x : R^o) : R^o := \int[mu]_(z in `[a, x]) f z in
    F^`() = f}.
Proof.
Admitted.

Corollary AC_integral_derive (f : R^o -> R^o) (a b : R) :
  AC a b f -> \int[mu]_(x in `[a, b]) f^`() x = f b - f a.
Proof.
Admitted.

Theorem Lebesgue_density (E : set R) :
  (0 < mu E)%E -> {ae mu, forall x, x \in E ->
    (fun e => fine (mu (E `&` `[x-e, x+e])) / (fine (mu `[x-e, x+e]))) @ (0:R)^' --> (1:R)}.
Proof.
Admitted.

End Integral_absolutely_continuous.

Section examples.
Variables (R : realType).
Let mu := @lebesgue_measure R.

Lemma derive1_expR : (@expR R:R^o -> R^o)^`() = (@expR R).
Proof. by apply/funext => x; rewrite derive1E derive_val. Qed.

Lemma integral_exp (x : R) : \int[mu]_(z in `[0, x]) expR z = expR x - 1.
Proof.
rewrite -expR0 -AC_integral_derive; last first.
  apply C1_is_AC.
  split.
    move => z z0x.
    apply/derivable1_diffP.
    apply: derivable_expR.
  apply: continuous_subspaceT.
  rewrite derive1_expR.
  apply continuous_expR.
congr Rintegral.
by rewrite derive1_expR.
Qed.

Lemma derive1_sin : (@sin R : R^o -> R^o)^`() = (@cos R).
Proof. by apply/funext => x; rewrite derive1E derive_val. Qed.

Lemma integral_cos (x : R) : \int[mu]_(z in `[0, x]) cos z = sin x.
Proof.
rewrite -[RHS]subr0 -[in RHS]sin0 -AC_integral_derive; last first.
  apply C1_is_AC.
  split.
    move => z z0x.
    apply/derivable1_diffP.
    apply: derivable_sin.
  apply: continuous_subspaceT.
  rewrite derive1_sin.
  apply continuous_cos.
congr Rintegral.
by rewrite derive1_sin.
Qed.

Lemma derive1_cos : (@cos R : R^o -> R^o)^`() = -(@sin R).
Proof. by apply/funext => x; rewrite derive1E derive_val. Qed.

Lemma integral_sin (x : R) : \int[mu]_(z in `[0, x]) sin z = -cos x + 1.
Proof.
  Require Import nsatz_realtype.
rewrite -[in RHS]cos0 [RHS](_ : _ = - cos x - - cos 0); last by nsatz.
rewrite -AC_integral_derive; last first.
  apply C1_is_AC.
  split.
    move => z z0x.
    apply/derivable1_diffP.
    apply derivableN.
    apply: derivable_id.
  apply: continuous_subspaceT.
  admit.
  (* rewrite derive1_cos.
  apply continuous_sin. *)
congr Rintegral.
by rewrite derive1_sin.
Qed.

End examples.