(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval finmap.
Require Import boolp reals ereal exp.
From HB Require Import structures.
Require Import classical_sets signed functions topology normedtype cardinality.
Require Import sequences esum measure numfun lebesgue_measure lebesgue_integral.

(******************************************************************************)
(*                       Probability (experimental)                           *)
(*                                                                            *)
(* This file provides basic notions of probability theory. See measure.v for  *)
(* the type probability T R (a measure that sums to 1).                       *)
(*                                                                            *)
(*          {RV P >-> R} == real random variable: a measurable function from  *)
(*                          the measurableType of the probability P to R      *)
(*        distribution X == measure image of P by X : {RV P -> R}, declared   *)
(*                          as an instance of probability measure             *)
(*               'E_P[X] == expectation of the real measurable function X     *)
(*               'V_P[X] == variance of the real random variable X            *)
(*       {dmfun T >-> R} == type of discrete real-valued measurable functions *)
(*         {dRV P >-> R} == real-valued discrete random variable              *)
(*             dRV_dom X == domain of the discrete random variable X          *)
(*            dRV_eunm X == bijection between the domain and the range of X   *)
(*               pmf X r := fine (P (X @^-1` [set r]))                        *)
(*         enum_prob X k == probability of the kth value in the range of X    *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "'{' 'RV' P >-> R '}'"
  (at level 0, format "'{' 'RV'  P  '>->'  R '}'").
Reserved Notation "''E_' P [ X ]" (format "''E_' P [ X ]", at level 5).
Reserved Notation "''V_' P [ X ]" (format "''V_' P [ X ]", at level 5).
Reserved Notation "{ 'dmfun' aT >-> T }"
  (at level 0, format "{ 'dmfun'  aT  >->  T }").
Reserved Notation "'{' 'dRV' P >-> R '}'"
  (at level 0, format "'{' 'dRV'  P  '>->'  R '}'").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Lspace.
Context d (T : measurableType d) (R : realType).
Variable mu : {finite_measure set T -> \bar R}.

Definition Lp_norm (p : nat) (f : T -> R) : \bar R :=
  ((\int[mu]_x (`|f x| ^+ p)%:E) `^ (p%:R^-1))%E.

Local Notation "`|| f ||_ p" := (Lp_norm p f) (at level 0).

Lemma Lp_norm_ge0 (p : nat) (f : T -> R) : (0 <= `|| f ||_(p%R))%E.
Proof. by rewrite /Lp_norm powere_pos_ge0. Qed.

Section Rintegral.
Implicit Types (f : T -> R) (D : set T).

Lemma eq_Rintegral D g f : {in D, f =1 g} ->
  (\int[mu]_(x in D) f x)%R = (\int[mu]_(x in D) g x)%R.
Proof.
move=> fg.
rewrite /Rintegral.
congr fine.
apply eq_integral => x Dx.
f_equal.
by apply: fg.
Qed.

End Rintegral.

Section fine.
Definition inve (x : \bar R) := EFin ((fine x)^-1).

Lemma fine_inv x : (fine x)^-1 = fine (inve x).
Proof. by case: x. Qed.
End fine.

Lemma powere_pos_lty (x : \bar R) y : (x != +oo -> x `^ y != +oo)%E.
Proof. by case: x => [x| |] //=; case: ifP. Qed.

Lemma powere_pos_lty' (x : \bar R) y : (x `^ y != +oo)%E -> 0 < y -> (x != +oo)%E.
Proof. by case: x => [x| |] //=; case: ifP => // /eqP ->; rewrite ltxx. Qed.

Lemma powere_posAC (x : \bar R) y z : (x `^ y `^ z = x `^ z `^ y)%E.
Proof.
case: x => [x| |]/=; first by rewrite power_posAC //.
  case: ifP => [/eqP ->|] /=.
    case: ifP => [/eqP ->|] //=.
    by rewrite ifT // power_pos1.
  case: ifP => /eqP //=.
    by rewrite power_pos1.
  case: ifP => //.
case: ifP => [/eqP ->|/eqP] /=.
  by case: ifP => [/eqP ->|/eqP] //=; rewrite power_pos0 power_pos1; case: eqP.
case: ifP => /eqP //=.
  by rewrite power_pos1 power_pos0 => z0 _; case: eqP.
by rewrite !power_pos0; case: eqP; case: eqP.
Qed.

Lemma power_posMD (x y z : R) : (x `^ (y * z) = (x `^ y `^ z)).
Proof.
rewrite /power_pos.
have [->/=|y0] := eqVneq y 0.
  rewrite !mul0r expR0.
  case: ifP => /eqP _; case: ifP; rewrite oner_eq0 ?ln1 ?mulr0 ?expR0 //=.
  by case: eqP.
have [->/=|z0] := eqVneq z 0.
  rewrite !mulr0 !mul0r expR0.
  by case: ifP => /eqP _; case: ifP => //; case: eqP.
case: eqP => //= [_|xneq0].
  rewrite ifT // mulIr_eq0; last by apply /rregP.
  by move: y0; case: eqP.
rewrite ifF; last admit.
by rewrite expK mulrA (mulrC z).
Admitted.

Lemma powere_posMD (x : \bar R) y z : (x `^ (y * z) = (x `^ y) `^ z)%E.
Proof.
case: x => [x| |]/=.
- by apply: congr1; exact: power_posMD.
- case: (@eqP _ y) => [->|y0].
    by rewrite mul0r ifT // powere_pos1r.
  have [->|z0] := eqVneq z 0.
    by rewrite mulr0 ifT // powere_pose0.
  rewrite ifF ?powere_posyr //.
  rewrite mulIr_eq0; last by apply /rregP.
  case: eqP => //.
- case: (@eqP _ y) => [->|y0].
    by rewrite mul0r ifT // powere_pos1r.
  have [->|z0] := eqVneq z 0.
    by rewrite mulr0 ifT // powere_pose0.
  rewrite ifF. rewrite powere_pos0r.
  by case: eqP => //; move: z0; case: eqP.
by rewrite mulIr_eq0; [case: eqP|apply /rregP].
Qed.

Local Open Scope ring_scope.
Lemma Lp_norm_hoelder (f g : T -> R) p q :
  (p != 0)%N -> (q != 0)%N ->
  measurable_fun setT f -> measurable_fun setT g ->
  (p%:R^-1 + q%:R^-1 = 1 :> R) ->
    (`|| (f \* g)%R ||_1 <= `|| f ||_p * `|| g ||_q)%E.
Proof.
have Lp_norm_hoelder0 (f' g' : T -> R) p' q' :
  (p' != 0)%N -> (q' != 0)%N ->
  (`|| f' ||_p' = 0)%E ->
  measurable_fun setT f' -> measurable_fun setT g' -> (p'%:R^-1 + q'%:R^-1 = 1 :> R) ->
    (`|| (f' \* g')%R ||_1 <= `|| f' ||_p' * `|| g' ||_q')%E.
  move=> p0 q0 f0 mf mg pq; rewrite f0 mul0e.
  suff: `|| (f' \* g')%R ||_ (1) = 0%E by move=> ->.
  move: f0; rewrite /Lp_norm; move/powere_pos_eq0.
  rewrite /= invr1 powere_pose1// => [fp|]; last by apply: integral_ge0.
  have f0 : ae_eq mu setT (fun x => (`|f' x| ^+ p')%:E) (cst 0%E).
    apply/ae_eq_integral_abs => //=.
      by apply: measurableT_comp => //; apply: (measurableT_comp (f := fun (x : R) => x ^+ p')) => //; apply: measurableT_comp => //=.
    under eq_integral => x _. rewrite ger0_norm. over. 
      by apply exprn_ge0; apply normr_ge0.
    by apply fp; apply: lt_le_trans; last
      by apply: integral_ge0 => x _; apply: exprn_ge0; apply: normr_ge0.
  rewrite (ae_eq_integral (cst 0)%E) => //.
  - by rewrite integral_cst // mul0e.
  - by apply measurableT_comp => //;
      have ->: (fun x : T => (`|f' x * g' x| ^+ 1)) = normr \o (fun x : T => f' x * g' x) => //;
      apply measurableT_comp => //; apply measurable_funM.
  apply: filterS => [x fp0 _|]; [move: fp0 => /= fp0|apply f0].
  apply congr1; apply EFin_inj in fp0 => //; rewrite expr1.
  have ->: f' x = 0.
    move: fp0; apply contraPP; move/eqP; rewrite -normr_gt0.
    move=> fp0; apply/eqP; apply lt0r_neq0.
    rewrite (_ : 0 = (p' == 0%N)%:R) -?expr0n //=; first by rewrite ltr_expn2r => //.
    by rewrite expr0n (negPf p0).
  by rewrite mul0r normr0 //.
move=> p0 q0 mf mg pq.
have [f0|f0] := eqVneq (`|| f ||_ (p)) 0%E; first by apply Lp_norm_hoelder0.
have [g0|g0] := eqVneq (`|| g ||_ (q)) 0%E.
  rewrite muleC.
  have ->: `|| (f \* g)%R ||_ (1) = `|| (g \* f)%R ||_ (1)
    by apply congr1; rewrite /GRing.mul_fun; apply funext => x; rewrite mulrC.
  by apply Lp_norm_hoelder0 => //; rewrite addrC.
have [foo|foo] := eqVneq (`|| f ||_(p)) +oo%E.
  rewrite foo gt0_mulye ?leey//.
  by rewrite lt_neqAle eq_sym g0/= powere_pos_ge0.
have [goo|goo] := eqVneq (`|| g ||_(q)) +oo%E.
  rewrite goo gt0_muley ?leey//.
  by rewrite lt_neqAle eq_sym f0/= powere_pos_ge0.
have fpos : (0 < `|| f ||_ (p))%E
  by rewrite lt_neqAle eq_sym; apply/andP; split; [|apply Lp_norm_ge0].
have gpos : (0 < `|| g ||_ (q))%E
  by rewrite lt_neqAle eq_sym; apply/andP; split; [|apply Lp_norm_ge0].
have mfpow : measurable_fun [set: T] (fun x : T => (`|f x| `^ p%:R)%:E)
  by apply: measurableT_comp => //;
     apply: (@measurableT_comp _ _ _ _ _ _ (fun x => power_pos x (p%:R))) => //;
     apply: measurableT_comp => //.
have mgpow : measurable_fun [set: T] (fun x : T => (`|g x| `^ q%:R)%:E)
  by apply: measurableT_comp => //;
    apply: (@measurableT_comp _ _ _ _ _ _ (fun x => power_pos x (q%:R))) => //;
    apply: measurableT_comp => //.
have ifpow : mu.-integrable [set: T] (fun x : T => (`|f x| `^ p%:R)%:E).
  rewrite /integrable ltey; split; first apply mfpow.
  apply powere_pos_lty' in foo => //; last by
    rewrite invr_gt0 ltr0n lt0n.
  by under eq_integral => x _ do rewrite power_pos_mulrn // gee0_abs //.
have igpow : mu.-integrable [set: T] (fun x : T => (`|g x| `^ q%:R)%:E).
  rewrite /integrable ltey; split; first apply mgpow.
  apply powere_pos_lty' in goo => //; last by
    rewrite invr_gt0 ltr0n lt0n.
  by under eq_integral => x _ do rewrite power_pos_mulrn // gee0_abs //.
pose F f p x := `| f x | / (fine `|| f ||_p).
have Fp1 f' p' : p' != 0%N -> (`|| f' ||_(p') != +oo)%E -> mu.-integrable [set: T] (fun x : T => (`|f' x| `^ p'%:R)%:E)
 -> \int[mu]_x (F f' p' x `^ p'%:R) = 1.
  rewrite /F => p0' foo'.
  transitivity (\int[mu]_x ((`|f' x| `^ p' %:R) / (fine `|| f' ||_ (p') `^ p'%:R))).
    apply: eq_Rintegral => t _.
    rewrite power_posM //; last by rewrite invr_ge0 fine_ge0 // Lp_norm_ge0.
    rewrite -power_pos_inv1; last by rewrite fine_ge0 // Lp_norm_ge0.
    by rewrite power_posAC -power_pos_inv1 // power_pos_ge0.
  transitivity (
    \int[mu]_x (`|f' x| `^ p'%:R) / (fine (`|| f' ||_ (p') `^ p'%:R))
  ).
    rewrite /Rintegral fine_inv mulrC -fineM => //;
      last first.
      apply/fin_numP; split.
        rewrite -ltNye; apply: lt_le_trans; first apply ltNyr.
        by apply integral_ge0 => x _; apply power_pos_ge0.
      apply powere_pos_lty' in foo'; last by rewrite invr_gt0 ltr0n lt0n.
      by under eq_integral => x _ do rewrite power_pos_mulrn //.
    apply congr1; rewrite -integralM //.
    apply eq_integral => x _; rewrite mulrC -EFinM.
    apply congr1; apply congr2 => //; apply congr1.
    by rewrite -fine_powere_pos.
  rewrite /Lp_norm.
  rewrite -powere_posMD.
  rewrite mulVf; last admit.
  rewrite powere_pose1; last first.
    apply integral_ge0 => x _; rewrite lee_fin; apply exprn_ge0; apply: normr_ge0.
  admit.
pose s x := ln ((F f p x) `^ p%:R).
pose t x := ln ((F g q x) `^ q%:R).
have Fs x : F f p x = expR (s x / p%:R).
  rewrite /F /s.
  admit.
have Gt x : F g q x = expR (t x / q%:R).
  admit.
have exp_convex x : F f p x * F g q x <= (F f p x) `^ p%:R / p%:R + (F f p x) `^ q%:R / q%:R.
  rewrite /F.
  have: expR (s x / p%:R + t x / q%:R) <= p%:R^-1 * expR (s x) + q%:R^-1 * expR (t x).
    admit. (* using convexity of exp *)
  rewrite expRD.
  rewrite -/(F f p x).
  rewrite -/(F g q x).
  rewrite -Fs -Gt => /le_trans; apply.
  rewrite /s /t.
  rewrite [X in _ * X + _](@lnK _ (F f p x `^ p%:R)); last by admit.
  admit.
Admitted.
(* follow http://pi.math.cornell.edu/~erin/analysis/lectures.pdf version with convexity, not young inequality *)
End Lspace.

Definition random_variable (d : _) (T : measurableType d) (R : realType)
  (P : probability T R) := {mfun T >-> R}.

Notation "{ 'RV' P >-> R }" := (@random_variable _ _ R P) : form_scope.

Lemma notin_range_measure d (T : measurableType d) (R : realType)
    (P : {measure set T -> \bar R}) (X : T -> R) r :
  r \notin range X -> P (X @^-1` [set r]) = 0%E.
Proof. by rewrite notin_set => hr; rewrite preimage10. Qed.

Lemma probability_range d (T : measurableType d) (R : realType)
  (P : probability T R) (X : {RV P >-> R}) : P (X @^-1` range X) = 1%E.
Proof. by rewrite preimage_range probability_setT. Qed.

Definition distribution (d : _) (T : measurableType d) (R : realType)
    (P : probability T R) (X : {mfun T >-> R}) :=
  pushforward P (@measurable_funP _ _ _ X).

Section distribution_is_probability.
Context d (T : measurableType d) (R : realType) (P : probability T R)
        (X : {mfun T >-> R}).

Let distribution0 : distribution P X set0 = 0%E.
Proof. exact: measure0. Qed.

Let distribution_ge0 A : (0 <= distribution P X A)%E.
Proof. exact: measure_ge0. Qed.

Let distribution_sigma_additive : semi_sigma_additive (distribution P X).
Proof. exact: measure_semi_sigma_additive. Qed.

HB.instance Definition _ := isMeasure.Build _ R _ (distribution P X)
  distribution0 distribution_ge0 distribution_sigma_additive.

Let distribution_is_probability : distribution P X [set: _] = 1%:E.
Proof.
by rewrite /distribution /= /pushforward /= preimage_setT probability_setT.
Qed.

HB.instance Definition _ := Measure_isProbability.Build _ _ R
  (distribution P X) distribution_is_probability.

End distribution_is_probability.

Section transfer_probability.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma probability_distribution (X : {RV P >-> R}) r :
  P [set x | X x = r] = distribution P X [set r].
Proof. by []. Qed.

Lemma integral_distribution (X : {RV P >-> R}) (f : R -> \bar R) :
    measurable_fun [set: R] f -> (forall y, 0 <= f y) ->
  \int[distribution P X]_y f y = \int[P]_x (f \o X) x.
Proof. by move=> mf f0; rewrite integral_pushforward. Qed.

End transfer_probability.

Section expectation.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition expectation (X : T -> R) := \int[P]_w (X w)%:E.

End expectation.
Arguments expectation {d T R} P _%R.
Notation "''E_' P [ X ]" := (@expectation _ _ _ P X).

Section expectation_lemmas.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma expectation_cst r : 'E_P[cst r] = r%:E.
Proof. by rewrite /expectation /= integral_cst//= probability_setT mule1. Qed.

Lemma expectation_indic (A : set T) (mA : measurable A) : 'E_P[\1_A] = P A.
Proof. by rewrite /expectation integral_indic// setIT. Qed.

Lemma integrable_expectation (X : {RV P >-> R})
  (iX : P.-integrable [set: T] (EFin \o X)) : `| 'E_P[X] | < +oo.
Proof.
move: iX => [? Xoo]; rewrite (le_lt_trans _ Xoo)//.
exact: le_trans (le_abse_integral _ _ _).
Qed.

Lemma expectationM (X : {RV P >-> R}) (iX : P.-integrable [set: T] (EFin \o X))
  (k : R) : 'E_P[k \o* X] = k%:E * 'E_P [X].
Proof.
rewrite /expectation.
under eq_integral do rewrite EFinM.
rewrite -integralM//.
by under eq_integral do rewrite muleC.
Qed.

Lemma expectation_ge0 (X : {RV P >-> R}) :
  (forall x, 0 <= X x)%R -> 0 <= 'E_P[X].
Proof.
by move=> ?; rewrite /expectation integral_ge0// => x _; rewrite lee_fin.
Qed.

Lemma expectation_le (X Y : T -> R) :
    measurable_fun [set: T] X -> measurable_fun [set: T] Y ->
    (forall x, 0 <= X x)%R -> (forall x, 0 <= Y x)%R ->
  {ae P, (forall x, X x <= Y x)%R} -> 'E_P[X] <= 'E_P[Y].
Proof.
move=> mX mY X0 Y0 XY; rewrite /expectation ae_ge0_le_integral => //.
- by move=> t _; apply: X0.
- by apply EFin_measurable_fun.
- by move=> t _; apply: Y0.
- by apply EFin_measurable_fun.
- move: XY => [N [mN PN XYN]]; exists N; split => // t /= h.
  by apply: XYN => /=; apply: contra_not h; rewrite lee_fin.
Qed.

Lemma expectationD (X Y : {RV P >-> R}) :
    P.-integrable [set: T] (EFin \o X) -> P.-integrable [set: T] (EFin \o Y) ->
  'E_P[X \+ Y] = 'E_P[X] + 'E_P[Y].
Proof. by move=> ? ?; rewrite /expectation integralD_EFin. Qed.

Lemma expectationB (X Y : {RV P >-> R}) :
    P.-integrable [set: T] (EFin \o X) -> P.-integrable [set: T] (EFin \o Y) ->
  'E_P[X \- Y] = 'E_P[X] - 'E_P[Y].
Proof. by move=> ? ?; rewrite /expectation integralB_EFin. Qed.

(* To be used in cauchy_schwarz *)
Lemma expectation_sqr_is_l2_norm (X : {RV P >-> R}) :
  Lp_norm P 2 X = sqrte 'E_P[X ^+ 2].
Proof.
  rewrite /Lp_norm /expectation powere12_sqrt.
  apply congr1; apply eq_integral => x _ /=; apply congr1.
  rewrite real_normK //; apply num_real.
  apply integral_ge0 => x _; rewrite lee_fin; apply sqr_ge0.
Qed.

Lemma expectation_sqr_eq0 (X : {RV P >-> R}) :
  'E_P[X ^+ 2] = 0 -> ae_eq P setT (EFin \o X) (EFin \o cst 0%R).
Proof.
move => hx.
have x20: ae_eq P setT (EFin \o (X ^+ 2)%R) (EFin \o cst 0%R).
  apply ae_eq_integral_abs => //; first by apply/EFin_measurable_fun.
    have -> : \int[P]_x `|(EFin \o (X ^+ 2)%R) x| = 'E_P[X ^+ 2] => //.
      under eq_integral => x _. rewrite gee0_abs. over.
      apply sqr_ge0.
      reflexivity.
apply: (ae_imply _ x20) => x /=.
rewrite -expr2 => h0 _.
apply EFin_inj in h0 => //.
have: (X ^+ 2)%R x == 0%R. rewrite -h0 //.
rewrite sqrf_eq0 /= => h1.
rewrite (eqP h1) //.
Qed.

End expectation_lemmas.

Section variance.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition variance (X : T -> R) := 'E_P[(X \- cst (fine 'E_P[X])) ^+ 2]%R.
Local Notation "''V_' P [ X ]" := (variance X).

Lemma varianceE (X : {RV P >-> R}) :
  (* TODO: check what happens when X is not integrable *)
  P.-integrable setT (EFin \o X) ->
  P.-integrable setT (EFin \o (X ^+ 2)%R) ->
  (*X \in P.-Lspace 1 -> X \in P.-Lspace 2 ->*)
  (* NB: Lspace 2 -> Lspace 1 *)
  'V_P[X] = 'E_P[X ^+ 2] - ('E_P[X]) ^+ 2.
Proof.
move=> X1 X2.
(*have ? : P.-integrable [set: T] (EFin \o X) by rewrite Lspace1 in X1.
have ? : P.-integrable [set: T] (EFin \o (X ^+ 2)%R)  by apply: Lspace2.*)
have ? : 'E_P[X] \is a fin_num by rewrite fin_num_abs// integrable_expectation.
rewrite /variance.
rewrite [X in 'E_P[X]](_ : _ = (X ^+ 2 \- (2 * fine 'E_P[X]) \o* X \+
    fine ('E_P[X] ^+ 2) \o* cst 1)%R); last first.
  by apply/funeqP => x /=; rewrite -expr2 sqrrB mulr_natl -mulrnAr mul1r fineM.
rewrite expectationD/=; last 2 first.
  - rewrite compreBr; last by [].
    apply: integrableB; [exact: measurableT|assumption|].
    by rewrite compre_scale; [exact: integrablerM|by []].
  - rewrite compre_scale; last by [].
    apply: integrablerM; first exact: measurableT.
    exact: finite_measure_integrable_cst.
rewrite expectationB/=; [|assumption|]; last first.
  by rewrite compre_scale; [exact: integrablerM|by []].
rewrite expectationM// expectationM; last exact: finite_measure_integrable_cst.
rewrite expectation_cst mule1 EFinM fineK// fineK ?fin_numM// -muleA -expe2.
rewrite mule_natl mule2n oppeD; last by rewrite fin_num_adde_defl// fin_numX.
by rewrite addeA subeK// fin_numX.
Qed.

End variance.
Notation "'V_ P [ X ]" := (variance P X).

Section markov_chebyshev.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma markov (X : {RV P >-> R}) (f : R -> R) (eps : R) :
    (0 < eps)%R ->
    measurable_fun [set: R] f -> (forall r : R, 0 <= f r)%R ->
    {in `[0, +oo[%classic &, {homo f : x y / x <= y}}%R ->
  (f eps)%:E * P [set x | eps%:E <= `| (X x)%:E | ] <=
    'E_P[f \o (fun x => `| x |%R) \o X].
Proof.
move=> e0 mf f0 f_nd; rewrite -(setTI [set _ | _]).
apply: (le_trans (@le_integral_comp_abse d T R P setT measurableT (EFin \o X)
  eps (er_map f) _ _ _ _ e0)) => //=.
- exact: measurable_fun_er_map.
- by case => //= r _; exact: f0.
- exact: le_er_map.
- exact/EFin_measurable_fun.
Qed.

Lemma chebyshev (X : {RV P >-> R}) (eps : R) : (0 < eps)%R ->
  P [set x | (eps <= `| X x - fine ('E_P[X])|)%R ] <= (eps ^- 2)%:E * 'V_P[X].
Proof.
move => heps; have [->|hv] := eqVneq ('V_P[X])%E +oo%E.
  by rewrite mulr_infty gtr0_sg ?mul1e// ?leey// invr_gt0// exprn_gt0.
have h (Y : {RV P >-> R}) :
    P [set x | (eps <= `|Y x|)%R] <= (eps ^- 2)%:E * 'E_P[Y ^+ 2].
  rewrite -lee_pdivr_mull; last by rewrite invr_gt0// exprn_gt0.
  rewrite exprnN expfV exprz_inv opprK -exprnP.
  apply: (@le_trans _ _ ('E_P[(@GRing.exp R ^~ 2%N \o normr) \o Y])).
    apply: (@markov Y (@GRing.exp R ^~ 2%N)) => //.
    - exact/measurable_fun_exprn/measurable_fun_id.
    - by move=> r; apply: sqr_ge0.
    - move=> x y; rewrite !inE !mksetE !in_itv/= !andbT => x0 y0.
      by rewrite ler_sqr.
  apply: expectation_le => //.
  - apply: measurable_funT_comp => //; apply: measurable_funT_comp => //.
    exact/measurable_fun_exprn/measurable_fun_id.
  - by move=> x /=; apply: sqr_ge0.
  - by move=> x /=; apply: sqr_ge0.
simpl.


  - by apply/aeW => t /=; rewrite real_normK// num_real.
have := h [the {mfun T >-> R} of (X \- cst (fine ('E_P[X])))%R].
by move=> /le_trans; apply; rewrite lee_pmul2l// lte_fin invr_gt0 exprn_gt0.
Qed.

End markov_chebyshev.


HB.mixin Record MeasurableFun_isDiscrete d (T : measurableType d) (R : realType)
    (X : T -> R) of @MeasurableFun d T R X := {
  countable_range : countable (range X)
}.

HB.structure Definition discreteMeasurableFun d (T : measurableType d)
    (R : realType) := {
  X of isMeasurableFun d T R X & MeasurableFun_isDiscrete d T R X
}.

Notation "{ 'dmfun' aT >-> T }" :=
  (@discreteMeasurableFun.type _ aT T) : form_scope.

Definition discrete_random_variable (d : _) (T : measurableType d)
  (R : realType) (P : probability T R) := {dmfun T >-> R}.

Notation "{ 'dRV' P >-> R }" :=
  (@discrete_random_variable _ _ R P) : form_scope.

Section dRV_definitions.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition dRV_dom_enum (X : {dRV P >-> R}) :
  { B : set nat & {splitbij B >-> range X}}.
have /countable_bijP/cid[B] := @countable_range _ _ _ X.
move/card_esym/ppcard_eqP/unsquash => f.
exists B; exact: f.
Qed.

Definition dRV_dom (X : {dRV P >-> R}) : set nat := projT1 (dRV_dom_enum X).

Definition dRV_enum (X : {dRV P >-> R}) : {splitbij (dRV_dom X) >-> range X} :=
  projT2 (dRV_dom_enum X).

Definition enum_prob (X : {dRV P >-> R}) :=
  (fun k => P (X @^-1` [set dRV_enum X k])) \_ (dRV_dom X).

End dRV_definitions.

Section distribution_dRV.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Variable X : {dRV P >-> R}.

Lemma distribution_dRV_enum (n : nat) : n \in dRV_dom X ->
  distribution P X [set dRV_enum X n] = enum_prob X n.
Proof.
by move=> nX; rewrite /distribution/= /enum_prob/= patchE nX.
Qed.

Lemma distribution_dRV A : measurable A ->
  distribution P X A = \sum_(k <oo) enum_prob X k * \d_ (dRV_enum X k) A.
Proof.
move=> mA; rewrite /distribution /pushforward.
have mAX i : dRV_dom X i -> measurable (X @^-1` (A `&` [set dRV_enum X i])).
  move=> _; rewrite preimage_setI; apply: measurableI => //.
  exact/measurable_sfunP.
have tAX : trivIset (dRV_dom X) (fun k => X @^-1` (A `&` [set dRV_enum X k])).
  under eq_fun do rewrite preimage_setI; rewrite -/(trivIset _ _).
  apply: trivIset_setIl; apply/trivIsetP => i j iX jX /eqP ij.
  rewrite -preimage_setI (_ : _ `&` _ = set0)//.
  by apply/seteqP; split => //= x [] -> {x} /inj; rewrite inE inE => /(_ iX jX).
have := measure_bigcup P _ (fun k => X @^-1` (A `&` [set dRV_enum X k])) mAX tAX.
rewrite -preimage_bigcup => {mAX tAX}PXU.
rewrite -{1}(setIT A) -(setUv (\bigcup_(i in dRV_dom X) [set dRV_enum X i])).
rewrite setIUr preimage_setU measureU; last 3 first.
  - rewrite preimage_setI; apply: measurableI => //.
      exact: measurable_sfunP.
    by apply: measurable_sfunP; exact: bigcup_measurable.
  - apply: measurable_sfunP; apply: measurableI => //.
    by apply: measurableC; exact: bigcup_measurable.
  - rewrite 2!preimage_setI setIACA -!setIA -preimage_setI.
    by rewrite setICr preimage_set0 2!setI0.
rewrite [X in _ + X = _](_ : _ = 0) ?adde0; last first.
  rewrite (_ : _ @^-1` _ = set0) ?measure0//; apply/disjoints_subset => x AXx.
  rewrite setCK /bigcup /=; exists ((dRV_enum X)^-1 (X x))%function.
    exact: funS.
  by rewrite invK// inE.
rewrite setI_bigcupr; etransitivity; first exact: PXU.
rewrite eseries_mkcond; apply: eq_eseriesr => k _.
rewrite /enum_prob patchE; case: ifPn => nX; rewrite ?mul0e//.
rewrite diracE; have [kA|] := boolP (_ \in A).
  by rewrite mule1 setIidr// => _ /= ->; exact: set_mem.
rewrite notin_set => kA.
rewrite mule0 (disjoints_subset _ _).2 ?preimage_set0 ?measure0//.
by apply: subsetCr; rewrite sub1set inE.
Qed.

Lemma sum_enum_prob : (\sum_(n <oo) (enum_prob X) n = 1)%E.
Proof.
have := distribution_dRV measurableT.
rewrite probability_setT/= => /esym; apply: eq_trans.
by rewrite [RHS]eseries_mkcond; apply: eq_eseriesr => k _; rewrite diracT mule1.
Qed.

End distribution_dRV.

Section discrete_distribution.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma dRV_expectation (X : {dRV P >-> R}) : P.-integrable [set: T] (EFin \o X) ->
  'E_P[X] = (\sum_(n <oo) enum_prob X n * (dRV_enum X n)%:E)%E.
Proof.
move=> ix; rewrite /expectation.
rewrite -[in LHS](_ : \bigcup_k (if k \in dRV_dom X then
    X @^-1` [set dRV_enum X k] else set0) = setT); last first.
  apply/seteqP; split => // t _.
  exists ((dRV_enum X)^-1%function (X t)) => //.
  case: ifPn=> [_|].
    by rewrite invK// inE.
  by rewrite notin_set/=; apply; apply: funS.
have tA : trivIset (dRV_dom X) (fun k => [set dRV_enum X k]).
  by move=> i j iX jX [r [/= ->{r}]] /inj; rewrite !inE; exact.
have {tA}/trivIset_mkcond tXA :
    trivIset (dRV_dom X) (fun k => X @^-1` [set dRV_enum X k]).
  apply/trivIsetP => /= i j iX jX ij.
  move/trivIsetP : tA => /(_ i j iX jX) Aij.
  by rewrite -preimage_setI Aij ?preimage_set0.
rewrite integral_bigcup //; last 2 first.
  - by move=> k; case: ifPn.
  - apply: (integrableS measurableT) => //.
    by rewrite -bigcup_mkcond; exact: bigcup_measurable.
transitivity (\sum_(i <oo)
    \int[P]_(x in (if i \in dRV_dom X then X @^-1` [set dRV_enum X i] else set0))
      (dRV_enum X i)%:E)%E.
  apply: eq_eseriesr => i _; case: ifPn => iX.
    by apply: eq_integral => t; rewrite in_setE/= => ->.
  by rewrite !integral_set0.
transitivity (\sum_(i <oo) (dRV_enum X i)%:E *
    \int[P]_(x in (if i \in dRV_dom X then X @^-1` [set dRV_enum X i] else set0))
      1)%E.
  apply: eq_eseriesr => i _; rewrite -integralM//; last 2 first.
    - by case: ifPn.
    - split; first exact: measurable_fun_cst.
      rewrite (eq_integral (cst 1%E)); last by move=> x _; rewrite abse1.
      rewrite integral_cst//; last by case: ifPn.
      rewrite mul1e (@le_lt_trans _ _ 1%E) ?ltey//.
      by case: ifPn => // _; exact: probability_le1.
  by apply: eq_integral => y _; rewrite mule1.
apply: eq_eseriesr => k _; case: ifPn => kX.
  rewrite /= integral_cst//= mul1e probability_distribution muleC.
  by rewrite distribution_dRV_enum.
by rewrite integral_set0 mule0 /enum_prob patchE (negbTE kX) mul0e.
Qed.

Definition pmf (X : {RV P >-> R}) (r : R) : R := fine (P (X @^-1` [set r])).

Local Open Scope ereal_scope.
Lemma expectation_pmf (X : {dRV P >-> R}) :
    P.-integrable [set: T] (EFin \o X) -> 'E_P[X] =
  \sum_(n <oo | n \in dRV_dom X) (pmf X (dRV_enum X n))%:E * (dRV_enum X n)%:E.
Proof.
move=> iX; rewrite dRV_expectation// [in RHS]eseries_mkcond.
apply: eq_eseriesr => k _.
rewrite /enum_prob patchE; case: ifPn => kX; last by rewrite mul0e.
by rewrite /pmf fineK// fin_num_measure.
Qed.
Local Close Scope ereal_scope.

End discrete_distribution.

Section covariance.
Local Open Scope ereal_scope.
Variables (d : _) (T : measurableType d) (R : realType) (P : probability T R).

Definition covariance (X Y : {RV P >-> R}) :=
  ('E_P [(X \- cst (fine 'E_P[X])) \* (Y \- cst (fine 'E_P[Y]))])%R.
Local Notation "''Cov' [ X , Y ]" := (covariance X Y).

(* Note: this could actually be proved as a special case of hoelder's inequality,
   by choosing p = q = 2, see https://en.wikipedia.org/wiki/H%C3%B6lder%27s_inequality *)
Lemma cauchy_schwarz (X Y : {RV P >-> R}) :
  P.-integrable [set: T] (EFin \o X) -> P.-integrable [set: T] (EFin \o Y) ->
  (* 'E X < +oo -> 'E Y < +oo -> TODO: use lspaces *)
    'E_P[(X \* Y)%R] ^+2 <= 'E_P[(X ^+ 2)%R] * 'E_P[(Y ^+ 2)%R].
Proof.
move => hfinex hfiney.
have mf : measurable_fun [set: T] X by admit.
have mg : measurable_fun [set: T] Y by admit.
have twoone : (2^-1 + 2^-1)%R = 1%R :> R by admit.
have := @Lp_norm_hoelder d T R P X Y 2%N 2%N erefl erefl mf mg twoone.
rewrite /expectation /Lp_norm/=.
under eq_integral do rewrite expr1.
rewrite invr1.
rewrite powere_funr1; last by admit.
Admitted.

(* Old proof not using hoelder:
pose a := Num.sqrt (fine 'E_P[(Y ^+ 2)%R]).
pose b := Num.sqrt (fine 'E_P[(X ^+ 2)%R]).
have ex2_ge0 : 0 <= 'E_P[(X ^+ 2)%R] by apply expectation_ge0 => x /=; exact: sqr_ge0.
have ey2_ge0 : 0 <= 'E_P[(Y ^+ 2)%R] by apply expectation_ge0 => x /=; exact: sqr_ge0.
have [a0|a0] := eqVneq ('E_P[(Y ^+ 2)%R]) 0.
- rewrite a0 adde0.
  have y0: ae_eq P setT (EFin \o Y) (EFin \o cst 0%R) by apply expectation_sqr_eq0.
  have -> : 'E_P[X \* Y] = 'E_P[cst 0%R].
    apply: ae_eq_integral => //=.
      apply measurable_funT_comp => //; apply measurable_funM => //.
      apply measurable_fun_cst.
      apply: (ae_imply _ y0) => x /= h _.
      apply EFin_inj in h => //.
      by rewrite h mulr0.
  rewrite expectation_cst /= mule0.
  apply expectation_ge0 => x.
  apply sqr_ge0.
have [b0|b0] := eqVneq ('E_P[(X ^+ 2)%R]) 0.
- rewrite b0 add0e.
  have x0: ae_eq P setT (EFin \o X) (EFin \o cst 0%R) by apply expectation_sqr_eq0.
  have -> : 'E_P[X \* Y] = 'E_P[cst 0%R].
    apply: ae_eq_integral => //=.
      apply measurable_funT_comp => //; apply measurable_funM => //.
      apply measurable_fun_cst.
      apply: (ae_imply _ x0) => x /= h _.
      apply EFin_inj in h => //.
      by rewrite h mul0r.
  rewrite expectation_cst /= mule0.
  apply expectation_ge0 => x.
  apply sqr_ge0.
have H2ab : (2 * a * b * (b * a) = a * a * (fine 'E_P[X ^+ 2]) + b * b * (fine 'E_P[Y ^+ 2]))%R.
  rewrite -(sqr_sqrtr (a:=fine 'E_P[X ^+ 2])); last (apply: fine_ge0; apply: expectation_ge0 => x; apply sqr_ge0).
  rewrite -(sqr_sqrtr (a:=fine 'E_P[Y ^+ 2])); last (apply: fine_ge0; apply: expectation_ge0 => x; apply sqr_ge0).
  rewrite -/a -/b /GRing.exp /=.
  by rewrite mulrA (mulrC (_ * _) a)%R ![in LHS]mulrA (mulrC a) (mulrC _ (a * a)%R)
             -![in LHS]mulrA mulrC mulr2n !mulrA mulrDr mulr1. *)

Lemma cauchy_schwarz' (X Y : {RV P >-> R}) :
  ('Cov[ X , Y ])^+2 <= 'V_P[X] + 'V_P[Y].
Admitted.

End covariance.
Notation "''Cov' [ X , Y ]" := (covariance X Y).
