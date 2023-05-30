(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval finmap.
From HB Require Import structures.
From mathcomp.classical Require Import mathcomp_extra cardinality boolp.
From mathcomp.classical Require Import classical_sets functions.
Require Import signed reals ereal sequences exp itv topology normedtype esum.
Require Import numfun  measure convex lebesgue_measure lebesgue_integral.

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

(* TODO: PR *)
Section inve.
Context {R : realFieldType}.

Definition inve (x : \bar R) :=
  match x with
  | x%:E => x^-1%:E
  | +oo%E => +oo%E
  | -oo%E => -oo%E
  end.

Lemma inve_fin_num (x : \bar R) : (inve x \is a fin_num) = (x \is a fin_num).
Proof. by move: x => [x| |]. Qed.

Lemma fine_inv x : (fine x)^-1 = fine (inve x).
Proof. by case: x => //=; rewrite invr0. Qed.

Lemma inveM x y : (x != 0 -> y != 0 -> inve x * inve y = inve (x * y))%E.
Proof.
move: x y => [x| |] [y| |]//=; rewrite ?eqE/=.
- by move=> x0 y0; rewrite -EFinM invfM.
- rewrite neq_lt => /orP[|] x0 _.
  + by rewrite mulry sgrV [in RHS]mulry ltr0_sg// mulN1e.
  + by rewrite mulry sgrV [in RHS]mulry gtr0_sg// mul1e.
- rewrite neq_lt => /orP[|] x0 _.
  + by rewrite mulrNy sgrV [in RHS]mulrNy ltr0_sg// mulN1e.
  + by rewrite mulrNy sgrV [in RHS]mulrNy gtr0_sg// mul1e.
- move=> _; rewrite neq_lt => /orP[|] y0.
  + by rewrite mulyr sgrV [in RHS]mulyr ltr0_sg// mulN1e.
  + by rewrite mulyr sgrV [in RHS]mulyr gtr0_sg// mul1e.
- by rewrite mulyy.
- by rewrite mulyNy.
- move=> _; rewrite neq_lt => /orP[|] y0.
  + by rewrite mulNyr sgrV [in RHS]mulNyr ltr0_sg// mulN1e.
  + by rewrite mulNyr sgrV [in RHS]mulNyr gtr0_sg// mul1e.
- by rewrite mulNyy.
Qed.

Lemma inveK x : (x != 0 -> x \is a fin_num -> x * inve x = 1)%E.
Proof.
case: x => [x x0| |] //=.
by rewrite /inve /= -EFinM ?neq_lt // mulrC mulVf.
Qed.

End inve.

(* TODO: PR *)
Section power_pos.
Context {R : realType}.

Lemma power_posMD (x y z : R) : x `^ (y * z) = x `^ y `^ z.
Proof.
rewrite /power_pos.
have [->/=|y0] := eqVneq y 0%R.
  rewrite !mul0r expR0.
  case: ifP => /eqP _; case: ifP; rewrite oner_eq0 ?ln1 ?mulr0 ?expR0 //=.
  by case: eqP.
have [->/=|z0] := eqVneq z 0%R.
  rewrite !mulr0 !mul0r expR0.
  by case: ifP => /eqP _; case: ifP => //; case: eqP.
case: eqP => //= [_|xneq0].
  rewrite ifT // mulIr_eq0; last by apply /rregP.
  by move: y0; case: eqP.
by rewrite gt_eqF ?expR_gt0// expK mulrCA mulrA.
Qed.

Lemma power_pos_gt0_inv (x : R) (r : R) : 0 < r -> 0 <= x -> 0 < x `^ r -> 0 < x.
Proof.
move=> r0 x0.
rewrite /power_pos; case: ifPn => [_|x0' _].
  by rewrite gt_eqF//= ltxx.
by rewrite lt_neqAle x0 andbT eq_sym.
Qed.

Lemma ler_power_pos' (a : R) : 0 < a ->
  {in `[0, +oo[%classic &, {homo @power_pos R ^~ a : x y / x <= y >-> x <= y}}.
Proof.
move=> a0 u v; rewrite !inE /= !in_itv/= !andbT.
rewrite !le_eqVlt => /orP[/eqP<-|u0].
  move=> /orP[/eqP<- _|v0 _].
    by rewrite eqxx.
  rewrite power_pos0; apply/orP; right.
  by rewrite gt_eqF//= power_pos_gt0.
move=> /orP[/eqP<-|v0].
  by rewrite gt_eqF//= ltNge (ltW u0).
move=> /orP[/eqP->//|uv]; first by rewrite eqxx.
apply/orP; right.
by rewrite /power_pos !gt_eqF// ltr_expR ltr_pmul2l// ltr_ln.
Qed.

Lemma lt0_norm_power_pos (a p : R) : a < 0 -> `|a `^ p| = 1.
Proof.
move=> a0.
rewrite /power_pos.
by rewrite lt_eqF// gtr0_norm ?expR_gt0// ln0 ?mulr0 ?expR0// ltW.
Qed.

Lemma norm_power_pos (a p : R) : 0 <= a -> `|a `^ p| = `|a| `^ p.
Proof.
move=> a0.
rewrite /power_pos; case: ifPn => [/eqP ->|].
  by rewrite normr0 eqxx normr_nat.
rewrite neq_lt ltNge a0/= => {}a0.
by rewrite gtr0_norm ?expR_gt0// gtr0_norm// gt_eqF.
Qed.

End power_pos.

Section powere_pos.
Context {R : realType}.
Local Open Scope ereal_scope.

Lemma powere_pos_lty (x : \bar R) y : x != +oo -> x `^ y != +oo.
Proof. by case: x => [x| |] //=; case: ifP. Qed.

Lemma powere_pos_lty' (x : \bar R) y : (0 < y)%R -> x `^ y != +oo -> x != +oo.
Proof. by case: x => [x| |] //=; case: ifP => // /eqP ->; rewrite ltxx. Qed.

Lemma powere_posAC (x : \bar R) y z : x `^ y `^ z = x `^ z `^ y.
Proof.
case: x => [x| |]/=; first by rewrite power_posAC.
  case: ifPn => [/eqP ->|] /=.
    by case: ifPn => [/eqP ->|] //=; rewrite eqxx power_pos1.
  by case: ifPn => /eqP /=; [rewrite power_pos1|case: ifP].
case: ifPn => [/eqP ->|] /=.
  by case: ifPn => [/eqP ->|] //=; rewrite power_pos0 power_pos1 eqxx.
case: ifPn => [/eqP ->|]/=; first by rewrite power_pos0 eqxx power_pos1.
by rewrite !power_pos0 => /negbTE -> /negbTE ->.
Qed.

Lemma powere_posMD (x : \bar R) y z : (x `^ (y * z) = (x `^ y) `^ z).
Proof.
case: x => [x| |]/=.
- by apply: congr1; exact: power_posMD.
- have [->|y0] := eqVneq y 0%R.
    by rewrite mul0r eqxx powere_pos1r.
  have [->|z0] := eqVneq z 0%R.
    by rewrite mulr0 eqxx powere_pose0.
  by rewrite mulf_eq0 (negbTE z0) orbF (negbTE y0) ?powere_posyr.
- have [->|y0] := eqVneq y 0%R.
    by rewrite mul0r eqxx powere_pos1r.
  have [->|z0] := eqVneq z 0%R.
    by rewrite mulr0 eqxx powere_pose0.
  by rewrite mulf_eq0 (negbTE z0) orbF (negbTE y0) powere_pos0r (negbTE z0).
Qed.

Lemma powere_pos_gt0_inv (x : \bar R) (r : R) : (0 < r)%R -> 0 <= x ->
  0 < x `^ r -> 0 < x.
Proof.
move=> r0; move: x => [x|//|]; rewrite ?leeNe_eq// lee_fin !lte_fin => x0.
exact: power_pos_gt0_inv.
Qed.

End powere_pos.

Reserved Notation "''N_' p [ f ]" (format "''N_' p [ f ]", at level 5).

Section L_norm.
Context d (T : measurableType d) (R : realType)
  (mu : {measure set T -> \bar R}).
Local Open Scope ereal_scope.

Definition L_norm (p : R) (f : T -> R) : \bar R :=
  (\int[mu]_x (`|f x| `^ p)%:E) `^ p^-1.

Local Notation "''N_' p [ f ]" := (L_norm p f).

Lemma L_norm_ge0 (p : R) (f : T -> R) : (0 <= 'N_p[f])%E.
Proof. by rewrite /L_norm powere_pos_ge0. Qed.

Lemma eq_L_norm (p : R) (f g : T -> R) : f =1 g -> 'N_p [f] = 'N_p [g].
Proof. by move=> fg; congr L_norm; exact/funext. Qed.

End L_norm.
#[global]
Hint Extern 0 (0 <= L_norm _ _ _)%E => solve [apply: L_norm_ge0] : core.

Section Rintegral.
Context d (T : measurableType d) (R : realType).
Variable mu : {finite_measure set T -> \bar R}.
Implicit Types (f : T -> R) (D : set T).

Lemma eq_Rintegral D g f : {in D, f =1 g} ->
  (\int[mu]_(x in D) f x)%R = (\int[mu]_(x in D) g x)%R.
Proof.
move=> fg; rewrite /Rintegral; congr fine.
by apply:eq_integral => x Dx; congr EFin; exact: fg.
Qed.

End Rintegral.

Section PR_measure.
Context d (T : measurableType d) (R : realType).
Variable mu : {finite_measure set T -> \bar R}.

Lemma measurable_mulrr D (k : R) : measurable_fun D (fun x : R => x * k)%R.
Proof.
apply: measurable_funTS => /=.
by apply: continuous_measurable_fun; exact: mulrr_continuous.
Qed.

End PR_measure.

Section Hoelder.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Local Open Scope ereal_scope.

Local Notation "''N_' p [ f ]" := (L_norm mu p f).

Let measurableT_comp_power_pos (f : T -> R) p :
  measurable_fun setT f -> measurable_fun setT (fun x => f x `^ p)%R.
Proof. exact: (@measurableT_comp _ _ _ _ _ _ (@power_pos R ^~ p)). Qed.

Let integrable_power_pos (f : T -> R) p : (0 < p)%R ->
  measurable_fun setT f -> 'N_p[f] != +oo ->
  mu.-integrable [set: T] (fun x => (`|f x| `^ p)%:E).
Proof.
move=> p0 mf foo; split.
  apply: measurableT_comp => //; apply: measurableT_comp_power_pos.
  exact: measurableT_comp.
move/powere_pos_lty' : foo; rewrite invr_gt0// => /(_ p0) foo.
rewrite ltey.
by under eq_integral => x _ do rewrite gee0_abs // ?lee_fin ?power_pos_ge0//.
Qed.

Let hoelder0 (f g : T -> R) (p q : R) :
  measurable_fun setT f -> measurable_fun setT g ->
  (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
  'N_p[f] = 0 ->
  'N_1 [(f \* g)%R] <= 'N_p [f] * 'N_q [g].
Proof.
move=> mf mg p0 q0 pq f0; rewrite f0 mul0e.
suff: 'N_1 [(f \* g)%R] = 0%E by move=> ->.
move: f0; rewrite /L_norm; move/powere_pos_eq0.
rewrite /= invr1 powere_pose1// => [fp|]; last first.
  by apply: integral_ge0 => x _; rewrite lee_fin; apply: power_pos_ge0.
have {fp}f0 : ae_eq mu setT (fun x => (`|f x| `^ p)%:E) (cst 0).
  apply/ae_eq_integral_abs => //=.
  - apply: measurableT_comp => //; apply: measurableT_comp_power_pos.
    exact: measurableT_comp.
  - under eq_integral => x _ do rewrite ger0_norm ?power_pos_ge0//.
    apply: fp; rewrite (lt_le_trans _ (integral_ge0 _ _))// => x _.
    exact: power_pos_ge0.
rewrite (ae_eq_integral (cst 0)%E) => [|//||//|].
- by rewrite integral0.
- apply: measurableT_comp => //; apply: measurableT_comp_power_pos => //.
  by apply: measurableT_comp => //; exact: measurable_funM.
- apply: filterS f0 => x /(_ I) /= [] /power_pos_eq0 fp0 _.
  by rewrite power_posr1// normrM fp0 mul0r.
Qed.

Let normed p f x := `|f x| / fine 'N_p[f].

Let normed_ge0 p f x : (0 <= normed p f x)%R.
Proof. by rewrite /normed divr_ge0// fine_ge0// L_norm_ge0. Qed.

Let measurable_normed p f : measurable_fun setT f ->
  measurable_fun setT (normed p f).
Proof.
move=> mf; rewrite (_ : normed _ _ = *%R (fine 'N_p[f])^-1 \o normr \o f).
  by apply: measurableT_comp => //; exact: measurableT_comp.
by apply/funext => x /=; rewrite mulrC.
Qed.

Let normed_expR p f x : (0 < p)%R ->
  let F := normed p f in F x != 0%R -> expR (ln (F x `^ p) / p) = F x.
Proof.
move=> p0 F Fx0.
rewrite ln_power_pos// mulrAC divff// ?gt_eqF// mul1r.
by rewrite lnK// posrE lt_neqAle normed_ge0 eq_sym Fx0.
Qed.

Let integral_normed f p : (0 < p)%R -> 0 < 'N_p[f] ->
  mu.-integrable [set: T] (fun x => (`|f x| `^ p)%:E) ->
  \int[mu]_x (normed p f x `^ p)%:E = 1.
Proof.
move=> p0 fpos ifp.
transitivity (\int[mu]_x (`|f x| `^ p / fine 'N_p[f] `^ p)%:E).
  apply: eq_integral => t _.
  rewrite power_posM //; last by rewrite invr_ge0 fine_ge0 // L_norm_ge0.
  rewrite -power_pos_inv1; last by rewrite fine_ge0 // L_norm_ge0.
  by rewrite power_posAC -power_pos_inv1 // power_pos_ge0.
transitivity (\int[mu]_x (`|f x| `^ p / fine ('N_p[f] `^ p))%:E).
  by rewrite fine_powere_pos.
rewrite /L_norm -powere_posMD mulVf ?lt0r_neq0 //.
rewrite powere_pose1; last first.
  by apply integral_ge0 => x _; rewrite lee_fin; exact: power_pos_ge0.
under eq_integral do rewrite EFinM muleC.
rewrite integralM// fine_inv fineK; last first.
  rewrite inve_fin_num ge0_fin_numE.
    case: ifp => _; apply: le_lt_trans; rewrite le_eqVlt.
    apply/orP; left; apply/eqP; apply: eq_integral => x _.
    by rewrite [RHS]gee0_abs// lee_fin power_pos_ge0.
  by rewrite integral_ge0// => x _; rewrite lee_fin power_pos_ge0.
rewrite muleC inveK//; last first.
  rewrite ge0_fin_numE//; last first.
    by rewrite integral_ge0// => x _; rewrite lee_fin// power_pos_ge0.
  case: ifp => _; apply: le_lt_trans; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by apply eq_integral => x _; rewrite gee0_abs// lee_fin power_pos_ge0.
rewrite gt_eqF//.
apply: powere_pos_gt0_inv fpos; rewrite ?invr_gt0//.
by apply integral_ge0 => t _; rewrite lee_fin power_pos_ge0.
Qed.

(* ref http://pi.math.cornell.edu/~erin/analysis/lectures.pdf *)
Lemma hoelder (f g : T -> R) (p q : R) :
  measurable_fun setT f -> measurable_fun setT g ->
  (0 < p)%R -> (0 < q)%R -> (p^-1 + q^-1 = 1)%R ->
 'N_1 [(f \* g)%R] <= 'N_p [f] * 'N_q [g].
Proof.
move=> mf mg p0 q0 pq.
have [f0|f0] := eqVneq 'N_p[f] 0%E; first exact: hoelder0.
have [g0|g0] := eqVneq 'N_q[g] 0%E.
  rewrite muleC; apply: le_trans; last by apply: hoelder0 => //; rewrite addrC.
  by under eq_L_norm do rewrite /= mulrC.
have {f0}fpos : 0 < 'N_p[f] by rewrite lt_neqAle eq_sym f0//= L_norm_ge0.
have {g0}gpos : 0 < 'N_q[g] by rewrite lt_neqAle eq_sym g0//= L_norm_ge0.
have [foo|foo] := eqVneq 'N_p[f] +oo%E; first by rewrite foo gt0_mulye ?leey.
have [goo|goo] := eqVneq 'N_q[g] +oo%E; first by rewrite goo gt0_muley ?leey.
pose F := normed p f.
pose G := normed q g.
have exp_convex x : (F x * G x <= F x `^ p / p + G x `^ q / q)%R.
  have [Fx0|Fx0] := eqVneq (F x) 0%R.
    by rewrite Fx0 mul0r power_pos0 gt_eqF// mul0r add0r divr_ge0 ?power_pos_ge0 ?ltW.
  have {}Fx0 : (0 < F x)%R.
    by rewrite lt_neqAle eq_sym Fx0 divr_ge0// fine_ge0// L_norm_ge0.
  have [Gx0|Gx0] := eqVneq (G x) 0%R.
    by rewrite Gx0 mulr0 power_pos0 gt_eqF// mul0r addr0 divr_ge0 ?power_pos_ge0 ?ltW.
  have {}Gx0 : (0 < G x)%R.
    by rewrite lt_neqAle eq_sym Gx0/= divr_ge0// fine_ge0// L_norm_ge0.
  pose s x := ln ((F x) `^ p).
  pose t x := ln ((G x) `^ q).
  have : (expR (p^-1 * s x + q^-1 * t x) <= p^-1 * expR (s x) + q^-1 * expR (t x))%R.
    have -> : (p^-1 = 1 - q^-1)%R by rewrite -pq addrK.
    have K : (q^-1 \in `[0, 1])%R.
      by rewrite in_itv/= invr_ge0 (ltW q0)/= -pq ler_paddl// invr_ge0 ltW.
    exact: (convex_expR (@Itv.mk _ `[0, 1] q^-1 K)%R).
  rewrite expRD (mulrC _ (s x)) normed_expR ?gt_eqF// -/(F x).
  rewrite (mulrC _ (t x)) normed_expR ?gt_eqF// -/(G x) => /le_trans; apply.
  rewrite /s /t [X in (_ * X + _)%R](@lnK _ (F x `^ p)%R); last first.
    by rewrite posrE power_pos_gt0.
  rewrite (@lnK _ (G x `^ q)%R); last by rewrite posrE power_pos_gt0.
  by rewrite mulrC (mulrC _ q^-1).
have -> : 'N_1[(f \* g)%R] = 'N_1[(F \* G)%R] * 'N_p[f] * 'N_q[g].
  rewrite {1}/L_norm; under eq_integral => x _ do rewrite power_posr1 //.
  rewrite invr1 powere_pose1; last by apply: integral_ge0 => x _; rewrite lee_fin.
  rewrite {1}/L_norm.
  under [in RHS]eq_integral.
    move=> x _.
    rewrite /F /G /= /normed (mulrC `|f x|)%R mulrA -(mulrA (_^-1)) (mulrC (_^-1)) -mulrA.
    rewrite ger0_norm; last first.
      by rewrite mulr_ge0// divr_ge0 ?(fine_ge0,L_norm_ge0,invr_ge0).
    rewrite power_posr1; last first.
      by rewrite mulr_ge0// divr_ge0 ?(fine_ge0,L_norm_ge0,invr_ge0).
    rewrite mulrC -normrM EFinM.
    over.
  rewrite /=.
  rewrite ge0_integralM//; last 2 first.
    - apply: measurableT_comp => //; apply: measurableT_comp => //.
      exact: measurable_funM.
    - by rewrite lee_fin mulr_ge0// invr_ge0 fine_ge0// L_norm_ge0.
  rewrite -muleA muleC invr1 powere_pose1; last first.
    rewrite mule_ge0//.
      by rewrite lee_fin mulr_ge0// invr_ge0 fine_ge0// L_norm_ge0.
    by apply integral_ge0 => x _; rewrite lee_fin.
  rewrite muleA EFinM !fine_inv.
  rewrite fineK ?inve_fin_num ?ge0_fin_numE ?L_norm_ge0 ?ltey//.
  rewrite fineK ?inve_fin_num ?ge0_fin_numE ?L_norm_ge0 ?ltey//.
  rewrite inveM ?gt_eqF// inveK ?mul1e ?mule_neq0// ?gt_eqF//.
  by rewrite fin_numM// ge0_fin_numE ?L_norm_ge0// ltey.
rewrite -(mul1e ('N_p[f] * _)) -muleA lee_pmul ?mule_ge0 ?L_norm_ge0//.
apply: (@le_trans _ _ (\int[mu]_x (F x `^ p / p + G x `^ q / q)%:E)).
  rewrite /L_norm invr1 powere_pose1; last first.
    by apply integral_ge0 => x _; rewrite lee_fin; exact: power_pos_ge0.
  apply: ae_ge0_le_integral => //.
  - by move=> x _; exact: power_pos_ge0.
  - apply: measurableT_comp => //; apply: measurableT_comp_power_pos => //.
    apply: measurableT_comp => //.
    by apply: measurable_funM => //; exact: measurable_normed.
  - by move=> x _; rewrite lee_fin addr_ge0// divr_ge0// ?power_pos_ge0// ltW.
  - apply: measurableT_comp => //; apply: measurable_funD => //; apply: measurable_funM => //;
    by apply: measurableT_comp_power_pos => //; exact: measurable_normed.
  apply/aeW => x _.
  by rewrite lee_fin power_posr1// ger0_norm ?exp_convex// mulr_ge0// normed_ge0.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
under eq_integral.
  by move=> x _; rewrite EFinD mulrC (mulrC _ (_^-1)); over.
rewrite ge0_integralD//; last 4 first.
- by move=> x _; rewrite lee_fin mulr_ge0// ?invr_ge0 ?power_pos_ge0// ltW.
- apply: measurableT_comp => //; apply: measurableT_comp => //.
  by apply: measurableT_comp_power_pos => //; exact: measurable_normed.
- by move=> x _; rewrite lee_fin mulr_ge0// ?invr_ge0 ?power_pos_ge0// ltW.
- apply: measurableT_comp => //; apply: measurableT_comp => //.
  by apply: measurableT_comp_power_pos => //; exact: measurable_normed.
under eq_integral do rewrite EFinM.
rewrite {1}ge0_integralM//; last 3 first.
- apply: measurableT_comp => //.
  by apply: measurableT_comp_power_pos => //; exact: measurable_normed.
- by move=> x _; rewrite lee_fin power_pos_ge0.
- by rewrite lee_fin invr_ge0 ltW.
under [X in (_ + X)%E]eq_integral => x _ do rewrite EFinM.
rewrite ge0_integralM//; last 3 first.
- apply: measurableT_comp => //.
  by apply: measurableT_comp_power_pos => //; exact: measurable_normed.
- by move=> x _; rewrite lee_fin power_pos_ge0.
- by rewrite lee_fin invr_ge0 ltW.
rewrite integral_normed//; last exact: integrable_power_pos.
rewrite integral_normed//; last exact: integrable_power_pos.
by rewrite 2!mule1 -EFinD pq.
Qed.

Lemma inve_powere_pos x (p : R) : 0 <= x -> (0 < p)%R -> inve (x `^ p) = x `^ -p.
Proof.
rewrite le_eqVlt => /orP[/eqP <- p0|].
  by rewrite !powere_pos0r oppr_eq0 gt_eqF//= /inve/= invr0.
case: x => // [x|_ p0].
  rewrite lte_fin => x0 p0.
  rewrite /powere_pos/= /inve/=.
  by rewrite /power_pos gt_eqF// mulNr expRN.
by rewrite /inve/= gt_eqF// oppr_eq0 gt_eqF.
Qed.

Lemma oneminvp (p : R) : (1 < p)%R ->  (1 - p^-1 = (p / (p - 1))^-1)%R.
Proof.
move=> p1.
by rewrite invf_div mulrDl divff ?gt_eqF// ?(le_lt_trans _ p1)// mulN1r.
Qed.

Lemma power_posD (a x y : R) : (0 < a)%R -> (a `^ (x + y) = a `^ x * a `^ y)%R.
Proof. by move=> a0; rewrite /power_pos gt_eqF// mulrDl expRD. Qed.

Lemma powere_posD (a : \bar R) (x y : R) : 0 < a -> (0 <= x)%R -> (0 <= y)%R ->
  a `^ (x + y) = a `^ x * a `^ y.
Proof.
move=> a0 x_ge0 y_ge0; move: a0.
case: a => [a|_/=|//].
  by rewrite lte_fin/= => a0; rewrite -EFinM power_posD.
have [->|x0] := eqVneq x 0%R; first by rewrite mul1e add0r.
have [->|y0] := eqVneq y 0%R; first by rewrite addr0 (negbTE x0) mule1.
by rewrite paddr_eq0// (negbTE x0) (negbTE y0) mulyy.
Qed.

Lemma powere_posB (a : \bar R) (x y : R) : 0 <= a -> x != y ->
  a `^ (x - y) = a `^ x * a `^ -y.
Proof.
move=> a0 xy.
have [->|x0] := eqVneq x 0%R.
  by rewrite powere_pose0 sub0r mul1e.
have [->|y0] := eqVneq y 0%R.
  by rewrite subr0 oppr0 powere_pose0 mule1.
move: a0; case: a => [a|_/=|//].
  rewrite lee_fin le_eqVlt => /orP[/eqP <-|a0].
    by rewrite !powere_pos0r oppr_eq0 subr_eq0 (negbTE xy) (negbTE x0) (negbTE y0) mule0.
  by rewrite /powere_pos /power_pos gt_eqF// mulrBl expRD mulNr.
by rewrite oppr_eq0 (negbTE y0) (negbTE x0) subr_eq0 (negbTE xy) mulyy.
Qed.

Lemma L_normK (p : R) (f : T -> R) : (1 < p)%R ->
  'N_p / (p - 1)[((power_pos (R:=R))^~ (p - 1)%R \o normr) \o f] =
  'N_p[f] `^ p * inve 'N_p[f].
Proof.
move=> p1.
rewrite /L_norm/=.
rewrite -powere_posMD mulVf ?gt_eqF// ?(lt_trans _ p1)// powere_pose1; last first.
  by rewrite integral_ge0// => x _; rewrite lee_fin power_pos_ge0.
under eq_integral.
  move=> x _; rewrite ger0_norm ?power_pos_ge0// -power_posMD.
  rewrite mulrCA divff// ?gt_eqF // ?subr_gt0// mulr1.
  over.
rewrite /=.
rewrite /= inve_powere_pos//; last 2 first.
  by rewrite integral_ge0// => x _; rewrite lee_fin power_pos_ge0.
  by rewrite invr_gt0 (lt_trans _ p1).
rewrite -oneminvp// powere_posB//; last 2 first.
  by rewrite integral_ge0// => x _; rewrite lee_fin power_pos_ge0.
  by rewrite gt_eqF// invf_lt1// (lt_trans _ p1).
rewrite powere_pose1// integral_ge0// => x _.
by rewrite lee_fin power_pos_ge0.
Qed.

Lemma minkowski (f g : T -> R) (p : R) :
  measurable_fun setT f -> measurable_fun setT g ->
  (1 < p)%R ->
  'N_p [(f \+ g)%R] <= 'N_p [f] + 'N_p [g].
Proof.
move=> mf mg p1.
have : 'N_p [(f \+ g)%R] `^ p <=
    ('N_p [f] + 'N_p [g]) * 'N_p [(f \+ g)%R] `^ p * inve 'N_p [(f \+ g)%R].
  rewrite [leLHS](_ : _ = \int[mu]_x (`| f x + g x | `^ p)%:E); last first.
    rewrite /L_norm -powere_posMD mulVf; last by rewrite gt_eqF// (le_lt_trans _ p1).
    by rewrite powere_pose1 ?integral_ge0// => x _; rewrite lee_fin// power_pos_ge0.
  rewrite [leLHS](_ : _ = \int[mu]_x (`|f x + g x| * `|f x + g x| `^ (p - 1))%:E); last first.
    apply: eq_integral => x _; congr EFin.
    have [->|fxgx0]:= eqVneq `|f x + g x|%R 0%R.
      by rewrite mul0r power_pos0 gt_eqF// (lt_trans _ p1).
    rewrite -[X in (X * _)%R]power_posr1//.
    rewrite -power_posD; last by rewrite lt_neqAle eq_sym fxgx0/=.
    by rewrite addrCA subrr addr0.
  apply: (@le_trans _ _ (\int[mu]_x ((`|f x| + `|g x|) * `|f x + g x| `^ (p - 1))%:E)).
    apply: ge0_le_integral => //.
    - by move=> x _; rewrite lee_fin mulr_ge0// power_pos_ge0.
    - apply: measurableT_comp => //; apply: measurable_funM.
        by apply: measurableT_comp => //; exact: measurable_funD.
      apply: measurableT_comp_power_pos.
      by apply: measurableT_comp => //; exact: measurable_funD.
    - by move=> x _; rewrite lee_fin mulr_ge0// power_pos_ge0.
    - apply: measurableT_comp => //; apply: measurable_funM.
        by apply: measurable_funD => //; exact: measurableT_comp.
      apply: measurableT_comp_power_pos.
      by apply: measurableT_comp => //; exact: measurable_funD.
    - by move=> x _; rewrite lee_fin ler_wpmul2r// ?power_pos_ge0// ler_normD.
  under eq_integral=> x _ do rewrite mulrDl EFinD.
  rewrite ge0_integralD//; last 4 first.
    - by move=> x _; rewrite lee_fin mulr_ge0// power_pos_ge0.
    - apply: measurableT_comp => //; apply: measurable_funM.
        exact: measurableT_comp.
      apply: measurableT_comp_power_pos.
      by apply: measurableT_comp => //; exact: measurable_funD.
    - by move=> x _; rewrite lee_fin mulr_ge0// power_pos_ge0.
    - apply: measurableT_comp => //; apply: measurable_funM.
        exact: measurableT_comp.
      apply: measurableT_comp_power_pos.
      by apply: measurableT_comp => //; exact: measurable_funD.
  apply: (@le_trans _ _ (('N_p[f] + 'N_p[g]) *
      (\int[mu]_x (`|f x + g x| `^ (p - 1) `^ (p / (p - 1)))%:E) `^ (1 - p^-1))).
    rewrite muleDl; last 2 first.
      admit.
      by rewrite ge0_adde_def//= inE L_norm_ge0.
    rewrite lee_add//.
    - apply: (@le_trans _ _ ('N_1 [(f \* (@power_pos R ^~ (p - 1) \o normr \o (f \+ g)))%R])).
        rewrite /L_norm invr1 [leRHS]powere_pose1/=; last first.
          by apply: integral_ge0 => x _; rewrite lee_fin power_posr1.
        apply: ge0_le_integral => //.
        - by move=> x _; rewrite lee_fin mulr_ge0// power_pos_ge0.
        - apply: measurableT_comp => //; apply: measurable_funM.
            exact: measurableT_comp.
          apply: measurableT_comp_power_pos.
          by apply: measurableT_comp => //; exact: measurable_funD.
        - by move=> x _; rewrite lee_fin power_posr1.
        - apply: measurableT_comp => //; apply: measurableT_comp_power_pos.
          apply: measurableT_comp => //; apply: measurable_funM => //.
          apply: measurableT_comp_power_pos.
          by apply: measurableT_comp => //; exact: measurable_funD.
        - move=> x _.
          rewrite lee_fin power_posr1// normrM.
          by rewrite ler_wpmul2l// [leRHS]ger0_norm// power_pos_ge0.
      apply: le_trans.
        apply: (@hoelder _ _ p (p / (p - 1))) => //.
        - apply: measurableT_comp => //.
            exact: measurableT_comp.
          exact: measurable_funD.
        - by rewrite (lt_trans _ p1).
        - by rewrite divr_gt0// ?subr_gt0// (lt_trans _ p1).
        - by rewrite -oneminvp// addrCA subrr addr0.
      rewrite lee_wpmul2l; [by []|by rewrite L_norm_ge0 |].
      rewrite le_eqVlt; apply/orP; left; apply/eqP.
      rewrite /L_norm/= -(oneminvp p1).
      congr (_ `^ (1 - p^-1)).
      apply: eq_integral => x _.
      by rewrite ger0_norm// power_pos_ge0.
    - admit.
  rewrite -muleA.
  rewrite lee_wpmul2l// ?adde_ge0 ?L_norm_ge0//.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  rewrite (oneminvp p1).
  transitivity ('N_(p/(p -1)) [(@power_pos R ^~ (p - 1)%R \o normr \o (f \+ g)%R)]).
    rewrite /L_norm/= -(oneminvp p1).
    congr (_ `^ (1 - p^-1)).
    apply: eq_integral => x _.
    by rewrite [in RHS]ger0_norm// power_pos_ge0.
  by rewrite /= L_normK.
rewrite muleAC.
Admitted.

End Hoelder.

Definition random_variable d (T : measurableType d) (R : realType)
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
  rewrite power_pos_mulrn// real_normK //; apply num_real.
  apply integral_ge0 => x _; rewrite lee_fin; apply power_pos_ge0.
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
apply: (filterS _ x20) => x /=.
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
    measurable_fun [set: R] f -> (forall r, 0 <= f r)%R ->
    {in `[0, +oo[%classic &, {homo f : x y / x <= y}}%R ->
  (f eps)%:E * P [set x | eps%:E <= `| (X x)%:E | ] <=
    'E_P[f \o (fun x => `| x |%R) \o X].
Proof.
move=> e0 mf f0 f_nd; rewrite -(setTI [set _ | _]).
apply: (le_trans (@le_integral_comp_abse d T R P setT measurableT (EFin \o X)
  eps (er_map f) _ _ _ _ e0)) => //=.
- exact: measurable_er_map.
- by case => //= r _; exact: f0.
- by move=> [x| |] [y| |] xP yP xy//=; rewrite ?leey ?leNye// lee_fin f_nd.
- exact/EFin_measurable_fun.
Qed.

Lemma chebyshev (X : {RV P >-> R}) (eps : R) : (0 < eps)%R ->
  P [set x | (eps <= `| X x - fine ('E_P[X])|)%R ] <= (eps ^- 2)%:E * 'V_P[X].
Proof.
move => heps; have [->|hv] := eqVneq 'V_P[X] +oo.
  by rewrite mulr_infty gtr0_sg ?mul1e// ?leey// invr_gt0// exprn_gt0.
have h (Y : {RV P >-> R}) :
    P [set x | (eps <= `|Y x|)%R] <= (eps ^- 2)%:E * 'E_P[Y ^+ 2].
  rewrite -lee_pdivr_mull; last by rewrite invr_gt0// exprn_gt0.
  rewrite exprnN expfV exprz_inv opprK -exprnP.
  apply: (@le_trans _ _ ('E_P[(@GRing.exp R ^~ 2%N \o normr) \o Y])).
    apply: (@markov Y (@GRing.exp R ^~ 2%N)) => //.
    - by move=> r; apply: sqr_ge0.
    - move=> x y; rewrite !inE !mksetE !in_itv/= !andbT => x0 y0.
      by rewrite ler_sqr.
  apply: expectation_le => //.
    - by apply: measurableT_comp => //; exact: measurableT_comp.
  - by move=> x /=; apply: sqr_ge0.
  - by move=> x /=; apply: sqr_ge0.
  - by apply/aeW => t /=; rewrite real_normK// num_real.
have := h [the {mfun T >-> R} of (X \- cst (fine ('E_P[X])))%R].
by move=> /le_trans; apply; rewrite /variance.
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
have hoeld := @hoelder d T R P X Y 2 2 _ _ mf mg twoone.
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
