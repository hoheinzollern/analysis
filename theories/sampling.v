(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From HB Require Import structures.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import reals ereal interval_inference topology normedtype sequences.
From mathcomp Require Import realfun convex.
From mathcomp Require Import derive esum measure exp numfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral kernel probability.

Reserved Notation "' P [ A | B ]".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

From mathcomp Require Import real_interval.

Section bool_to_real.
Context d (T : measurableType d) (R : realType) (P : probability T R) (f : {mfun T >-> bool}).
Definition bool_to_real : T -> R := (fun x => x%:R) \o (f : T -> bool).

Lemma measurable_bool_to_real : measurable_fun [set: T] bool_to_real.
Proof.
rewrite /bool_to_real.
apply: measurableT_comp => //=.
have := @measurable_funP _ _ _ _ setT f.
exact.
Qed.
HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ bool_to_real measurable_bool_to_real.

Definition btr : {RV P >-> R} := bool_to_real.

End bool_to_real.

Section move.

Lemma sumr_map {R : realType} U d (T : measurableType d) (l : seq U) Q
    (f : U -> {mfun T >-> R}) (x : T) :
  (\sum_(i <- l | Q i) f i) x = \sum_(i <- l | Q i) f i x.
Proof. by elim/big_ind2 : _ => //= _ g _ h <- <-. Qed.

Lemma prodr_map {R : realType} U d (T : measurableType d) (l : seq U) Q
    (f : U -> {mfun T >-> R}) (x : T) :
  (\prod_(i <- l | Q i) f i) x = \prod_(i <- l | Q i) f i x.
Proof. by elim/big_ind2 : _ => //= _ h _ g <- <-. Qed.

Definition sumrfct {R : realType} d {T : measurableType d} (s : seq {mfun T >-> R}) : T -> R :=
  fun x => \sum_(f <- s) f x.

Lemma measurable_sumrfct {R : realType} d {T : measurableType d} (s : seq {mfun T >-> R}) :
  measurable_fun setT (sumrfct s).
Proof.
apply/measurable_EFinP => /=; apply/measurableT_comp => //.
exact: measurable_sum.
Qed.

HB.instance Definition _ {R : realType} d {T : measurableType d} (s : seq {mfun T >-> R}) :=
  isMeasurableFun.Build _ _ _ _ (sumrfct s) (measurable_sumrfct s).

Lemma sum_mfunE {R : realType} d {T : measurableType d} (s : seq {mfun T >-> R}) x :
  ((\sum_(f <- s) f) x = sumrfct s x)%R.
Proof. by rewrite/sumrfct; elim/big_ind2 : _ => //= u a v b <- <-. Qed.


End move.

Definition measure_tuple_display : measure_display -> measure_display.
Proof. exact. Qed.

Definition g_sigma_preimage d (rT : semiRingOfSetsType d) (aT : Type)
    (n : nat) (f : 'I_n -> aT -> rT) : set (set aT) :=
  <<s \big[setU/set0]_(i < n) preimage_set_system setT (f i) measurable >>.

HB.instance Definition _ (n : nat) (T : pointedType) :=
  isPointed.Build (n.-tuple T) (nseq n point).

Definition mtuple (n : nat) d (T : measurableType d) : Type := n.-tuple T.

HB.instance Definition _ (n : nat) d (T : measurableType d) := Pointed.on (mtuple n T).

Lemma countable_range_bool d (T : measurableType d) (b : bool) :
  countable (range (@cst T _ b)).
Proof. exact: countableP. Qed.

HB.instance Definition _ d (T : measurableType d) b :=
  MeasurableFun_isDiscrete.Build d _ T _  (cst b) (countable_range_bool T b).

Section measurable_tuple.
Context {d} {T : measurableType d}.
Variable n : nat.

Let coors := (fun i x => @tnth n T x i).

Let tuple_set0 : g_sigma_preimage coors set0.
Proof. exact: sigma_algebra0. Qed.

Let tuple_setC A : g_sigma_preimage coors A -> g_sigma_preimage coors (~` A).
Proof. exact: sigma_algebraC. Qed.

Let tuple_bigcup (F : _^nat) :
  (forall i, g_sigma_preimage coors (F i)) ->
  g_sigma_preimage coors (\bigcup_i (F i)).
Proof. exact: sigma_algebra_bigcup. Qed.

HB.instance Definition _ :=
  @isMeasurable.Build (measure_tuple_display d)
    (mtuple n T) (g_sigma_preimage coors)
    (tuple_set0) (tuple_setC) (tuple_bigcup).

End measurable_tuple.

Definition cylinder d {T : measurableType d} m (A : set (m.-tuple T))
    (J : {fset 'I_m}%fset) : set (m.-tuple T) :=
  \big[setI/setT]_(i <- J) (@tnth _ T ^~ i) @^-1`
                           ((@tnth _ T ^~ i) @` A).

Definition Z d {T : measurableType d} m
    (J : {fset 'I_m}%fset) : set_system (m.-tuple T) :=
  [set B | exists A, B = cylinder A J].

Section pro.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Fixpoint mpro (n : nat) : set (mtuple n T) -> \bar R :=
  match n with
  | 0%N => \d_([::] : mtuple 0 T)
  | m.+1 => fun A => (P \x^ @mpro m)%E [set (thead x, [tuple of behead x]) | x in A]
  end.

Lemma mpro_measure n : @mpro n set0 = 0 /\ (forall A, (0 <= @mpro n A)%E) /\ semi_sigma_additive (@mpro n).
Proof.
elim: n => //= [|n ih]; first by repeat split => //; exact: measure_semi_sigma_additive.
pose build_Mpro := isMeasure.Build _ _ _ (@mpro n) ih.1 ih.2.1 ih.2.2.
pose Mpro : measure _ R := HB.pack (@mpro n) build_Mpro.
pose ppro : measure _ R := (P \x^ Mpro)%E.
split.
  rewrite image_set0 /product_measure2/=.
  under eq_fun => x do rewrite ysection0 measure0 (_ : 0 = cst 0 x)//.
  rewrite (_ : @mpro n = Mpro)//.
  by rewrite integral_cst// mul0e.
split.
  by move => A; rewrite (_ : @mpro n = Mpro).
rewrite (_ : @mpro n = Mpro)// (_ : (P \x^ Mpro)%E = ppro)//.
move=> F mF dF mUF.
rewrite image_bigcup.
apply: measure_semi_sigma_additive.
- move=> i.
  admit.
- apply/trivIsetP => i j _ _ ineqj.
  have := dF.
  move/trivIsetP/(_ i j Logic.I Logic.I ineqj).
  admit.
apply: bigcup_measurable => j _.
admit.
Admitted.

HB.instance Definition _ n :=
  isMeasure.Build _ _ _ (@mpro n) (@mpro_measure n).1 (@mpro_measure n).2.1 (@mpro_measure n).2.2.

Lemma mpro_setT n : @mpro n setT = 1%E.
Proof.
elim: n => //=; first by rewrite diracT.
move=> n ih.
rewrite /product_measure2/ysection/=.
under eq_fun => x.
  rewrite [X in P X](_ : _ = [set: T]); last first.
    under eq_fun => y. rewrite [X in _ \in X](_ : _ = setT); last first.
      apply: funext=> z/=.
      apply: propT.
      exists (z.1 :: z.2) => //=.
      case: z => z1 z2/=.
      congr pair.
      exact/val_inj.
      over.
    by apply: funext => y/=; rewrite in_setT trueE.
  rewrite probability_setT.
  over.
by rewrite integral_cst// mul1e.
Qed.

HB.instance Definition _ n :=
  Measure_isProbability.Build _ _ _ (@mpro n) (@mpro_setT n).

Definition pro (n : nat) : probability (mtuple n T) R := @mpro n.

End pro.
Arguments pro {d T R} P n.

Section bernoulli.

Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Variable p : R.
Hypothesis p01 : (0 <= p <= 1)%R.

Definition bernoulli_RV (X : {RV P >-> bool}) :=
  distribution P X = bernoulli p.

Lemma bernoulli_RV1 (X : {RV P >-> bool}) : bernoulli_RV X ->
  P [set i | X i == 1%R] = p%:E.
Proof.
move=> [[/(congr1 (fun f => f [set 1%:R]))]].
rewrite bernoulliE//.
rewrite /mscale/=.
rewrite diracE/= mem_set// mule1// diracE/= memNset//.
rewrite mule0 adde0.
rewrite /distribution /= => <-.
congr (P _).
rewrite /preimage/=.
by apply/seteqP; split => [x /eqP H//|x /eqP].
Qed.

Lemma bernoulli_RV2 (X : {RV P >-> bool}) : bernoulli_RV X ->
  P [set i | X i == 0%R] = (`1-p)%:E.
Proof.
move=> [[/(congr1 (fun f => f [set 0%:R]))]].
rewrite bernoulliE//.
rewrite /mscale/=.
rewrite diracE/= memNset//.
rewrite mule0// diracE/= mem_set// add0e mule1.
rewrite /distribution /= => <-.
congr (P _).
rewrite /preimage/=.
by apply/seteqP; split => [x /eqP H//|x /eqP].
Qed.

Lemma bernoulli_expectation (X : {RV P >-> bool}) :
  bernoulli_RV X -> 'E_P[btr P X] = p%:E.
Proof.
move=> bX.
rewrite unlock /btr.
rewrite -(@ge0_integral_distribution _ _ _ _ _ _ X (EFin \o [eta GRing.natmul 1]))//; last first.
  by move=> y //=.
rewrite /bernoulli/=.
rewrite (@eq_measure_integral _ _ _ _ (bernoulli p)); last first.
  by move=> A mA _/=; rewrite (_ : distribution P X = bernoulli p).
rewrite integral_bernoulli//=.
by rewrite -!EFinM -EFinD mulr0 addr0 mulr1.
Qed.

Lemma integrable_bernoulli (X : {RV P >-> bool}) :
  bernoulli_RV X -> P.-integrable [set: T] (EFin \o btr P X).
Proof.
move=> bX.
apply/integrableP; split; first by apply: measurableT_comp => //; exact: measurable_bool_to_real.
have -> : \int[P]_x `|(EFin \o btr P X) x| = 'E_P[btr P X].
  rewrite unlock /expectation.
  apply: eq_integral => x _.
  by rewrite gee0_abs //= lee_fin.
by rewrite bernoulli_expectation// ltry.
Qed.

Lemma bool_RV_sqr (X : {dRV P >-> bool}) :
  ((btr P X ^+ 2) = btr P X :> (T -> R))%R.
Proof.
apply: funext => x /=.
rewrite /GRing.exp /btr/bool_to_real /GRing.mul/=.
by case: (X x) => /=; rewrite ?mulr1 ?mulr0.
Qed.

Lemma bernoulli_variance (X : {dRV P >-> bool}) :
  bernoulli_RV X -> 'V_P[btr P X] = (p * (`1-p))%:E.
Proof.
move=> b.
rewrite (@varianceE _ _ _ _ (btr P X)); last admit.
rewrite [X in 'E_P[X]]bool_RV_sqr !bernoulli_expectation//.
by rewrite expe2 -EFinD onemMr.
Admitted.

Definition is_bernoulli_trial n (X : n.-tuple {RV P >-> bool}) :=
  (forall i, bernoulli_RV (tnth X i)).

Definition tuple_sum n (s : n.-tuple {mfun T >-> R}) : mtuple n T -> R :=
  (fun x => \sum_(i < n) (tnth s i) (tnth x i))%R.

Lemma measurable_tnth n (i : 'I_n) :
  measurable_fun [set: mtuple n T] (@tnth _ T ^~ i).
Proof.
move=> _ Y mY; rewrite setTI; apply: sub_sigma_algebra => /=.
rewrite -bigcup_seq/=; exists i => //=; first by rewrite mem_index_enum.
by exists Y => //; rewrite setTI.
Qed.

Lemma measurable_tuple_sum n (s : n.-tuple {mfun T >-> R}) :
  measurable_fun setT (tuple_sum s).
Proof.
apply: measurable_sum => i/=; apply/measurableT_comp => //.
exact: measurable_tnth.
Qed.

HB.instance Definition _ n (s : n.-tuple {mfun T >-> R}) :=
  isMeasurableFun.Build _ _ _ _ (tuple_sum s) (measurable_tuple_sum s).

Definition tuple_prod n (s : n.-tuple {mfun T >-> R}) : mtuple n T -> R :=
  (fun x => \prod_(i < n) (tnth s i) (tnth x i))%R.

Lemma measurable_tuple_prod n (s : n.-tuple {mfun T >-> R}) :
  measurable_fun setT (tuple_prod s).
Proof.
apply: measurable_prod => /= i _; apply/measurableT_comp => //.
exact: measurable_tnth.
Qed.

HB.instance Definition _ n (s : n.-tuple {mfun T >-> R}) :=
  isMeasurableFun.Build _ _ _ _ (tuple_prod s) (measurable_tuple_prod s).

Definition bernoulli_trial n (X : n.-tuple {RV P >-> bool}) : {RV (pro P n) >-> R} :=
  tuple_sum [the n.-tuple _ of (map (btr P)
   (map (fun t : {RV P >-> bool} => t : {mfun T >-> bool}) X))].

(*
was wrong
Definition bernoulli_trial n (X : {dRV P >-> bool}^nat) : {RV (pro n P) >-> R} :=
  (\sum_(i<n) (btr P (X i)))%R. (* TODO: add HB instance measurablefun sum*)
*)

Lemma expectation_sum_pro n (X : n.-tuple {RV P >-> R}) :
    (forall Xi, Xi \in X -> P.-integrable [set: T] (EFin \o Xi)) ->
  'E_(pro P n)[tuple_sum X] = \sum_(i < n) ('E_P[(tnth X i)]).
Proof.
move: n X.
elim => [X|n IH X] /= intX.
- rewrite /tuple_sum.
  under eq_fun do rewrite big_ord0.
  by rewrite big_ord0 expectation_cst.
pose X0 := tnth X ord0.
have intX0 : P.-integrable [set: T] (EFin \o X0).
  by apply: intX; rewrite mem_tnth.
have {}intX Xi : Xi \in X -> P.-integrable [set: T] (EFin \o Xi).
  by move=> XiX; exact: intX.
rewrite big_ord_recr/=.
rewrite /tuple_sum/=.
under eq_fun do rewrite big_ord_recr/=.
pose X1 := fun x : mtuple n.+1 T =>
                (\sum_(i < n) MeasurableFun.sort (tnth X (widen_ord (leqnSn n) i)) (tnth x (widen_ord (leqnSn n) i)))%R.
have mX1 : measurable_fun setT X1.
  apply: measurable_sum => /= i; apply: measurableT_comp => //.
  exact: measurable_tnth.
pose build_mX1 := isMeasurableFun.Build _ _ _ _ _ mX1.
pose Y1 : {mfun mtuple n.+1 T >-> R} := HB.pack X1 build_mX1.
pose X2 := fun x : mtuple n.+1 T =>
                MeasurableFun.sort (tnth X ord_max) (tnth x ord_max).
have mX2 : measurable_fun setT X2.
rewrite /X2 /=.
  by apply: measurableT_comp => //; exact: measurable_tnth.
pose build_mX2 := isMeasurableFun.Build _ _ _ _ _ mX2.
pose Y2 : {mfun mtuple n.+1 T >-> R} := HB.pack X2 build_mX2.
rewrite [X in 'E__[X]](_ : _ = Y1 \+ Y2)//.
rewrite expectationD; last 2 first.
  admit.
  admit.
congr (_ + _); last first.
- rewrite /Y1/X1/=.
  rewrite unlock /expectation.
  pose phi : mtuple n.+1 T -> T := (fun w => @tnth n.+1 T w ord_max).
  have mphi : measurable_fun setT phi.
    exact: measurable_tnth.
  admit. (* priority? *)
rewrite /Y2/X2/=.
Admitted.

Lemma expectation_bernoulli_trial n (X : n.-tuple {RV P >-> bool}) :
  is_bernoulli_trial X -> 'E_(pro P n)[bernoulli_trial X] = (n%:R * p)%:E.
Proof.
move=> bRV. rewrite /bernoulli_trial.
transitivity ('E_(pro P n)[tuple_sum (map (btr P) X)]).
  congr expectation; apply/funext => t.
  by apply: eq_bigr => /= i _; rewrite !tnth_map.
rewrite expectation_sum_pro; last first.
  move=> Xi.
  move=> /mapP[/= k kn] ->.
  have [i ki] : exists i : 'I_n, k = tnth X i.
    by apply/tnthP.
  apply: integrable_bernoulli.
  rewrite ki.
  by apply bRV.
transitivity (\sum_(i < n) p%:E).
  apply: eq_bigr => k _.
  by rewrite tnth_map bernoulli_expectation.
by rewrite sumEFin big_const_ord iter_addr addr0 mulrC mulr_natr.
Qed.

Lemma bernoulli_trial_ge0 n (X : n.-tuple {RV P >-> bool}) : is_bernoulli_trial X ->
  (forall t, 0 <= bernoulli_trial X t)%R.
Proof.
move=> bRV t.
rewrite /bernoulli_trial.
apply/sumr_ge0 => /= i _.
by rewrite !tnth_map.
Qed.

(* this seems to be provable like in https://www.cs.purdue.edu/homes/spa/courses/pg17/mu-book.pdf page 65
taylor_ln_le :
  forall (delta : R), ((1 + delta) * ln (1 + delta) >= delta + delta^+2 / 3)%R.  *)
Section taylor_ln_le.
Local Open Scope ring_scope.

Axiom expR2_lt8 : expR 2 <= 8 :> R.

Lemma taylor_ln_le (x : R) : x \in `]0, 1[ -> (1 + x) * ln (1 + x) >= x + x^+2 / 3.
Proof.
move=> x01; rewrite -subr_ge0.
pose f (x : R) := (1 + x) * ln (1 + x) - (x + x ^+ 2 / 3).
have f0 : f 0 = 0 by rewrite /f expr0n /= mul0r !addr0 ln1 mulr0 subr0.
rewrite [leRHS](_ : _ = f x) // -f0.
evar (df0 : R -> R); evar (df : R -> R).
have idf (y : R) : 0 < 1 + y -> is_derive y (1:R) f (df y).
  move=> y1.
  rewrite (_ : df y = df0 y).
    apply: is_deriveB; last exact: is_deriveD.
    apply: is_deriveM=> //.
    apply: is_derive1_comp=> //.
    exact: is_derive1_ln.
  rewrite /df0.
  rewrite deriveD// derive_cst derive_id.
  rewrite /GRing.scale /= !(mulr0,add0r,mulr1).
  rewrite divff ?lt0r_neq0// opprD addrAC addrA subrr add0r.
  instantiate (df := fun y : R => - (3^-1 * (y + y)) + ln (1 + y)).
  reflexivity.
clear df0.
have y1cc y : y \in `[0, 1] -> 0 < 1 + y.
  rewrite in_itv /= => /andP [] y0 ?.
  by have y1: 0 < 1 + y by apply: (le_lt_trans y0); rewrite ltrDr.
have y1oo y : y \in `]0, 1[ -> 0 < 1 + y by move/subset_itv_oo_cc/y1cc.
have dfge0 y : y \in `]0, 1[ -> 0 <= df y.
  move=> y01.
  have:= y01.
  rewrite /df in_itv /= => /andP [] y0 y1.
  rewrite -lerBlDl opprK add0r -mulr2n -(mulr_natl _ 2) mulrA.
  rewrite [in leLHS](_ : y = 1 + y - 1); last by rewrite addrAC subrr add0r.
  pose iy:= Itv01 (ltW y0) (ltW y1).
  have y1E: 1 + y = @convex.conv _ R^o iy 1 2.
    rewrite convRE /= /onem mulr1 (mulr_natr _ 2) mulr2n.
    by rewrite addrACA (addrC (- y)) subrr addr0.
  rewrite y1E; apply: (le_trans _ (concave_ln _ _ _))=> //.
  rewrite -y1E addrAC subrr add0r convRE ln1 mulr0 add0r /=.
  rewrite mulrC ler_pM// ?(@ltW _ _ 0)// mulrC.
  rewrite ler_pdivrMr//.
  rewrite -[leLHS]expRK -[leRHS]expRK ler_ln ?posrE ?expR_gt0//.
  rewrite expRM/= powR_mulrn ?expR_ge0// lnK ?posrE//.
  rewrite !exprS expr0 mulr1 -!natrM mulnE /=.
  by rewrite expR2_lt8.
apply: (@ger0_derive1_homo R f 0 1 true false).
- by move=> y /y1oo /idf /@ex_derive.
- by move=> y /[dup] /y1oo /idf /@derive_val ->; exact: dfge0.
- by apply: derivable_within_continuous=> y /y1cc /idf /@ex_derive.
- by rewrite bound_itvE.
- exact: subset_itv_oo_cc.
- by have:= x01; rewrite in_itv=> /andP /= [] /ltW.
Qed.

End taylor_ln_le.

Lemma expR_prod d' {U : measurableType d'} (X : seq {mfun U >-> R}) (f : {mfun U >-> R} -> R) :
  (\prod_(x <- X) expR (f x) = expR (\sum_(x <- X) f x))%R.
Proof.
elim: X => [|h t ih]; first by rewrite !big_nil expR0.
by rewrite !big_cons ih expRD.
Qed.

Lemma expR_sum U l Q (f : U -> R) : (expR (\sum_(i <- l | Q i) f i) = \prod_(i <- l | Q i) expR (f i))%R.
Proof.
elim: l; first by rewrite !big_nil expR0.
move=> a l ih.
rewrite !big_cons.
case: ifP => //= aQ.
by rewrite expRD ih.
Qed.

(* wrong lemma *)
Lemma bernoulli_trial_mmt_gen_fun n (X_ : n.-tuple {RV P >-> bool}) (t : R) :
  is_bernoulli_trial X_ ->
  let X := bernoulli_trial X_ in
  'M_X t = \prod_(i < n) 'M_(btr P (tnth X_ i)) t.
Proof.
move=> bRVX /=.
rewrite /bernoulli_trial/mmt_gen_fun.
pose mmtX : n.-tuple {mfun T >-> R} := map (fun X => mmt_gen_fun0 X t)
  (map (btr P)  X_).
(*pose mmtX (i : 'I_n) : {RV P >-> R} := expR \o t \o* (btr P (tnth X_ i)).*)
Admitted.

Arguments sub_countable [T U].
Arguments card_le_finite [T U].

Lemma bernoulli_mmt_gen_fun (X : {RV P >-> bool}) (t : R) :
  bernoulli_RV X -> 'M_(btr P X : {RV P >-> R}) t = (p * expR t + (1-p))%:E.
Proof.
move=> bX. rewrite/mmt_gen_fun.
pose mmtX : {RV P >-> R} := expR \o t \o* (btr P X).
set A := X @^-1` [set true].
set B := X @^-1` [set false].
have mA: measurable A by exact: measurable_sfunP.
have mB: measurable B by exact: measurable_sfunP.
have dAB: [disjoint A & B]
  by rewrite /disj_set /A /B preimage_true preimage_false setICr.
have TAB: setT = A `|` B by rewrite -preimage_setU -setT_bool preimage_setT.
rewrite unlock.
rewrite TAB integral_setU_EFin -?TAB//.
under eq_integral.
  move=> x /=.
  rewrite /A inE /bool_to_real /= => ->.
  rewrite mul1r.
  over.
rewrite integral_cst//.
under eq_integral.
  move=> x /=.
  rewrite /B inE /bool_to_real /= => ->.
  rewrite mul0r.
  over.
rewrite integral_cst//.
rewrite /A /B /preimage /=.
under eq_set do rewrite (propext (rwP eqP)).
rewrite (bernoulli_RV1 bX).
under eq_set do rewrite (propext (rwP eqP)).
rewrite (bernoulli_RV2 bX).
rewrite -EFinD; congr (_ + _)%:E; rewrite mulrC//.
by rewrite expR0 mulr1.
Qed.

(* wrong lemma *)
Lemma binomial_mmt_gen_fun n (X_ : n.-tuple {RV P >-> bool}) (t : R) :
  is_bernoulli_trial X_ ->
  let X := bernoulli_trial X_ : {RV pro P n >-> R} in
  'M_X t = ((p * expR t + (1-p))`^(n%:R))%:E.
Proof.
move: p01 => /andP[p0 p1] bX/=.
rewrite bernoulli_trial_mmt_gen_fun//.
under eq_bigr => i _.
  rewrite bernoulli_mmt_gen_fun; last exact: bX.
  over.
rewrite big_const iter_mule mule1 cardT size_enum_ord -EFin_expe powR_mulrn//.
by rewrite addr_ge0// ?subr_ge0// mulr_ge0// expR_ge0.
Qed.

(* TODO: add to the PR by reynald that adds the \prod notation to master *)
Lemma prod_EFin U l Q (f : U -> R) : \prod_(i <- l | Q i) ((f i)%:E) = (\prod_(i <- l | Q i) f i)%:E.
Proof.
elim: l; first by rewrite !big_nil.
move=> a l ih.
rewrite !big_cons.
case: ifP => //= aQ.
by rewrite EFinM ih.
Qed.

Lemma mmt_gen_fun_expectation n (X_ : n.-tuple {RV P >-> bool}) (t : R) :
  (0 <= t)%R ->
  is_bernoulli_trial X_ ->
  let X := bernoulli_trial X_ : {RV pro P n >-> R} in
  'M_X t <= (expR (fine 'E_(pro P n)[X] * (expR t - 1)))%:E.
Proof.
move=> t0 bX/=.
have /andP[p0 p1] := p01.
rewrite binomial_mmt_gen_fun// lee_fin.
rewrite expectation_bernoulli_trial//.
rewrite addrCA -{2}(mulr1 p) -mulrN -mulrDr.
rewrite -mulrA (mulrC (n%:R)) expRM ge0_ler_powR// ?nnegrE ?expR_ge0//.
  by rewrite addr_ge0// mulr_ge0// subr_ge0 -expR0 ler_expR.
exact: expR_ge1Dx.
Qed.

Lemma end_thm24 n (X_ : n.-tuple {RV P >-> bool}) (t delta : R) :
  is_bernoulli_trial X_ ->
  (0 < delta)%R ->
  let X := @bernoulli_trial n X_ in
  let mu := 'E_(pro P n)[X] in
  let t := ln (1 + delta) in
  (expR (expR t - 1) `^ fine mu)%:E *
    (expR (- t * (1 + delta)) `^ fine mu)%:E <=
    ((expR delta / (1 + delta) `^ (1 + delta)) `^ fine mu)%:E.
Proof.
move=> bX d0 /=.
rewrite -EFinM lee_fin -powRM ?expR_ge0// ge0_ler_powR ?nnegrE//.
- by rewrite fine_ge0// expectation_ge0// => x; exact: (bernoulli_trial_ge0 bX).
- by rewrite divr_ge0 ?expR_ge0// powR_ge0.
- rewrite lnK ?posrE ?addr_gt0// addrAC subrr add0r ler_wpM2l ?expR_ge0//.
  by rewrite -powRN mulNr -mulrN expRM lnK// posrE addr_gt0.
Qed.

(* theorem 2.4 Rajani / thm 4.4.(2) mu-book *)
Theorem bernoulli_trial_inequality1 n (X_ : n.-tuple {RV P >-> bool}) (delta : R) :
  is_bernoulli_trial X_ ->
  (0 < delta)%R ->
  let X := @bernoulli_trial n X_ in
  let mu := 'E_(pro P n)[X] in
  (pro P n) [set i | X i >= (1 + delta) * fine mu]%R <=
  ((expR delta / ((1 + delta) `^ (1 + delta))) `^ (fine mu))%:E.
Proof.
rewrite /= => bX delta0.
set X := @bernoulli_trial n X_.
set mu := 'E_(pro P n)[X].
set t := ln (1 + delta).
have t0 : (0 < t)%R by rewrite ln_gt0// ltrDl.
apply: (le_trans (chernoff _ _ t0)).
apply: (@le_trans _ _ ((expR (fine mu * (expR t - 1)))%:E *
                       (expR (- (t * ((1 + delta) * fine mu))))%:E)).
  rewrite lee_pmul2r ?lte_fin ?expR_gt0//.
  by apply: (mmt_gen_fun_expectation _ bX); rewrite le_eqVlt t0 orbT.
rewrite mulrC expRM -mulNr mulrA expRM.
exact: (end_thm24 _ bX).
Qed.

(* theorem 2.5 *)
Theorem bernoulli_trial_inequality2 n (X : n.-tuple {RV P >-> bool}) (delta : R) :
  is_bernoulli_trial X ->
  let X' := @bernoulli_trial n X in
  let mu := 'E_(pro P n)[X'] in
  (0 < n)%nat ->
  (0 < delta < 1)%R ->
  (pro P n) [set i | X' i >= (1 + delta) * fine mu]%R <=
  (expR (- (fine mu * delta ^+ 2) / 3))%:E.
Proof.
move=> bX X' mu n0 /[dup] delta01 /andP[delta0 _].
apply: (@le_trans _ _ (expR ((delta - (1 + delta) * ln (1 + delta)) * fine mu))%:E).
  rewrite expRM expRB (mulrC _ (ln _)) expRM lnK; last rewrite posrE addr_gt0//.
  apply: (bernoulli_trial_inequality1 bX) => //.
apply: (@le_trans _ _ (expR ((delta - (delta + delta ^+ 2 / 3)) * fine mu))%:E).
  rewrite lee_fin ler_expR ler_wpM2r//.
    by rewrite fine_ge0//; apply: expectation_ge0 => t; exact: (bernoulli_trial_ge0 bX).
  rewrite lerB//.
  apply: taylor_ln_le.
  by rewrite in_itv /=.
rewrite le_eqVlt; apply/orP; left; apply/eqP; congr (expR _)%:E.
by rewrite opprD addrA subrr add0r mulrC mulrN mulNr mulrA.
Qed.

(* TODO: move *)
Lemma ln_div : {in Num.pos &, {morph ln (R:=R) : x y / (x / y)%R >-> (x - y)%R}}.
Proof.
by move=> x y; rewrite !posrE => x0 y0; rewrite lnM ?posrE ?invr_gt0// lnV ?posrE.
Qed.

Lemma norm_expR : normr \o expR = (expR : R -> R).
Proof. by apply/funext => x /=; rewrite ger0_norm ?expR_ge0. Qed.

(* Rajani thm 2.6 / mu-book thm 4.5.(2) *)
Theorem bernoulli_trial_inequality3 n (X : n.-tuple {RV P >-> bool}) (delta : R) :
  is_bernoulli_trial X -> (0 < delta < 1)%R ->
  let X' := @bernoulli_trial n X : {RV pro P n >-> R} in
  let mu := 'E_(pro P n)[X'] in
  (pro P n) [set i | X' i <= (1 - delta) * fine mu]%R <= (expR (-(fine mu * delta ^+ 2) / 2)%R)%:E.
Proof.
move=> bX /andP[delta0 delta1] /=.
set X' := @bernoulli_trial n X : {RV pro P n >-> R}.
set mu := 'E_(pro P n)[X'].
have /andP[p0 p1] := p01.
apply: (@le_trans _ _ (((expR (- delta) / ((1 - delta) `^ (1 - delta))) `^ (fine mu))%:E)).
  (* using Markov's inequality somewhere, see mu's book page 66 *)
  have H1 t : (t < 0)%R ->
    (pro P n) [set i | (X' i <= (1 - delta) * fine mu)%R] = (pro P n) [set i | `|(expR \o t \o* X') i|%:E >= (expR (t * (1 - delta) * fine mu))%:E].
    move=> t0; apply: congr1; apply: eq_set => x /=.
    rewrite lee_fin ger0_norm ?expR_ge0// ler_expR (mulrC _ t) -mulrA.
    by rewrite -[in RHS]ler_ndivrMl// mulrA mulVf ?lt_eqF// mul1r.
  set t := ln (1 - delta).
  have ln1delta : (t < 0)%R.
    (* TODO: lacking a lemma here *)
    rewrite -oppr0 ltrNr -lnV ?posrE ?subr_gt0// ln_gt0//.
    by rewrite invf_gt1// ?subr_gt0// ltrBlDr ltrDl.
  have {H1}-> := H1 _ ln1delta.
  apply: (@le_trans _ _ (((fine 'E_(pro P n)[normr \o expR \o t \o* X']) / (expR (t * (1 - delta) * fine mu))))%:E).
    rewrite EFinM lee_pdivl_mulr ?expR_gt0// muleC fineK.
    apply: (@markov _ _ _ (pro P n) (expR \o t \o* X' : {RV (pro P n) >-> R}) id (expR (t * (1 - delta) * fine mu))%R _ _ _ _) => //.
    - apply: expR_gt0.
    - rewrite norm_expR.
      have -> : 'E_(pro P n)[expR \o t \o* X'] = 'M_X' t by [].
      by rewrite (binomial_mmt_gen_fun _ bX).
  apply: (@le_trans _ _ (((expR ((expR t - 1) * fine mu)) / (expR (t * (1 - delta) * fine mu))))%:E).
    rewrite norm_expR lee_fin ler_wpM2r ?invr_ge0 ?expR_ge0//.
    have -> : 'E_(pro P n)[expR \o t \o* X'] = 'M_X' t by [].
    rewrite (binomial_mmt_gen_fun _ bX)/=.
    rewrite /mu /X' (expectation_bernoulli_trial bX)/=.
    rewrite !lnK ?posrE ?subr_gt0//.
    rewrite expRM powRrM powRAC.
    rewrite ge0_ler_powR ?ler0n// ?nnegrE ?powR_ge0//.
      by rewrite addr_ge0 ?mulr_ge0// subr_ge0// ltW.
    rewrite addrAC subrr sub0r -expRM.
    rewrite addrCA -{2}(mulr1 p) -mulrBr addrAC subrr sub0r mulrC mulNr.
    by apply: expR_ge1Dx.
  rewrite !lnK ?posrE ?subr_gt0//.
  rewrite -addrAC subrr sub0r -mulrA [X in (_ / X)%R]expRM lnK ?posrE ?subr_gt0//.
  rewrite -[in leRHS]powR_inv1 ?powR_ge0// powRM// ?expR_ge0 ?invr_ge0 ?powR_ge0//.
  by rewrite powRAC powR_inv1 ?powR_ge0// powRrM expRM.
rewrite lee_fin.
rewrite -mulrN -mulrA [in leRHS]mulrC expRM ge0_ler_powR// ?nnegrE.
- by rewrite fine_ge0// expectation_ge0// => x; exact: (bernoulli_trial_ge0 bX).
- by rewrite divr_ge0 ?expR_ge0// powR_ge0.
- by rewrite expR_ge0.
- rewrite -ler_ln ?posrE ?divr_gt0 ?expR_gt0 ?powR_gt0 ?subr_gt0//.
  rewrite expRK// ln_div ?posrE ?expR_gt0 ?powR_gt0 ?subr_gt0//.
  rewrite expRK//.
  rewrite /powR (*TODO: lemma ln of powR*) gt_eqF ?subr_gt0// expRK.
  (* requires analytical argument: see p.66 of mu's book *)
  Local Open Scope ring_scope.
  rewrite -(@ler_pM2r _ 2)// -mulrA mulVf// mulr1 mulrDl.
  rewrite -subr_le0 mulNr opprK.
  rewrite addrC !addrA.
  have->: delta ^+ 2 - delta * 2 = (1 - delta)^+2 - 1.
    rewrite sqrrB expr1n mul1r [RHS]addrC !addrA addNr add0r addrC -mulNrn.
    by rewrite -(mulr_natr (- delta) 2) mulNr.
  rewrite addrAC subr_le0.
  set f := fun (x : R) => x ^+ 2 + - (x * ln x) * 2.
  have @idf (x : R^o) : 0 < x -> {df | is_derive x 1 (f : R^o -> R^o) df}.
    move=> x0; evar (df : (R : Type)); exists df.
    apply: is_deriveD; first by [].
    apply: is_deriveM; last by [].
    apply: is_deriveN.
    apply: is_deriveM; first by [].
    exact: is_derive1_ln.
  suff: forall x : R, x \in `]0, 1[ -> f x <= 1.
    by apply; rewrite memB_itv0 in_itv /= delta0 delta1.
  move=> x x01.
  have->: 1 = f 1 by rewrite /f expr1n ln1 mulr0 oppr0 mul0r addr0.
  apply: (@ger0_derive1_homo _ f 0 1 false false)=> //.
  - move=> t /[!in_itv] /= /andP [] + _.
    by case/idf=> ? /@ex_derive.
  - move=> t /[!in_itv] /= /andP [] t0 t1.
    Local Arguments derive_val {R V W a v f df}.
    rewrite (derive_val (svalP (idf _ t0))) /=.
    clear idf.
    rewrite exp_derive derive_cst derive_id .
    rewrite scaler0 add0r /GRing.scale /= !mulr1 expr1.
    rewrite -mulrDr mulr_ge0// divff ?lt0r_neq0//.
    rewrite opprD addrA subr_ge0 -ler_expR.
    have:= t0; rewrite -lnK_eq => /eqP ->.
    by rewrite -[leLHS]addr0 -(subrr 1) addrCA expR_ge1Dx.
  - apply: derivable_within_continuous => t /[!in_itv] /= /andP [] + _.
    by case/idf=> ? /@ex_derive.
  - by apply: (subset_itvW_bound _ _ x01); rewrite bnd_simp.
  - by rewrite in_itv /= ltr01 lexx.
  - by move: x01; rewrite in_itv=> /= /andP [] _ /ltW.
Qed.
Local Open Scope ereal_scope.

Lemma measurable_fun_le D (f g : T -> R) : d.-measurable D -> measurable_fun D f ->
  measurable_fun D g -> measurable (D `&` [set x | f x <= g x]%R).
Proof.
move=> mD mf mg.
under eq_set => x do rewrite -lee_fin.
apply: emeasurable_fun_le => //; apply: measurableT_comp => //.
Qed.

(* Rajani -> corollary 2.7 / mu-book -> corollary 4.7 *)
Corollary bernoulli_trial_inequality4 n (X : n.-tuple {RV P >-> bool}) (delta : R) :
  is_bernoulli_trial X -> (0 < delta < 1)%R ->
  (0 < n)%nat ->
  (0 < p)%R ->
  let X' := @bernoulli_trial n X in
  let mu := 'E_(pro P n)[X'] in
  (pro P n) [set i | `|X' i - fine mu | >=  delta * fine mu]%R <=
  (expR (- (fine mu * delta ^+ 2) / 3)%R *+ 2)%:E.
Proof.
move=> bX /andP[d0 d1] n0 p0 /=.
set X' := @bernoulli_trial n X.
set mu := 'E_(pro P n)[X'].
under eq_set => x.
  rewrite ler_normr.
  rewrite lerBrDl opprD opprK -{1}(mul1r (fine mu)) -mulrDl.
  rewrite -lerBDr -(lerN2 (- _)%R) opprK opprB.
  rewrite -{2}(mul1r (fine mu)) -mulrBl.
  rewrite -!lee_fin.
  over.
rewrite /=.
rewrite set_orb.
rewrite measureU; last 3 first.
- rewrite -(@setIidr _ setT [set _ | _]) ?subsetT//.
  apply: emeasurable_fun_le => //.
  apply: measurableT_comp => //.
- rewrite -(@setIidr _ setT [set _ | _]) ?subsetT//.
  apply: emeasurable_fun_le => //.
  apply: measurableT_comp => //.
- rewrite disjoints_subset => x /=.
  rewrite /mem /in_mem/= => X0; apply/negP.
  rewrite -ltNge.
  apply: (@lt_le_trans _ _ _ _ _ _ X0).
  rewrite !EFinM.
  rewrite lte_pmul2r//; first by rewrite lte_fin ltrD2l gt0_cp.
  by rewrite fineK /mu/X' (expectation_bernoulli_trial bX)// lte_fin  mulr_gt0 ?ltr0n.
rewrite mulr2n EFinD lee_add//=.
- by apply: (bernoulli_trial_inequality2 bX); rewrite //d0 d1.
- have d01 : (0 < delta < 1)%R by rewrite d0.
  apply: (le_trans (@bernoulli_trial_inequality3 _ X delta bX d01)).
  rewrite lee_fin ler_expR !mulNr lerN2.
  rewrite ler_pM//; last by rewrite lef_pV2 ?posrE ?ler_nat.
  rewrite mulr_ge0 ?fine_ge0 ?sqr_ge0//.
  rewrite /mu unlock /expectation integral_ge0// => x _.
  by rewrite /X' lee_fin; apply: (bernoulli_trial_ge0 bX).
Qed.

(* Rajani thm 3.1 / mu-book thm 4.7 *)
Theorem sampling n (X : n.-tuple {RV P >-> bool}) (theta delta : R) :
  let X_sum := bernoulli_trial X in
  let X' x := (X_sum x) / n%:R in
  (0 < p)%R ->
  is_bernoulli_trial X ->
  (0 < delta <= 1)%R -> (0 < theta < p)%R -> (0 < n)%nat ->
  (3 / theta ^+ 2 * ln (2 / delta) <= n%:R)%R ->
  (pro P n) [set i | `| X' i - p | <= theta]%R >= 1 - delta%:E.
Proof.
move=> X_sum X' p0 bX /andP[delta0 delta1] /andP[theta0 thetap] n0 tdn.
have E_X_sum: 'E_(pro P n)[X_sum] = (p * n%:R)%:E.
  by rewrite /X_sum expectation_bernoulli_trial// mulrC.
have /andP[_ p1] := p01.
set epsilon := theta / p.
have epsilon01 : (0 < epsilon < 1)%R.
  by rewrite /epsilon ?ltr_pdivrMr ?divr_gt0 ?mul1r.
have thetaE : theta = (epsilon * p)%R.
  by rewrite /epsilon -mulrA mulVf ?mulr1// gt_eqF.
have step1 : (pro P n) [set i | `| X' i - p | >= epsilon * p]%R <=
    ((expR (- (p * n%:R * (epsilon ^+ 2)) / 3)) *+ 2)%:E.
  rewrite [X in (pro P n) X <= _](_ : _ =
      [set i | `| X_sum i - p * n%:R | >= epsilon * p * n%:R]%R); last first.
    apply/seteqP; split => [t|t]/=.
      move/(@ler_wpM2r _ n%:R (ler0n _ _)) => /le_trans; apply.
      rewrite -[X in (_ * X)%R](@ger0_norm _ n%:R)// -normrM mulrBl.
      by rewrite -mulrA mulVf ?mulr1// gt_eqF ?ltr0n.
    move/(@ler_wpM2r _ n%:R^-1); rewrite invr_ge0// ler0n => /(_ erefl).
    rewrite -(mulrA _ _ n%:R^-1) divff ?mulr1 ?gt_eqF ?ltr0n//.
    move=> /le_trans; apply.
    rewrite -[X in (_ * X)%R](@ger0_norm _ n%:R^-1)// -normrM mulrBl.
    by rewrite -mulrA divff ?mulr1// gt_eqF// ltr0n.
  rewrite -mulrA.
  have -> : (p * n%:R)%R = fine (p * n%:R)%:E by [].
  rewrite -E_X_sum.
  exact: (@bernoulli_trial_inequality4 _ X epsilon bX).
have step2 : (pro P n) [set i | `| X' i - p | >= theta]%R <=
    ((expR (- (n%:R * theta ^+ 2) / 3)) *+ 2)%:E.
  rewrite thetaE; move/le_trans : step1; apply.
  rewrite lee_fin ler_wMn2r// ler_expR mulNr lerNl mulNr opprK.
  rewrite -2![in leRHS]mulrA [in leRHS]mulrCA.
  rewrite /epsilon -mulrA mulVf ?gt_eqF// mulr1 -!mulrA !ler_wpM2l ?(ltW theta0)//.
  rewrite mulrCA ler_wpM2l ?(ltW theta0)//.
  rewrite [X in (_ * X)%R]mulrA mulVf ?gt_eqF// -[leLHS]mul1r [in leRHS]mul1r.
  by rewrite ler_wpM2r// invf_ge1.
suff : delta%:E >= (pro P n) [set i | (`|X' i - p| >=(*NB: this >= in the pdf *) theta)%R].
  rewrite [X in (pro P n) X <= _ -> _](_ : _ = ~` [set i | (`|X' i - p| < theta)%R]); last first.
    apply/seteqP; split => [t|t]/=.
      by rewrite leNgt => /negP.
    by rewrite ltNge => /negP/negPn.
  have ? : measurable [set i | (`|X' i - p| < theta)%R].
    under eq_set => x do rewrite -lte_fin.
    rewrite -(@setIidr _ setT [set _ | _]) ?subsetT /X'//.
    by apply: emeasurable_fun_lt => //; apply: measurableT_comp => //;
      apply: measurableT_comp => //; apply: measurable_funD => //;
      apply: measurable_funM.
  rewrite probability_setC// lee_subel_addr//.
  rewrite -lee_subel_addl//; last by rewrite fin_num_measure.
  move=> /le_trans; apply.
  rewrite le_measure ?inE//.
    under eq_set => x do rewrite -lee_fin.
    rewrite -(@setIidr _ setT [set _ | _]) ?subsetT /X'//.
    by apply: emeasurable_fun_le => //; apply: measurableT_comp => //;
      apply: measurableT_comp => //; apply: measurable_funD => //;
      apply: measurable_funM.
  by move=> t/= /ltW.
(* NB: last step in the pdf *)
apply: (le_trans step2).
rewrite lee_fin -(mulr_natr _ 2) -ler_pdivlMr//.
rewrite -(@lnK _ (delta / 2)); last by rewrite posrE divr_gt0.
rewrite ler_expR mulNr lerNl -lnV; last by rewrite posrE divr_gt0.
rewrite invf_div ler_pdivlMr// mulrC.
rewrite -ler_pdivrMr; last by rewrite exprn_gt0.
by rewrite mulrAC.
Admitted.

End bernoulli.
