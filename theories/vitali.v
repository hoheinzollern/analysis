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

Definition C1 (I : set R) (f : R^o -> R^o) :=
  (forall x, x \in I -> differentiable f x) /\
  {within I, continuous f^`()}.

Definition AC (a b : R) (f : R -> R) := forall e : {posnum R},
  exists d : {posnum R}, forall n (ab : 'I_n -> R * R),
    (forall i, `[(ab i).1, (ab i).2]%classic `<=` `[a, b]%classic) /\
    trivIset setT (fun i => `[(ab i).1, (ab i).2]%classic) /\
    \sum_(k < n) maxr 0 ((ab k).2  - (ab k).1) < d%:num ->
    \sum_(k < n) maxr 0 (f (ab k).2  - f (ab k).1) < e%:num.

Open Scope ring_scope.

Lemma C1_is_AC (a b : R) (f : R -> R) :
  C1 `[a, b] f -> AC a b f.
Proof.
move=> [df cdf] e.
(* pose M := maxr 0 [set x : R| exists y, y \in `[a, b]%classic /\ x = `|f^`() y|]. *)
(* pose d := e / M)*)
(* forall n and ab,
 * \sum_(k < n) maxr 0 (f (ab k).2 - f (ab k).1)
 *    <= M * \sum_(k < n) maxr 0 ((ab k).2 - (ab k).1)
 *    <  M * d
 *    =  e
 *)
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
  \int[[the measure _ _ of mu]]_(x in `[a, b]) f^`() x <= f b - f a.
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
      (\int[[the measure _ _ of mu]]_(x in E) `| (f x)%:E | < e%:num%:E)%E.
Proof.
Admitted.

Theorem L1_integral_AC (f : R -> R) (a b : R) :
  f \in L1 a b -> AC a b (fun x => \int[[the measure _ _ of mu]]_(z in `[a, x]) f z).
Proof.
Admitted.

Lemma L1_integral_0 (f : R -> R) (a b : R) :
  f \in L1 a b -> (forall c, c \in `[a, b] -> \int[[the measure _ _ of mu]]_(x in `[a, c]) f x = 0) ->
    {ae mu, forall x, x \in `[a, b] -> f x = 0}.
Proof.
Admitted.

Corollary L1_integral_eq (f g : R -> R) (a b : R) :
  f \in L1 a b -> g \in L1 a b ->
    (forall c, c \in `[a, b] -> \int[[the measure _ _ of mu]]_(x in `[a, c]) f x = \int[[the measure _ _ of mu]]_(x in `[a, c]) g x) ->
      {ae mu, forall x, x \in `[a, b] -> f x = g x}.
Proof.
Admitted.

Theorem L1_integral_derive (f : R -> R) (a b : R) :
  {ae mu, forall x, x \in `[a, b] ->
    let F (x : R^o) : R^o := \int[[the measure _ _ of mu]]_(z in `[a, x]) f z in
    F^`() = f}.
Proof.
Admitted.

Corollary AC_integral_derive (f : R^o -> R^o) (a b : R) :
  AC a b f -> \int[[the measure _ _ of mu]]_(x in `[a, b]) f^`() x = f b - f a.
Proof.
Admitted.

Theorem Lebesgue_density (E : set R) :
  (0 < mu E)%E -> {ae mu, forall x, x \in E ->
    (fun e => fine (mu (E `&` `[x-e, x+e])) / (fine (mu `[x-e, x+e]))) @ (0:R)^' --> (1:R)}.
Proof.
Admitted.

End Integral_absolutely_continuous.

Section Partition.
Context {R : realType}.
Variables a b : R.
Variable n : nat.

Definition PartitionL i := a + i%:R * 2 ^- n * (b - a).

Definition Partition i :=
  `[PartitionL i, PartitionL i.+1[%classic.

Lemma PartitionP : `[a, b[%classic =
  \big[setU/set0]_(i < (2 ^ n).+1) Partition i.
Proof.
Admitted.

End Partition.

Section ftc_RN.
Context {R : realType}.
Variables a b : R.
Variable f : R^o -> R^o. (* non decreasing *)
Hypothesis f_AC : AC a b f.
Variable lsf : {measure set [the measurableType (R.-ocitv.-measurable).-sigma of salgebraType (R.-ocitv.-measurable)] -> \bar R}. (* lebesgue stietljes measure of f *)

Theorem FTC t : t \in `[a, b] ->
  f t - f a = \int[[the measure _ _ of @lebesgue_measure R]]_(s in `[a, t] ) f^`() s.
Proof.
move=> tab.
have [h hh] : exists h, forall A, measurable A ->
    [the measure _ _ of @lebesgue_measure R].-integrable setT h /\
    lsf A = (\int[[the measure _ _ of @lebesgue_measure R]]_s (h s))%E.
  (* TODO: requires lsf `<< [the measure _ _ of @lebesgue_measure R] *)
  admit.
pose h_ n x := if x == b then 0 else
  \sum_(i < (2 ^ n).+1) (fine (lsf (Partition a b n i)) /
                         fine (lebesgue_measure (Partition a b n i)))
                        * \1_(Partition a b n i) x.
have h_h : {ae @lebesgue_measure R, forall x, (h_ n x)%:E @[n --> \oo] --> h x}.
  admit.
have f_diff : {ae @lebesgue_measure R, forall x, differentiable f x}.
  admit.
have f'_h : {ae @lebesgue_measure R, forall x, (f^`() x)%:E = h x}.
  admit.
rewrite /=.
transitivity (fine (lsf (`[a, t]%classic))).
  admit. (* lebesgue-stieltjes definition *)
transitivity (fine (\int[[the measure _ _ of @lebesgue_measure R]]_(s in `[a, t]) h s)).
  admit. (* by RN *)
(* see ge0_ae_eq_integral or a related lemma *)
admit.
Abort.

End ftc_RN.

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

Require Import nsatz_realtype.

Lemma integral_sin (x : R) : \int[mu]_(z in `[0, x]) sin z = -cos x + 1.
Proof.
rewrite -[in RHS]cos0 [RHS](_ : _ = - cos x - - cos 0); last by nsatz.
rewrite -(@AC_integral_derive _ (fun x => - cos x)); last first.
  apply C1_is_AC.
  split.
    move => z z0x.
    apply/derivable1_diffP.
    apply derivableN.
    apply: derivable_cos.
  apply: continuous_subspaceT.
  rewrite (_ : _^`() = (fun x => sin x : R^o)); last first.
    apply/funext => y /=.
    by rewrite derive1E deriveN// -derive1E derive1_cos opprK.
  exact: continuous_sin.
congr Rintegral => //=.
apply/funext => y.
by rewrite derive1E deriveN// -derive1E derive1_cos opprK.
Qed.

End examples.

Section pushforward_measure.
Local Open Scope ereal_scope.
Context d d' (T1 : measurableType d) (T2 : measurableType d') (f : T1 -> T2).
Variables (R : realFieldType) (m : {measure set T1 -> \bar R}).
Variables (D : set T1) (mD : measurable D).

Definition pushforward (mf : measurable_fun D f) A := m (D `&` f @^-1` A).

Hypothesis mf : measurable_fun D f.

Let pushforward0 : pushforward mf set0 = 0.
Proof. by rewrite /pushforward preimage_set0 setI0 measure0. Qed.

Let pushforward_ge0 A : 0 <= pushforward mf A.
Proof. exact: measure_ge0. Qed.

Let pushforward_sigma_additive : semi_sigma_additive (pushforward mf).
Proof.
move=> F mF tF mUF; rewrite /pushforward preimage_bigcup setI_bigcupr.
apply: measure_semi_sigma_additive.
- by move=> n; exact: mf.
- apply: trivIset_setIl => //.
  apply/trivIsetP => /= i j _ _ ij; rewrite -preimage_setI.
  by move/trivIsetP : tF => /(_ _ _ _ _ ij) ->//; rewrite preimage_set0.
- by rewrite -setI_bigcupr -preimage_bigcup; exact: mf.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  (pushforward mf) pushforward0 pushforward_ge0 pushforward_sigma_additive.

End pushforward_measure.

Section transfer.
Local Open Scope ereal_scope.
Context d1 d2 (X : measurableType d1) (Y : measurableType d2) (R : realType).
Variables (D : set X) (mD : measurable D).
Variables (phi : X -> Y) (mphi : measurable_fun D phi)
  (phiD : d2.-measurable (phi @` D)).
Variables (mu : {measure set X -> \bar R}).

Lemma integral_pushforward (f : Y -> \bar R) :
  measurable_fun setT f -> (forall y, 0 <= f y) ->
  \int[pushforward mu mphi]_(y in phi @` D) f y = \int[mu]_(x in D) (f \o phi) x.
Proof.
move=> mf f0.
have [f_ [ndf_ f_f]] := approximation measurableT mf (fun t _ => f0 t).
transitivity (lim (fun n => \int[pushforward mu mphi]_(x in phi @` D) (f_ n x)%:E)).
  rewrite -monotone_convergence//.
  - by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: f_f.
  - move=> n; apply/EFin_measurable_fun.
    exact: (@measurable_funS _ _ _ _ setT).
  - by move=> n y phi_y; rewrite lee_fin.
  - by move=> y phi_y m n mn; rewrite lee_fin; apply/lefP/ndf_.
rewrite (_ : (fun _ => _) = (fun n => \int[mu]_(x in D) (EFin \o f_ n \o phi) x)).
  rewrite -monotone_convergence//; last 3 first.
    - move=> n /=; apply: measurable_funT_comp; first exact: measurable_fun_EFin.
      by apply: measurable_funT_comp => //.
    - by move=> n x _ /=; rewrite lee_fin.
    - by move=> x _ m n mn; rewrite lee_fin; exact/lefP/ndf_.
  by apply: eq_integral => x _ /=; apply/cvg_lim => //; exact: f_f.
apply/funext => n.
have mfnphi r : measurable (D `&` (f_ n @^-1` [set r] \o phi)).
  exact/mphi.
transitivity (\sum_(k \in range (f_ n))
    \int[mu]_(x in D) (k * \1_(D `&` ((f_ n @^-1` [set k]) \o phi)) x)%:E).
  under eq_integral do rewrite fimfunE -fsumEFin//.
  rewrite ge0_integral_fsum//; last 2 first.
    - move=> y; apply/EFin_measurable_fun; apply: measurable_funM.
        exact: measurable_fun_cst.
      rewrite (_ : \1_ _ = mindic R (measurable_sfunP (f_ n) (measurable_set1 y)))//.
      exact: (@measurable_funS _ _ _ _ setT).
    - by move=> y x _; rewrite nnfun_muleindic_ge0.
  apply: eq_fsbigr => r ?; rewrite integralM_indic_nnsfun// integral_indic//=.
  rewrite (integralM_indic _ (fun r => D `&` (f_ n @^-1` [set r] \o phi)))//.
    congr (_ * _); rewrite [RHS](@integral_indic)//.
    rewrite /pushforward/=.
    congr (mu _).
    apply/seteqP; split => [x [Dx [/= fphir [x0 Dx0 x0x]]]|].
      by split => //.
    move=> x [[Dx /= phixr] _]; split => //; split => //.
    by exists x.
  by move=> r0; rewrite preimage_nnfun0//= setI0.
rewrite -ge0_integral_fsum//; last 2 first.
  - move=> r; apply/EFin_measurable_fun; apply: measurable_funM.
      exact: measurable_fun_cst.
    rewrite (_ : \1_ _ = mindic R (mfnphi r))//.
    by apply: (@measurable_funS _ _ _ _ setT).
  - move=> r x Dx.
    rewrite EFinM.
    rewrite indicE.
    rewrite in_setI (mem_set Dx) /=.
    by rewrite nnfun_muleindic_ge0.
apply: eq_integral => x xD.
rewrite /=.
rewrite fsumEFin//=.
transitivity ((\sum_(i \in range (f_ n)) (i * \1_((f_ n @^-1` [set i] \o phi)) x))%:E).
  congr EFin.
  apply: eq_fsbigr => y yfn.
  by rewrite indicE in_setI xD/=.
by rewrite -fimfunE.
Qed.

End transfer.

(* statement from Burkill *)
(* NB: other reference
   https://healy.econ.ohio-state.edu/kcb/Ma103/Notes/Integration.pdf *)
Section change.
Variables (R : realType) (g : R^o -> R^o) (a b : R).
Hypothesis ACg : AC a b g.
Hypothesis ndg : {in `[a, b], {homo g : x y / x <= y}}.
Variable (f : R -> R).
Let mu := @lebesgue_measure R.
Hypothesis fi : mu.-integrable `[a, b] (EFin \o f).

Lemma burkill521 (F : R -> R) (X : R -> R) :
  AC a b F -> AC a b X -> {homo X : x y / x <= y} ->
  AC a b (F \o X).
Proof.
Admitted.

Lemma burkill522 (X : set R) : measurable X -> X `<=` range g ->
  mu X = 0%E ->
  let T := g @^-1` X in
  {ae mu, forall t, t \in T -> g^`() t = 0}.
Proof.
move=> mX Xg muX0 T.
have H1 := @AC_integral_derive R g a b ACg.
set Ox := `](g b), (g a)[%classic.
set Ot := `]b, a[%classic.
have H2 : \int[mu]_(x in Ot) g^`() x = fine (mu Ox).
  admit.
have [Ox_ [oOx XOx_ dOx_ muOx_0]] : exists (Ox_ : (set R)^nat),
  [/\ (forall n, open (Ox_ n)), (forall n, X `<=` Ox_ n),
      {homo mu \o Ox_ : x y / (x <= y)%N >-> (x > y)%E} &
      mu \o Ox_ --> 0%E].
  admit.
pose Ot_ k := g @^-1` (Ox_ k).
pose T0 := \bigcap_i (Ot_ i).
have H3 : T `<=` T0.
  apply: sub_bigcap => i _.
  rewrite /T /Ot_.
  apply: preimage_subset.
  exact: XOx_.
have H4 (e : {posnum R}) :
    \forall n \near \oo, \int[mu]_(t in T0) g^`() t <=
                         \int[mu]_(t in Ox_ n) g^`() t < e%:num.
  (* NB: use \int[mu]_(t in Ox_ n) g^`() t = mu (Ox n) *)
  admit.
have H5 : \int[mu]_(t in T0) g^`() t = 0.
  admit.
have H6 : forall t, g^`() t >= 0.
  admit.
have : {ae mu, forall t, t \in T0 -> g^`() t = 0}.
  admit.
by apply/ae_imply => /= x /[swap] /[!inE] /H3 /[swap] /[apply].
Admitted.

Lemma change :
  \int[mu]_(t in `[a, b]) (f (g t) * g^`() t) =
  \int[mu]_(u in `[g a, g b]) f u.
Proof.
(* use burkill521 and burkill522 *)
Admitted.

Section change.

Section gauss_integral.
(* ref : https://mathlandscape.com/gauss-integral/#toc4 *)
Let dx := @lebesgue_measure R.
Let Gaussian := fun (x : R) => expR (- (x ^+ 2)).

(*
Lemma integral_M_integral (f g: R -> R) : \int[dx]_x f x * \int[dx]_x g x =
\int[dx \* dx]_z (f z.1) * (g z.2).
*)
Print tan.
Check (tan\^-1) a.
Check ((tan : R^o -> R^o)^`()).

Lemma derive1_comp (f1 f2: R^o -> R^o) : (f1 \o f2)^`() = f2^`() \* (f1^`() \o f2).
Proof.
Admitted.

Lemma derive1_expR2 : ((fun (x : R) => expR (- (x^+ 2))): R^o -> R^o)^`() = (fun x => -x * expR(- (x ^+ 2))).
Proof.
(* apply: derive1_comp. *)
Admitted.
Lemma deriveM (f1 f2: R^o -> R^o) : (f1 \* f2)^`() =
(f1^`() \* f2) \+ (f1 \* f2^`()).
Proof.
Admitted.

Lemma derive1_arctan : (tan\^-1 : R^o -> R^o)^`() = (fun t => 1 / (1 + t ^+ 2)).
Proof.
have tan_inv (x : R): tan\^-1=(fun x => cos x) \* (fun x => 1/sin x).
  rewrite /tan/inv_fun.
  under eq_fun do rewrite invf_div.
  rewrite /mul_fun.
  apply/funext => z.
  by rewrite mulrA mulr1.
rewrite tan_inv.
apply /funext => x.
apply deriveM.
rewrite derive1E.
apply deriveM.
rewrite derive_val.
Admitted.

Lemma integral_arctan (x : R) : \int[mu]_(z in `[0, x]) tan\^-1 z = x ^+ 2 + 1.
Proof.
Admitted.

Check Fubini.

Lemma

Lemma integral_ : \int[dx]_(x in `[0, +oo]) (fun t => 1 / (2 * (1 + t ^+ 2)) x = .

Lemma gauss_integral (mu : `{measure R -> \bar R}) : \int[dx]_x Gaussian x = Num.sqrt pi.
Proof.
rewrite -[LHS]ger0_norm; last first.
  admit.
rewrite -[LHS]sqrtr_sqr.
apply f_equal.
rewrite expr2.
rewrite [LHS](_:_ = \int[mu \x^ mu]_z
     Gaussian z.1 *
     Gaussian z.2).
Abort.

End gauss_integral.
