From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference archimedean finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality reals fsbigop ereal topology tvs.
From mathcomp Require Import normedtype sequences real_interval esum measure.
From mathcomp Require Import lebesgue_measure numfun realfun measurable_realfun.
From mathcomp Require Import normed_module measurable_structure.

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope measure_display_scope.

Reserved Notation "{ 'nnfun' aT >-> T }"
  (at level 0, format "{ 'nnfun'  aT  >->  T }").
Reserved Notation "[ 'nnfun' 'of' f ]"
  (at level 0, format "[ 'nnfun'  'of'  f ]").
Reserved Notation "{ 'nnsfun' aT >-> T }"
  (at level 0, format "{ 'nnsfun'  aT  >->  T }").
Reserved Notation "[ 'nnsfun' 'of' f ]"
  (at level 0, format "[ 'nnsfun'  'of'  f ]").
Reserved Notation "{ 'sfun' aT >-> T }"
  (at level 0, format "{ 'sfun'  aT  >->  T }").
Reserved Notation "[ 'sfun' 'of' f ]"
  (at level 0, format "[ 'sfun'  'of'  f ]").

(* Introducing the Borel sigma-algebra for topological spaces*)
Section Topological_measurable.
Variable T : topologicalType.

Let G := @open T.

Definition measurableTop : set (set T) :=
  G.-sigma.-measurable.

Lemma measurable0T : measurableTop set0. Proof. exact: sigma_algebra0. Qed.
Lemma measurableCT : forall A, measurableTop A -> measurableTop (~` A). 
Proof. exact: sigma_algebraC. Qed.
Lemma measurable_bigcupT : forall F : (set T)^nat, (forall i, measurableTop (F i)) -> 
measurableTop (\bigcup_i (F i)). Proof. exact: sigma_algebra_bigcup. Qed.    

Definition measurableTypeTop := g_sigma_algebraType G.

End Topological_measurable.

HB.about topologicalType.

#[short(type = "measurableTopologicalType")] 
HB.structure Definition MeasurableTopological d := 
  {U of Topological U & Measurable d U}.

HB.about MeasurableTopological.

HB.instance Definition topological_isMeasurable (T : topologicalType) :
  isMeasurable default_measure_display T :=
  @isMeasurable.Build _ T (@measurableTop T)
    (@measurable0T T) (@measurableCT T) (@measurable_bigcupT T).

HB.instance Definition _ (T : topologicalType) := Measurable.on T.
HB.instance Definition _ (T : topologicalType) := Topological.on T.
(*HB.saturate topologicalType.
   HB.saturate measurableTypeTop.*)
HB.instance Definition _ (T : topologicalType) := MeasurableTopological.on T.

Axiom T: topologicalType.
Check T : measurableType default_measure_display.

Module HBSimple.

HB.structure Definition SimpleFun d d' (aT : sigmaRingType d) 
(T : measurableTopologicalType d') :=
  {f of @isMeasurableFun _ _ aT T f & @FiniteImage aT T f}.

End HBSimple.

Notation "{ 'sfun' aT >-> T }" := (@HBSimple.SimpleFun.type _ _ aT T) : form_scope.
Notation "[ 'sfun' 'of' f ]" := [the {sfun _ >-> _} of f] : form_scope.

Module HBNNSimple.
Import HBSimple.

HB.structure Definition NonNegSimpleFun
    d (aT : sigmaRingType d) (rT : realType) :=
  {f of @SimpleFun d _ aT (measurableTypeTop rT) f & @NonNegFun aT rT f}.

End HBNNSimple.

Notation "{ 'nnsfun' aT >-> T }" := (@HBNNSimple.NonNegSimpleFun.type _ aT%type T) : form_scope.
Notation "[ 'nnsfun' 'of' f ]" := [the {nnsfun _ >-> _} of f] : form_scope.

Section sfun_pred.
Context {d d'} {aT : sigmaRingType d} {T: measurableTopologicalType d'}.
Definition sfun : {pred _ -> _} := [predI (@mfun d d' aT T) & fimfun].
Definition sfun_key : pred_key sfun. Proof. exact. Qed.
Canonical sfun_keyed := KeyedPred sfun_key.
Lemma sub_sfun_mfun : {subset sfun <= mfun}. Proof. by move=> x /andP[]. Qed.
Lemma sub_sfun_fimfun : {subset sfun <= fimfun}. Proof. by move=> x /andP[]. Qed.

End sfun_pred.

Section sfun.
Context {d d'} {aT : measurableType d} {T : measurableTopologicalType d'}.
Notation Sf := {sfun aT >-> T}.
Notation sfun := (@sfun _ _ aT T).
Section Sub.
Context (f : aT -> T) (fP : f \in sfun).
Definition sfun_Sub1_subproof :=
  @isMeasurableFun.Build d d' aT T f (set_mem (sub_sfun_mfun fP)).
#[local] HB.instance Definition _ := sfun_Sub1_subproof.
Definition sfun_Sub2_subproof :=
  @FiniteImage.Build aT T f (set_mem (sub_sfun_fimfun fP)).

Import HBSimple.

#[local] HB.instance Definition _ := sfun_Sub2_subproof.
Definition sfun_Sub := [sfun of f].
End Sub.

Lemma sfun_rect (K : Sf -> Type) :
  (forall f (Pf : f \in sfun), K (sfun_Sub Pf)) -> forall u : Sf, K u.
Proof.
move=> Ksub [f [[Pf1] [Pf2]]]; have Pf : f \in sfun by apply/andP; rewrite ?inE.
have -> : Pf1 = set_mem (sub_sfun_mfun Pf) by [].
have -> : Pf2 = set_mem (sub_sfun_fimfun Pf) by [].
exact: Ksub.
Qed.

Import HBSimple.

Lemma sfun_valP f (Pf : f \in sfun) : sfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ := isSub.Build _ _ Sf sfun_rect sfun_valP.

Lemma sfuneqP (f g : {sfun aT >-> T}) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of {sfun aT >-> T} by <:].

(* NB: already in cardinality.v *)
HB.instance Definition _ x : @FImFun aT T (cst x) := FImFun.on (cst x).

Definition cst_sfun x : {sfun aT >-> T} := cst x.

Lemma cst_sfunE x : @cst_sfun x =1 cst x. Proof. by []. Qed.

End sfun.

(* a better way to refactor function stuffs *)
Lemma fctD (T : Type) (K : pzRingType) (L : lmodType K) (f g : T -> L) : f + g = f \+ g.
Proof. by []. Qed.
Lemma fctN (T : Type) (K : pzRingType) (L : lmodType K) (f : T -> L) : - f = \- f.
Proof. by []. Qed.
Lemma fctM (T : Type) (K : pzRingType) (f g : T -> K) : f * g = f \* g.
Proof. by []. Qed.
Lemma fctZ (T : Type) (K : pzRingType) (L : lmodType K) k (f : T -> L) :
   k *: f = k \*: f.
Proof. by []. Qed.
Arguments cst _ _ _ _ /.
Definition fctWE := (fctD, fctN, fctM, fctZ).

Section composition.
Context d (aT : measurableType d) (rT : realType) (T1 T2 T3 : normedModType rT).
Import HBSimple.

Lemma singleton_inter {R : realType} {D : metricType R} (x:D) : [set x] = \bigcap_(k:nat) (ball x (1/((k.+1)%:R))).
Proof.
  rewrite eqEsubset; split=> [x0 ->| y] /=. rewrite /bigcap /= => k _;
  apply: ballxx; by rewrite ltr_pdivlMr.
  rewrite /bigcap/=; apply: contraPP=> ynx; rewrite -existsNE.
  exists (Num.truncn (1/ mdist x y)). rewrite not_implyE; split => [//|].
  rewrite ballEmdist/= ltr_pdivlMr => //; have := truncnS_gt (1/mdist x y);
  rewrite ltr_pdivrMr. rewrite mdist_gt0. by apply/eqP; apply: nesym.
  by rewrite mulrC => asb bsa; have:= lt_trans asb bsa; rewrite lt_irreflexive.
Qed.

HB.about metricType.
HB.saturate metricType.

HB.instance Definition _ (R : realType) (D : metricType R) := Measurable.on D.

Axiom (R : realType) (D : metricType R).
Check D : measurableTopologicalType.

(* TODO : prove it for metric spaces, when it is doable*)
Lemma measurable1 {R : realType} {D : metricType R} (x:D) : measurable [set x].
Proof.
  rewrite singleton_inter. apply: bigcap_measurable=> [//|k _]. 
  rewrite/measurable/=/smallest/bigcap/= => A [sda osa]. apply: osa. have:= (ball_open x).

(* No choice but to do it all at the same time: 
B(X x Y) != B(X) \otimes B(Y) in the general case.*)
Lemma sfun_op (f: {sfun aT >-> T1}) (g: {sfun aT >-> T2}) (h: T1*T2 -> T3) : (fun x:aT => h (f x, g x)) \in sfun.
Proof.
  rewrite inE. apply/andP; split. all: rewrite in_setE /=.
    move=> maT W mW. rewrite /preimage/= [X in measurable X] (_:_ = \bigcup_( a in range f) \bigcup_(b in range g) 
    [set t | f t = a /\ g t = b /\ W (h (a, b))]) /bigcup.
      apply: eq_set=>t. rewrite exists2E propeqE; split=>[[_ hfgt]|exa]. exists (f t). split=> [//|/=]. 
      exists (g t). by exists t. by[]. case: exa=> a [rfa] /=. rewrite exists2E. case=> b. 
      rewrite exists2E. move=> [_ [fta [gtb habW]]]. by rewrite fta gtb.
    apply: fin_bigcup_measurable=> [//| a rfa]. apply: fin_bigcup_measurable=>[//|b rgb].
    rewrite [X in measurable X] (_:_ = (f@^-1`[set a])`&`(g@^-1`[set b]) `&`[set t | W (h(a,b)) ]).
    apply: eq_set=> x//=. by rewrite andA. apply: measurableI. apply: measurableI. 
      rewrite -(setTI (_ @^-1` [set _])); have := measurable1 a; have : measurable_fun [set:aT] f by[]; 
      by rewrite /measurable_fun=> /(_ maT [set a]).
      rewrite -(setTI (_ @^-1` [set _])); have := measurable1 b; have : measurable_fun [set:aT] g by[]; 
      by rewrite /measurable_fun=> /(_ maT [set b]).
    rewrite -(in_setE W). have[_|_] := boolP (h (a,b) \in W). by rewrite trueE. 
    rewrite falseE. rewrite [[set _ | False]] (_:_ = set0)=>//.
  
  rewrite -image_comp. apply: finite_image. 
  apply: (@sub_finite_set _ _ [set (a,b)|a in range f & b in range g]). move=> [x y] /=. 
  rewrite exists2E. case=> t [_ [ftx gty]]. exists x. by exists t. exists y. by exists t. by[].
  rewrite [X in finite_set X] (_:_ = \bigcup_(b in range g) [set (a,b) | a in range f]).
  apply: eq_set=> [[x y]]/=. rewrite ?exists2E. apply: propext; 
  split=> [[a [[x0 _] fx0a]] [b [x1 _] gx1b] axby | [b [[x0 _] gx0b]] [a [x1 _] fx1a axby]].
  exists b; split. by exists x1. exists a. by exists x0. by[].
  exists a; split. by exists x1. exists b. by exists x0. by[].
  apply: bigcup_finite=>[//| b _]. by apply: finite_image.
Qed.

End composition.

Section module.
Context d (aT : measurableType d) (rT : realType) (nT : normedModType rT).
Import HBSimple.

Lemma sfun_submod_closed : submod_closed (@sfun d aT nT).
Proof.
split=> [|k f g sf sg]. exact: (valP (cst_sfun (0:nT))).
  apply: (sfun_op (sfun_Sub sf) (sfun_Sub sg) (fun t=>k*:t.1 + t.2)).
Qed.

HB.instance Definition _ := GRing.isSubmodClosed.Build _ _ sfun
  sfun_submod_closed.
HB.instance Definition _ := [SubChoice_isSubLmodule  of {sfun aT >-> nT} by <:].

Implicit Types (f g : {sfun aT >-> nT}).

Lemma sfun0 : (0 : {sfun aT >-> nT}) =1 cst 0. Proof. by []. Qed.
Lemma sfunN f : - f =1 \- f. Proof. by []. Qed.
Lemma sfunD f g : f + g =1 f \+ g. Proof. by []. Qed.
Lemma sfunB f g : f - g =1 f \- g. Proof. by []. Qed.
Lemma sfunS k g : k*: g =1 k \*: g. Proof. by []. Qed.
Lemma sfun_sum I r (P : {pred I}) (f : I -> {sfun aT >-> nT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma sfun_prod I r (P : {pred I}) (f : I -> {sfun aT >-> nT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.

(* TODO : make these work*)
(*HB.instance Definition _ f g := MeasurableFun.copy (f \+ g) (f + g).
HB.instance Definition _ f g := MeasurableFun.copy (\- f) (- f).
HB.instance Definition _ f g := MeasurableFun.copy (f \- g) (f - g).
HB.instance Definition _ (k: rT) g := MeasurableFun.copy (k \*: g) (k *: g).*)

Import HBSimple.
Definition mindic_mod {d} {aT : measurableType d} 
{D : set aT} (mD : d.-measurable D) (z: nT) (x:aT) := (\1_D x) *: z.

(*HB.instance Definition _ (D : set aT) (mD : measurable D) (z:nT):
  @FImFun aT nT (mindic_mod mD z) := FImFun.on (mindic_mod mD z).

Definition indic_mod_sfun (D : set aT) (mD : measurable D) (z:nT) : {sfun aT >-> nT} :=
  mindic_mod mD z.*)

End module.

Lemma preimage_nnfun0 T (R : realDomainType) (f : {nnfun T >-> R}) t :
  t < 0 -> f @^-1` [set t] = set0.
Proof.
move=> t0.
by apply/preimage10 => -[x _]; apply: contraPnot t0 => <-; rewrite le_gtF.
Qed.

Lemma preimage_cstM T (R : realFieldType) (x y : R) (f : T -> R) :
  x != 0 -> (cst x \* f) @^-1` [set y] = f @^-1` [set y / x].
Proof.
move=> x0; apply/seteqP.
by split=> [z/= <-|z/= ->]; rewrite [x * _]mulrC (mulfK, divfK).
Qed.

Lemma preimage_add T (R : numDomainType) (f g : T -> R) z :
  (f \+ g) @^-1` [set z] = \bigcup_(a in f @` setT)
    ((f @^-1` [set a]) `&` (g @^-1` [set z - a])).
Proof.
apply/seteqP; split=> [x /= fgz|x [_ /= [y _ <-]] [fxfy gzf]]; last first.
  by rewrite gzf -fxfy addrC subrK.
exists (z - g x); first by exists x; rewrite // -fgz addrK.
by split; rewrite 1?subKr // -fgz addrK.
Qed.

Section simple_bounded.
Context d (T : sigmaRingType d) (R : realType) (N : normedModType R).

Import HBSimple.

Lemma simple_bounded (f : {sfun T >-> N}) : bounded_fun f.
Proof.
have /finite_seqP[r fr] := fimfunP f.
exists (fine (\big[maxe/-oo%E]_(i <- r) `|i|%:E)).
split; rewrite ?num_real// => x mx z _; apply/ltW/(le_lt_trans _ mx).
have ? : f z \in r by have := imageT f z; rewrite fr.
rewrite -[leLHS]/(fine `|f z|%:E) fine_le//.
  (* TODO: generalize the statement of bigmaxe_fin_num *)
  have := @bigmaxe_fin_num _ (map normr r) `|f z|.
  by rewrite big_map => ->//; apply/mapP; exists (f z).
by rewrite (unstable.bigmax_sup_seq _ _ (lexx _)).
Qed.

End simple_bounded.

Section nnsfun_functions.
Context d (T : measurableType d) (R : realType).

Import HBNNSimple.

Lemma cst_nnfun_subproof (x : {nonneg R}) : forall t : T, 0 <= cst x%:num t.
Proof. by move=> /=. Qed.
HB.instance Definition _ x := @isNonNegFun.Build T R (cst x%:num)
  (cst_nnfun_subproof x).

(*TODO*)
Definition cst_nnsfun (r : {nonneg R}) : {nnsfun T >-> R} := cst r%:num.

Definition nnsfun0 : {nnsfun T >-> R} := cst_nnsfun 0%:nng.

Lemma indic_nnfun_subproof (D : set T) : forall x, 0 <= (\1_D) x :> R.
Proof. by []. Qed.

HB.instance Definition _ D := @isNonNegFun.Build T R \1_D
  (indic_nnfun_subproof D).

HB.instance Definition _ D (mD : measurable D) :
   @NonNegFun T R (mindic R mD) := NonNegFun.on (mindic R mD).

End nnsfun_functions.
Arguments nnsfun0 {d T R}.

Section nnfun_bin.
Variables (T : Type) (R : numDomainType) (f g : {nnfun T >-> R}).

Lemma add_nnfun_subproof : @isNonNegFun T R (f \+ g).
Proof. by split => x; rewrite addr_ge0//; apply/fun_ge0. Qed.
HB.instance Definition _ := add_nnfun_subproof.

Lemma mul_nnfun_subproof : @isNonNegFun T R (f \* g).
Proof. by split => x; rewrite mulr_ge0//; apply/fun_ge0. Qed.
HB.instance Definition _ := mul_nnfun_subproof.

Lemma max_nnfun_subproof : @isNonNegFun T R (f \max g).
Proof. by split => x /=; rewrite /maxr; case: ifPn => _; apply: fun_ge0. Qed.
HB.instance Definition _ := max_nnfun_subproof.

End nnfun_bin.

Section nnsfun_bin.
Context d (T : measurableType d) (R : realType).
Variables f g : {nnsfun T >-> R}.

Import HBNNSimple.

HB.instance Definition _ := MeasurableFun.on (f \+ g).
Definition add_nnsfun : {nnsfun T >-> R} := f \+ g.

HB.instance Definition _ := MeasurableFun.on (f \* g).
Definition mul_nnsfun : {nnsfun T >-> R} := f \* g.

HB.instance Definition _ := MeasurableFun.on (f \max g).
Definition max_nnsfun : {nnsfun T >-> R} := f \max g.

Definition indic_nnsfun A (mA : measurable A) : {nnsfun T >-> R} := mindic R mA.

End nnsfun_bin.
Arguments add_nnsfun {d T R} _ _.
Arguments mul_nnsfun {d T R} _ _.
Arguments max_nnsfun {d T R} _ _.

Definition scale_nnsfun d (T : measurableType d) (R : realType)
    (f : {nnsfun T >-> R}) (k : R) (k0 : 0 <= k) :=
  mul_nnsfun (cst_nnsfun T (NngNum k0)) f.

Definition proj_nnsfun d (T : measurableType d) (R : realType)
    (f : {nnsfun T >-> R}) (A : set T) (mA : measurable A) :=
  mul_nnsfun f (indic_nnsfun R mA).

Section mrestrict.
Import HBNNSimple.

Lemma mrestrict d (T : measurableType d) (R : realType) (f : {nnsfun T >-> R})
  A (mA : measurable A) : f \_ A = proj_nnsfun f mA.
Proof.
apply/funext => x /=; rewrite /patch mindicE.
by case: ifP; rewrite (mulr0, mulr1).
Qed.

End mrestrict.

Section nnsfun_iter.
Context d (T : measurableType d) (R : realType) (D : set T).
Variable f : {nnsfun T >-> R}^nat.

Definition sum_nnsfun n := \big[add_nnsfun/nnsfun0]_(i < n) f i.

Import HBNNSimple.

Lemma sum_nnsfunE n t : sum_nnsfun n t = \sum_(i < n) (f i t).
Proof. by rewrite /sum_nnsfun; elim/big_ind2 : _ => [|x g y h <- <-|]. Qed.

Definition bigmax_nnsfun n := \big[max_nnsfun/nnsfun0]_(i < n) f i.

Lemma bigmax_nnsfunE n t : bigmax_nnsfun n t = \big[maxr/0]_(i < n) (f i t).
Proof. by rewrite /bigmax_nnsfun; elim/big_ind2 : _ => [|x g y h <- <-|]. Qed.

End nnsfun_iter.

Section nnsfun_cover.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable f : {nnsfun T >-> R}.

Import HBNNSimple.

Lemma nnsfun_cover : \big[setU/set0]_(i \in range f) (f @^-1` [set i]) = setT.
Proof. by rewrite fsbig_setU//= -subTset => x _; exists (f x). Qed.

Lemma nnsfun_coverT : \big[setU/set0]_(i \in [set: R]) f @^-1` [set i] = setT.
Proof.
by rewrite -(fsbig_widen (range f)) ?nnsfun_cover//= => x [_ /preimage10].
Qed.

End nnsfun_cover.

Section measure_fsbig.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType).
Variable m : {measure set T -> \bar R}.

Lemma measure_fsbig (I : choiceType) (A : set I) (F : I -> set T) :
  finite_set A ->
  (forall i, A i -> measurable (F i)) -> trivIset A F ->
  m (\big[setU/set0]_(i \in A) F i) = \sum_(i \in A) m (F i).
Proof.
move=> Afin Fm Ft.
by rewrite fsbig_finite// -measure_fin_bigcup// -bigsetU_fset_set.
Qed.

Import HBNNSimple.

Lemma additive_nnsfunr (g f : {nnsfun T >-> R}) x :
  \sum_(i \in range g) m (f @^-1` [set x] `&` (g @^-1` [set i])) =
  m (f @^-1` [set x] `&` \big[setU/set0]_(i \in range g) (g @^-1` [set i])).
Proof.
rewrite -?measure_fsbig//.
- by move=> i Ai; apply: measurableI.
- exact/trivIset_setIl/trivIset_preimage1.
- by rewrite !fsbig_finite//= big_distrr.
Qed.

Lemma additive_nnsfunl (g f : {nnsfun T >-> R}) x :
  \sum_(i \in range g) m (g @^-1` [set i] `&` (f @^-1` [set x])) =
  m (\big[setU/set0]_(i \in range g) (g @^-1` [set i]) `&` f @^-1` [set x]).
Proof. by under eq_fsbigr do rewrite setIC; rewrite setIC additive_nnsfunr. Qed.

End measure_fsbig.

Section mulem_ge0.
Local Open Scope ereal_scope.

Let mulef_ge0 (R : realDomainType) x (f : R -> \bar R) :
  0 <= f x -> ((x < 0)%R -> f x = 0) -> 0 <= x%:E * f x.
Proof.
case: (ltP x 0%R) => [x_lt0 ? ->|x_ge0 fx_ge0 _] //; last exact: mule_ge0.
by rewrite mule0.
Qed.

Lemma nnfun_muleindic_ge0 d (T : sigmaRingType d) (R : realDomainType)
  (f : {nnfun T >-> R}) r z : 0 <= r%:E * (\1_(f @^-1` [set r]) z)%:E.
Proof.
apply: (@mulef_ge0 _ _ (fun r => (\1_(f @^-1` [set r]) z)%:E)).
  by rewrite lee_fin// indicE.
by move=> r0; rewrite preimage_nnfun0// indic0.
Qed.

Lemma mulemu_ge0 d (T : sigmaRingType d) (R : realType)
    (mu : {measure set T -> \bar R}) x (A : R -> set T) :
  ((x < 0)%R -> A x = set0) -> 0 <= x%:E * mu (A x).
Proof.
by move=> xA; rewrite (@mulef_ge0 _ _ (mu \o _))//= => /xA ->; rewrite measure0.
Qed.
Global Arguments mulemu_ge0 {d T R mu x} A.

Import HBNNSimple.

Lemma nnsfun_mulemu_ge0 d (T : sigmaRingType d) (R : realType)
    (mu : {measure set T -> \bar R}) (f : {nnsfun T >-> R}) x :
  0 <= x%:E * mu (f @^-1` [set x]).
Proof.
by apply: (mulemu_ge0 (fun x => f @^-1` [set x])); exact: preimage_nnfun0.
Qed.

End mulem_ge0.

