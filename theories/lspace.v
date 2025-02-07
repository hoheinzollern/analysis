(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import boolp reals ereal.
From HB Require Import structures.
From mathcomp Require Import classical_sets signed functions topology normedtype cardinality.
From mathcomp Require Import sequences esum measure numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import exp hoelder.

(******************************************************************************)
(*                                                                            *)
(*         LfunType mu p == type of measurable functions f such that the      *)
(*                          integral of |f| ^ p is finite                     *)
(*            LType mu p == type of the elements of the Lp space              *)
(*          mu.-Lspace p == Lp space                                          *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "mu .-Lspace p" (at level 4, format "mu .-Lspace  p").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition finite_norm d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (f : T -> R) :=
  ('N[ mu ]_p [ f ] < +oo)%E.

HB.mixin Record isLfun d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E) (f : T -> R)
  of @MeasurableFun d _ T R f := {
  lfuny : finite_norm mu p f
}.

#[short(type=LfunType)]
HB.structure Definition Lfun d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E) :=
  {f of @MeasurableFun d _ T R f & isLfun d T R mu p p1 f}.

Arguments lfuny {d} {T} {R} {mu} {p} _.
#[global] Hint Resolve lfuny : core.
#[global] Hint Extern 0 (@LfunType _ _ _ _ _) =>
  solve [apply: lfuny] : core.

Section Lfun_canonical.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E).

HB.instance Definition _ := gen_eqMixin (LfunType mu p1).
HB.instance Definition _ := gen_choiceMixin (LfunType mu p1).

End Lfun_canonical.

Section Lequiv.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E).

Definition Lequiv (f g : LfunType mu p1) := `[< f = g %[ae mu] >].

Let Lequiv_refl : reflexive Lequiv.
Proof.
by move=> f; exact/asboolP/(filterS _ (ae_eq_refl mu setT (EFin \o f))).
Qed.

Let Lequiv_sym : symmetric Lequiv.
Proof.
by move=> f g; apply/idP/idP => /asboolP h; apply/asboolP/ae_eq_sym.
Qed.

Let Lequiv_trans : transitive Lequiv.
Proof.
by move=> f g h /asboolP gf /asboolP fh; apply/asboolP/(ae_eq_trans gf fh).
Qed.

Canonical Lequiv_canonical :=
  EquivRel Lequiv Lequiv_refl Lequiv_sym Lequiv_trans.

Local Open Scope quotient_scope.

Definition LspaceType := {eq_quot Lequiv}.
Canonical LspaceType_quotType := [the quotType _ of LspaceType].
Canonical LspaceType_eqType := [the eqType of LspaceType].
Canonical LspaceType_choiceType := [the choiceType of LspaceType].
Canonical LspaceType_eqQuotType := [the eqQuotType Lequiv of LspaceType].

Lemma LequivP (f g : LfunType mu p1) :
  reflect (f = g %[ae mu]) (f == g %[mod LspaceType]).
Proof. by apply/(iffP idP); rewrite eqmodE// => /asboolP. Qed.

Record LType := MemLType { Lfun_class : LspaceType }.
Coercion LfunType_of_LType (f : LType) : LfunType mu p1 :=
  repr (Lfun_class f).

End Lequiv.

Section Lspace.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.

Definition Lspace p (p1 : (1 <= p)%E) := [set: LType mu p1].
Arguments Lspace : clear implicits.

Lemma LType1_integrable (f : LType mu (@lexx _ _ 1%E)) : mu.-integrable setT (EFin \o f).
Proof.
apply/integrableP; split; first exact/EFin_measurable_fun.
have := lfuny _ f.
rewrite /finite_norm unlock /Lnorm ifF ?oner_eq0// invr1 poweRe1; last first.
  by apply integral_ge0 => x _; rewrite lee_fin powRr1//.
by under eq_integral => i _ do rewrite powRr1//.
Qed.

Let le12 : (1 <= 2%:E :> \bar R)%E.
rewrite lee_fin.
rewrite (ler_nat _ 1 2).
by [].
Qed.

Lemma LType2_integrable_sqr (f : LType mu le12) :
  mu.-integrable [set: T] (EFin \o (fun x => f x ^+ 2)).
Proof.
apply/integrableP; split.
  exact/EFin_measurable_fun/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x ^+ 2)%R _ f).
rewrite (@lty_poweRy _ _ (2^-1))//.
rewrite (le_lt_trans _ (lfuny _ f))//.
rewrite unlock /Lnorm ifF ?gt_eqF//.
rewrite gt0_ler_poweR//.
- by rewrite in_itv/= integral_ge0// leey.
- rewrite in_itv/= leey integral_ge0// => x _.
  by rewrite lee_fin powR_ge0.
rewrite ge0_le_integral//.
- apply: measurableT_comp => //.
  exact/EFin_measurable_fun/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x ^+ 2)%R _ f).
- by move=> x _; rewrite lee_fin powR_ge0.
- exact/EFin_measurable_fun/(@measurableT_comp _ _ _ _ _ _ (fun x : R => x `^ 2)%R)/measurableT_comp.
- by move=> t _/=; rewrite lee_fin normrX powR_mulrn.
Qed.

End Lspace.
Notation "mu .-Lspace p" := (@Lspace _ _ _ mu p) : type_scope.

(* move to hoelder.v *)
Section conjugate.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).
Hypothesis (p1 : (1 <= p)%E).

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Definition conjugate :=
  match p with
  | r%:E => [get q : R | r^-1 + q^-1 = 1]%:E
  | +oo  => 1
  | -oo  => 0
  end.

Lemma conjugateE :
  conjugate = if p is r%:E then (r * (r-1)^-1)%:E
              else if p == +oo then 1 else 0.
Proof.
rewrite /conjugate.
move: p1.
case: p => [r|//=|//].
rewrite lee_fin => r1.
have r0 : r != 0%R by rewrite gt_eqF// (lt_le_trans _ r1).
congr (_%:E).
apply: get_unique.
  by rewrite invf_div mulrBl divff// mul1r addrCA subrr addr0.
move=> /= y h0.
suffices -> : y = (1 - r^-1)^-1.
  by rewrite -(mul1r r^-1) -{1}(divff r0) -mulrBl invf_div.
by rewrite -h0 -addrAC subrr add0r invrK.
Qed.

End conjugate.


Section lfun_pred.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R).

Definition finlfun : {pred _ -> _} := mem [set f | finite_norm mu p f].
Definition lfun : {pred _ -> _} := [predI @mfun _ _ T R & finlfun].
Definition lfun_key : pred_key lfun. Proof. exact. Qed.
Canonical lfun_keyed := KeyedPred lfun_key.
Lemma sub_lfun_mfun : {subset lfun <= mfun}. Proof. by move=> x /andP[]. Qed.
Lemma sub_lfun_finlfun : {subset lfun <= finlfun}. Proof. by move=> x /andP[]. Qed.
End lfun_pred.


Lemma minkowskie :
forall [d : measure_display] [T : measurableType d] [R : realType] 
  (mu : measure T R) [f g : T -> R] [p : \bar R],
measurable_fun [set: T] f ->
measurable_fun [set: T] g ->
(1 <= p)%E -> ('N[mu]_p[(f \+ g)%R] <= 'N[mu]_p[f] + 'N[mu]_p[g])%E.
(* TODO: Jairo is working on this *)
Admitted.


Section lfun.
Context d (T : measurableType d) (R : realType).
Variables (mu : {measure set T -> \bar R}) (p : \bar R) (p1 : (1 <= p)%E).

Notation lfun := (@lfun _ T R mu p).
Section Sub.
Context (f : T -> R) (fP : f \in lfun).
Definition lfun_Sub1_subproof :=
  @isMeasurableFun.Build d _ T R f (set_mem (sub_lfun_mfun fP)).
#[local] HB.instance Definition _ := lfun_Sub1_subproof.
Definition lfun_Sub2_subproof :=
  @isLfun.Build d T R mu p p1 f (set_mem (sub_lfun_finlfun fP)).

Import HBSimple.

#[local] HB.instance Definition _ := lfun_Sub2_subproof.
Definition lfun_Sub : LfunType mu p1 := f.
End Sub.

Lemma lfun_rect (K : LfunType mu p1 -> Type) :
  (forall f (Pf : f \in lfun), K (lfun_Sub Pf)) -> forall u, K u.
Proof.
move=> Ksub [f [[Pf1] [Pf2]]].
have Pf : f \in lfun by apply/andP; rewrite ?inE.
have -> : Pf1 = set_mem (sub_lfun_mfun Pf) by [].
have -> : Pf2 = set_mem (sub_lfun_finlfun Pf) by [].
exact: Ksub.
Qed.

Lemma lfun_valP f (Pf : f \in lfun) : lfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ := isSub.Build _ _ (LfunType mu p1) lfun_rect lfun_valP.

Lemma lfuneqP (f g : LfunType mu p1) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of LfunType mu p1 by <:].

Import numFieldNormedType.Exports.

Lemma lfuny0 : finite_norm mu p (cst 0).
Proof. by rewrite /finite_norm Lnorm0. Qed.

HB.instance Definition _ := @isLfun.Build d T R mu p p1 (cst 0) lfuny0.

Lemma mfunP (f : {mfun T >-> R}) : (f : T -> R) \in mfun.
Proof. exact: valP. Qed.

Lemma lfunP (f : LfunType mu p1) : (f : T -> R) \in lfun.
Proof. exact: valP. Qed.

Lemma mfun_scaler_closed : scaler_closed (@mfun _ _ T R).
Proof. move=> a/= f; rewrite !inE; exact: measurable_funM. Qed.

HB.instance Definition _ := GRing.isScaleClosed.Build _ _ (@mfun _ _ T R)
  mfun_scaler_closed.
HB.instance Definition _ := [SubZmodule_isSubLmodule of {mfun T >-> R} by <:].

Lemma LnormZ (f : LfunType mu p1) a :
  ('N[mu]_p[a \*: f] = `|a|%:E * 'N[mu]_p[f])%E.
Proof.
rewrite unlock /Lnorm.
move: p p1 f.
case=> //[r r1 f|].
  rewrite gt_eqF ?(lt_le_trans ltr01)//.
  under eq_integral => x _/= do rewrite -mulr_algl scaler1 normrM powRM ?EFinM//.
  rewrite integralZl//; last first.
    apply /integrableP; split.
      apply: measurableT_comp => //.
      rewrite (_ : (fun x : T => `|f x| `^ r) = (@powR R)^~ r \o normr \o f)//.
      by repeat apply: measurableT_comp => //.
    apply: (@lty_poweRy _ _ r^-1).
      by rewrite gt_eqF// invr_gt0 ?(lt_le_trans ltr01).
    have -> : ((\int[mu]_x `|(`|f x| `^ r)%:E|) `^ r^-1 = 'N[mu]_r%:E[f])%E.
      rewrite unlock /Lnorm gt_eqF ?(lt_le_trans ltr01)//.
      by under eq_integral => x _ do rewrite gee0_abs ?lee_fin ?powR_ge0//.
    exact: (lfuny r1 f).
  rewrite poweRM ?integral_ge0=> //[||x _]; rewrite ?lee_fin ?powR_ge0//.
  by rewrite poweR_EFin -powRrM mulfV ?gt_eqF ?(lt_le_trans ltr01)// powRr1.
move=> p0 f.
case: ifP => mu0. admit.
by rewrite mule0.
Admitted.

Lemma lfun_submod_closed : submod_closed (lfun).
Proof.
split.
  rewrite -[0]/(cst 0). exact: lfunP.
move=> a/= f g fP gP.
rewrite -[f]lfun_valP -[g]lfun_valP.
move: (lfun_Sub _) (lfun_Sub _) => {fP} f {gP} g.
rewrite !inE rpredD ?rpredZ ?mfunP//=.
apply: mem_set => /=.
rewrite /finite_norm.
apply: (le_lt_trans (minkowskie _ _ _ _)) => //=.
  suff: a *: (g : T -> R) \in mfun by exact: set_mem.
  by rewrite rpredZ//; exact: mfunP.
rewrite lte_add_pinfty//; last exact: lfuny.
by rewrite LnormZ lte_mul_pinfty//; exact: lfuny.
Qed.

HB.instance Definition _ := GRing.isSubmodClosed.Build _ _ lfun
  lfun_submod_closed.
HB.instance Definition _ := [SubChoice_isSubLmodule of LfunType mu p1 by <:].

End lfun.


Section Lspace_norm.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.
Variable (p : \bar R) (p1 : (1 <= p)%E).

(* 0 - + should come with proofs that they are in LfunType mu p *)

Notation ty := (LfunType mu p1).
Definition nm f := fine ('N[mu]_p[f]).

Lemma finite_norm_fine (f : ty) : (nm f)%:E = 'N[mu]_p[f].
Proof. 
by rewrite /nm fineK// fin_numElt (lt_le_trans ltNy0) ?Lnorm_ge0//=; exact: lfuny.
Qed.

(* HB.instance Definition _ := GRing.Zmodule.on ty. *)

(* measurable_fun setT f -> measurable_fun setT g -> (1 <= p)%R *)

(* Notation ty := (LfunType mu p%:E). *)
(* Definition nm (f : ty) := fine ('N[mu]_p%:E[f]). *)

(* HB.instance Definition _ := GRing.Zmodule.on ty. *)

Lemma ler_Lnorm_add (f g : ty) :
  nm (f + g) <= nm f + nm g.
Proof. by rewrite -lee_fin EFinD !finite_norm_fine minkowskie. Qed.

Lemma natmulfctE (U : pointedType) (K : ringType) (f : U -> K) n :
  f *+ n = (fun x => f x *+ n).
Proof. by elim: n => [//|n h]; rewrite funeqE=> ?; rewrite !mulrSr h. Qed.

Lemma LnormN (f : ty) : nm (\-f) = nm f.
Proof. by rewrite /nm oppr_Lnorm. Qed.

Lemma enatmul_ninfty (n : nat) : (-oo *+ n.+1 = -oo :> \bar R)%E \/ (-oo *+ n.+1 = +oo :> \bar R)%E.
Proof. by elim: n => //=[|n []->]; rewrite ?addNye; left. Qed.

Lemma Lnorm_natmul (f : ty) k : nm (f *+ k) = nm f *+ k.
Proof.
apply/EFin_inj; rewrite finite_norm_fine -scaler_nat LnormZ normr_nat.
by rewrite -[in RHS]mulr_natl EFinM finite_norm_fine.
Qed.


HB.about Num.Zmodule_isSemiNormed.Build.

(* TODO : fix the definition *)
HB.instance Definition _ :=
  @Num.Zmodule_isSemiNormed.Build R (LfunType mu p1)
     nm ler_Lnorm_add Lnorm_natmul LnormN.

(* todo: add equivalent of mx_normZ and HB instance *)


(* TODO: move to hoelder *)

Lemma nm_eq0 (f : ty) : nm f = 0 -> f = 0 %[ae mu].
Proof.
rewrite /nm=> /eqP; rewrite -eqe=> /eqP; rewrite finite_norm_fine=> /Lnorm_eq0_eq0.
by apply; rewrite (lt_le_trans _ p1).
Qed.


End Lspace_norm.

Section Lspace_inclusion.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.

Lemma Lspace_inclusion (p q : R) (p1 : 1 <= p) (q1 : (1 <= q%:E)%E) :
  (p <= q) -> forall (f : LfunType mu q1), finite_norm mu (p%:E) f.
Proof.
(* move=> pleq f. *)
(* have := lfuny q1 f. *)
(* rewrite /finite_norm. *)
(* pose r := [get x : R | p = q * x] : R. *)
(* pose r' := [get x : R | r^-1 + x^-1 = 1] : R. *)
(* have := (@hoelder _ _ _ mu (fun x => `|f x| `^ p) (cst 1)%R r r'). *)
(* rewrite (_ : ((fun x : T => `|f x| `^ p) \* cst 1)%R = (fun x : T => `|f x| `^ p)); last first. *)
(*   by rewrite -fctM mulr1. *)

(* have /=r := conjugate q. *)
(* have h : forall h : p < +oo, exists r, q = p * r /\ 1 <= r. *)
(*   exists (q * ((fine p)^-1)%:E). *)
(*   move: p1 q1 pleq f h. *)
(*     case q=> //[r|]. *)
(*       case p=> //=t t1 r1. *)
(*       rewrite -!EFinM -mulrCA divff ?(gt_eqF (lt_le_trans ltr01 _))// mulr1 !lee_fin. *)
(*       by move=> tr _; rewrite ler_pdivlMr ?(lt_le_trans ltr01 _)// mul1r. *)
(*     case p=> //=t. *)
(*     by rewrite lee_fin=> t1 ? _ _; rewrite !gt0_mulye ?gt0_muley// lte_fin ?invr_gt0 (lt_le_trans ltr01). *)
(* move: h p1 q1 pleq f. *)
(* case p=> //=[t|]; case q=> //[r|]. *)
(*   case=>[|x rtx t1 q1 tr f]; first by rewrite ltey. *)
(*   (* hoelder *) admit. *)
(* rewrite !lee_fin => /[swap] t1 []. _ q1 _ f. *)
(* rewrite unlock /Lnorm. *)
(* move=> r[]. *)
(* case p => //=[t|]. => //=[r p1 r1 rle1 _|]. *)
(*     rewrite muleCA -EFinM. divff ?(gt_eqF (lt_le_trans ltr01 _))//. *)
(*     split; first by rewrite mule1. *)
(*     move: r1 p1 rle1; case p => /=[t||]; rewrite !lee_fin. *)
(*     - by move=> r1 t1 tr; rewrite ler_pdivlMr ?mul1r ?(lt_le_trans ltr01). *)
(*     - by move=> r1 ? rfin; rewrite gt0_mulye// lte_fin invr_gt0 (lt_le_trans ltr01). *)
(*     by rewrite leeNy_eq => _ /eqP. *)
(*   move=> p1 ?. rewrite !invr0 !mule0. leye_eq => /eqP -> _. rewrite invr0 !mule0//. case. *)
Admitted.

End Lspace_inclusion.
