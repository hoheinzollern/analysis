(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From HB Require Import structures.
From mathcomp Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import reals ereal interval_inference topology normedtype sequences.
From mathcomp Require Import derive esum measure exp numfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral kernel probability.
From mathcomp Require Import independence.

Reserved Notation "' P [ A | B ]".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section independent_events.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.

Lemma sub_independent_events (I : choiceType) (A B : set I) (E : I -> set T) :
  A `<=` B -> independent_events P B E -> independent_events P A E.
Proof.
by move=> AB [mE h]; split=> [i /AB/mE//|C CA]; apply: h; apply: subset_trans AB.
Qed.

Definition kwise_independent (I : choiceType) (A : set I) (E : I -> set T) k :=
  (forall i, A i -> measurable (E i)) /\
  forall B : {fset I}, [set` B] `<=` A -> (#|` B | <= k)%nat ->
    P (\bigcap_(i in [set` B]) E i) = \prod_(i <- B) P (E i).

Lemma sub_kwise_independent (I : choiceType) (A B : set I) (E : I -> set T) k :
  A `<=` B -> kwise_independent B E k -> kwise_independent A E k.
Proof.
by move=> AB [mE h]; split=> [i /AB/mE//|C CA]; apply: h; apply: subset_trans AB.
Qed.

Lemma mutual_indep_is_kwise_indep (I : choiceType) (A : set I) (E : I -> set T) k :
  independent_events P A E -> kwise_independent A E k.
Proof.
rewrite /independent_events /kwise_independent.
move=> [mE miE]; split=> // B BleA _.
exact: miE.
Qed.

Lemma nwise_indep_is_mutual_indep (I : choiceType) (A : {fset I}) (E : I -> set T) n :
  #|` A | = n -> kwise_independent [set` A] E n -> independent_events P [set` A] E.
Proof.
rewrite /independent_events /kwise_independent.
move=> nA [mE miE]; split=> // B BleA.
apply: miE => //; rewrite -nA fsubset_leq_card//.
by apply/fsubsetP => x xB; exact: (BleA x).
Qed.

Lemma mutually_independent_weak (I : choiceType) (E : I -> set T) (B : set I) :
  (forall b, ~ B b -> E b = setT) ->
  independent_events P [set: I] E <->
  independent_events P B E.
Proof.
move=> BE; split; first exact: sub_independent_events.
move=> [mE h]; split=> [i _|C _].
  by have [Bi|Bi] := pselect (B i); [exact: mE|rewrite BE].
have [CB|CB] := pselect ([set` C] `<=` B); first by rewrite h.
rewrite -(setIT [set` C]) -(setUv B) setIUr bigcap_setU.
rewrite (@bigcapT _ _ (_ `&` ~` _)) ?setIT//; last by move=> i [_ /BE].
have [D CBD] : exists D : {fset I}, [set` C] `&` B = [set` D].
  exists (fset_set ([set` C] `&` B)).
  by rewrite fset_setK//; exact: finite_setIl.
rewrite CBD h; last first.
  rewrite -CBD; exact: subIsetr.
rewrite [RHS]fsbig_seq//= [RHS](fsbigID B)//=.
rewrite [X in _ * X](_ : _ = 1) ?mule1; last first.
  by rewrite fsbig1// => m [_ /BE] ->; rewrite probability_setT.
by rewrite CBD -fsbig_seq.
Qed.

Lemma kwise_independent_weak (I : choiceType) (E : I -> set T) (B : set I) k :
  (forall b, ~ B b -> E b = setT) ->
  kwise_independent [set: I] E k <->
  kwise_independent B E k.
Proof.
move=> BE; split; first exact: sub_kwise_independent.
move=> [mE h]; split=> [i _|C _ Ck].
  by have [Bi|Bi] := pselect (B i); [exact: mE|rewrite BE].
have [CB|CB] := pselect ([set` C] `<=` B); first by rewrite h.
rewrite -(setIT [set` C]) -(setUv B) setIUr bigcap_setU.
rewrite (@bigcapT _ _ (_ `&` ~` _)) ?setIT//; last by move=> i [_ /BE].
have [D CBD] : exists D : {fset I}, [set` C] `&` B = [set` D].
  exists (fset_set ([set` C] `&` B)).
  by rewrite fset_setK//; exact: finite_setIl.
rewrite CBD h; last 2 first.
  - rewrite -CBD; exact: subIsetr.
  - rewrite (leq_trans _ Ck)// fsubset_leq_card// -(set_fsetK D) -(set_fsetK C).
    by rewrite -fset_set_sub// -CBD; exact: subIsetl.
rewrite [RHS]fsbig_seq//= [RHS](fsbigID B)//=.
rewrite [X in _ * X](_ : _ = 1) ?mule1; last first.
  by rewrite fsbig1// => m [_ /BE] ->; rewrite probability_setT.
by rewrite CBD -fsbig_seq.
Qed.

Lemma kwise_independent_weak01 E1 E2 :
  kwise_independent [set: nat] (bigcap2 E1 E2) 2%N <->
  kwise_independent [set 0%N; 1%N] (bigcap2 E1 E2) 2%N.
Proof.
apply: kwise_independent_weak.
by move=> n /= /not_orP[/eqP /negbTE -> /eqP /negbTE ->].
Qed.

Lemma independent_events_weak' (I : choiceType) (E : I -> set T) (B : set I) :
  (forall b, ~ B b -> E b = setT) ->
  independent_events P [set: I] E <->
  independent_events P B E.
Proof.
move=> BE; split; first exact: sub_independent_events.
move=> [mE h]; split=> [i _|C CI].
  by have [Bi|Bi] := pselect (B i); [exact: mE|rewrite BE].
have [CB|CB] := pselect ([set` C] `<=` B); first by rewrite h.
rewrite -(setIT [set` C]) -(setUv B) setIUr bigcap_setU.
rewrite (@bigcapT _ _ (_ `&` ~` _)) ?setIT//; last by move=> i [_ /BE].
have [D CBD] : exists D : {fset I}, [set` C] `&` B = [set` D].
  exists (fset_set ([set` C] `&` B)).
  by rewrite fset_setK//; exact: finite_setIl.
rewrite CBD h; last first.
  - rewrite -CBD; exact: subIsetr.
rewrite [RHS]fsbig_seq//= [RHS](fsbigID B)//=.
rewrite [X in _ * X](_ : _ = 1) ?mule1; last first.
  by rewrite fsbig1// => m [_ /BE] ->; rewrite probability_setT.
by rewrite CBD -fsbig_seq.
Qed.

Definition pairwise_independent E1 E2 :=
  kwise_independent [set 0; 1]%N (bigcap2 E1 E2) 2.

Lemma pairwise_independentM_old (E1 E2 : set T) :
  pairwise_independent E1 E2 <->
  [/\ d.-measurable E1, d.-measurable E2 & P (E1 `&` E2) = P E1 * P E2].
Proof.
split.
- move=> [mE1E2 /(_ [fset 0%N; 1%N]%fset)].
  rewrite bigcap_fset !big_fsetU1 ?inE//= !big_seq_fset1/= => ->; last 2 first.
  + by rewrite set_fsetU !set_fset1; exact: subset_refl.
  + rewrite cardfs2//.
  split => //.
  + by apply: (mE1E2 0%N) => /=; left.
  + by apply: (mE1E2 1%N) => /=; right.
- move=> [mE1 mE2 E1E2M].
  split => //=.
  + by move=> [| [| [|]]]//=.
  + move=> B _; have [B0|B0] := boolP (0%N \in B); last first.
      have [B1|B1] := boolP (1%N \in B); last first.
        rewrite big1_fset; last first.
          move=> k kB _; rewrite /bigcap2.
          move: kB B0; case: ifPn => [/eqP -> ->//|k0 kB B0].
          move: kB B1; case: ifPn => [/eqP -> ->//|_ _ _].
          by rewrite probability_setT.
        rewrite bigcapT ?probability_setT// => k/= kB.
        move: kB B0 B1; case: ifPn => [/eqP -> ->//|k0].
        by case: ifPn => [/eqP -> ->|].
      rewrite (bigcap_setD1 1%N _ [set` B])//=.
      rewrite bigcapT ?setIT; last first.
        move=> k [/= kB /eqP /negbTE ->].
        by move: kB B0; case: ifPn => [/eqP -> ->|].
      rewrite (big_fsetD1 1%N)//= big1_fset ?mule1// => k.
      rewrite !inE => /andP[/negbTE -> kB] _.
      move: kB B0; case: ifPn => [/eqP -> ->//|k0 kB B0].
      by rewrite probability_setT.
    rewrite (bigcap_setD1 0%N _ [set` B])//.
    have [B1|B1] := boolP (1%N \in B); last first.
      rewrite bigcapT ?setIT; last first.
        move=> k [/= kB /eqP /negbTE ->].
        by move: kB B1; case: ifPn => [/eqP -> ->|].
      rewrite (big_fsetD1 0%N)//= big1_fset ?mule1// => k.
      rewrite !inE => /andP[/negbTE -> kB] _.
      move: kB B1; case: ifPn => [/eqP -> ->//|k1 kB B1].
      by rewrite probability_setT.
    rewrite (bigcap_setD1 1%N _ ([set` B] `\ 0%N))// bigcapT ?setIT; last first.
      by move=> n/= [[nB]/eqP/negbTE -> /eqP/negbTE ->].
    rewrite E1E2M (big_fsetD1 0%N)//= (big_fsetD1 1%N)/=; last by rewrite !inE B1.
    rewrite big1_fset ?mule1//= => k.
    rewrite !inE => -/and3P[/negbTE -> /negbTE -> kB] _;
    by rewrite probability_setT.
Qed.

Lemma pairwise_independentM (E1 E2 : set T) :
  pairwise_independent E1 E2 <->
  [/\ d.-measurable E1, d.-measurable E2 & P (E1 `&` E2) = P E1 * P E2].
Proof.
split.
- move=> [mE1E2 /(_ [fset 0%N; 1%N]%fset)].
  rewrite bigcap_fset !big_fsetU1 ?inE//= !big_seq_fset1/= => ->; last 2 first.
  + by rewrite set_fsetU !set_fset1; exact: subset_refl.
  + by rewrite cardfs2.
  split => //.
  + by apply: (mE1E2 0%N) => /=; left.
  + by apply: (mE1E2 1%N) => /=; right.
- move=> [mE1 mE2 E1E2M].
  rewrite /pairwise_independent.
  split.
  + by move=> [| [| [|]]]//=.
  + move=> B B01 B2.
    have [B_set0|B_set0|B_set1|B_set01] := subset_set2 B01.
    * rewrite B_set0.
      move: B_set0 => /eqP; rewrite set_fset_eq0 => /eqP ->.
      by rewrite big_nil bigcap_set0 probability_setT.
    * rewrite B_set0 bigcap_set1 /=.
      by rewrite fsbig_seq//= B_set0 fsbig_set1/=.
    * rewrite B_set1 bigcap_set1 /=.
      by rewrite fsbig_seq//= B_set1 fsbig_set1/=.
    * rewrite B_set01 bigcap_setU1 bigcap_set1/=.
      rewrite fsbig_seq//= B_set01.
      rewrite fsbigU//=; last first.
        by move=> n [/= ->].
      by rewrite !fsbig_set1//=.
Qed.

Lemma pairwise_independent_setC (E1 E2 : set T) :
  pairwise_independent E1 E2 -> pairwise_independent E1 (~` E2).
Proof.
rewrite/pairwise_independent.
move/pairwise_independentM=> [mE1 mE2 h].
apply/pairwise_independentM; split=> //.
- exact: measurableC.
- rewrite -setDE measureD//; last first.
    exact: (le_lt_trans (probability_le1 P mE1) (ltry _)).
  rewrite probability_setC// muleBr// ?mule1 -?h//.
  by rewrite fin_num_measure.
Qed.

Lemma pairwise_independentC (E1 E2 : set T) :
  pairwise_independent E1 E2 -> pairwise_independent E2 E1.
Proof.
rewrite/pairwise_independent/kwise_independent; move=> [mE1E2 /(_ [fset 0%N; 1%N]%fset)].
rewrite bigcap_fset !big_fsetU1 ?inE//= !big_seq_fset1/= => h.
split.
- case=> [_|[_|]]//=.
  + by apply: (mE1E2 1%N) => /=; right.
  + by apply: (mE1E2 0%N) => /=; left.
- move=> B B01 B2.
  have [B_set0|B_set0|B_set1|B_set01] := subset_set2 B01.
  + rewrite B_set0.
    move: B_set0 => /eqP; rewrite set_fset_eq0 => /eqP ->.
    by rewrite big_nil bigcap_set0 probability_setT.
  + rewrite B_set0 bigcap_set1 /=.
    by rewrite fsbig_seq//= B_set0 fsbig_set1/=.
  + rewrite B_set1 bigcap_set1 /=.
    by rewrite fsbig_seq//= B_set1 fsbig_set1/=.
  + rewrite B_set01 bigcap_setU1 bigcap_set1/=.
    rewrite fsbig_seq//= B_set01.
    rewrite fsbigU//=; last first.
    by move=> n [/= ->].
    rewrite !fsbig_set1//= muleC setIC.
    apply: h.
    * by rewrite set_fsetU !set_fset1; exact: subset_refl.
    * by rewrite cardfs2.
Qed.
(* ale: maybe interesting is thm 8.3 and exercise 8.6 from shoup/ntb at this point *)

End independent_events.

Section conditional_probability.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

Definition conditional_probability (P : probability T R) E1 E2 := (fine (P (E1 `&` E2)) / fine (P E2))%:E.
Local Notation "' P [ E1 | E2 ]" := (conditional_probability P E1 E2).

Lemma conditional_independence (P : probability T R) E1 E2 :
  P E2 != 0 -> pairwise_independent P E1 E2 -> 'P [ E1 | E2 ] = P E1.
Proof.
move=> PE2ne0 iE12.
have /= mE1 := (iE12.1 0%N).
have /= mE2 := (iE12.1 1%N).
rewrite/conditional_probability.
have [_ _ ->] := (pairwise_independentM _ _ _).1 iE12.
rewrite fineM ?fin_num_measure//; [|apply: mE1; left=>//|apply: mE2; right=>//].
rewrite -mulrA mulfV ?mulr1 ?fineK// ?fin_num_measure//; first by apply: mE1; left.
by rewrite fine_eq0// fin_num_measure//; apply: mE2; right.
Qed.

(* TODO (klenke thm 8.4): if P B > 0 then 'P[.|B] is a probability measure *)

Lemma conditional_independent_is_pairwise_independent (P : probability T R) E1 E2 :
  d.-measurable E1 -> d.-measurable E2 ->
  P E2 != 0 ->
    'P[E1 | E2] = P E1 -> pairwise_independent P E1 E2.
Proof.
rewrite /conditional_probability/pairwise_independent=> mE1 mE2 pE20 pE1E2.
split.
- by case=> [|[|]]//=.
- move=> B B01 B2; have [B_set0|B_set0|B_set1|B_set01] := subset_set2 B01.
  + rewrite B_set0.
    move: B_set0 => /eqP; rewrite set_fset_eq0 => /eqP ->.
    by rewrite big_nil bigcap_set0 probability_setT.
  + rewrite B_set0 bigcap_set1 /=.
    by rewrite fsbig_seq//= B_set0 fsbig_set1/=.
  + rewrite B_set1 bigcap_set1 /=.
    by rewrite fsbig_seq//= B_set1 fsbig_set1/=.
  + rewrite B_set01 bigcap_setU1 bigcap_set1/=.
    rewrite fsbig_seq//= B_set01.
    rewrite fsbigU//=; last first.
    by move=> n [/= ->].
    rewrite !fsbig_set1//= -pE1E2 -{2}(@fineK _ (P E2)).
    rewrite -EFinM -mulrA mulVf ?mulr1 ?fine_eq0// ?fineK//.
    all: by apply: fin_num_measure => //; apply: measurableI.
Qed.

Lemma conditional_independentC (P : probability T R) E1 E2 :
  d.-measurable E1 -> d.-measurable E2 ->
  P E1 != 0 -> P E2 != 0 ->
    reflect ('P[E1 | E2] == P E1) ('P[E2 | E1] == P E2).
Proof.
move=> mE1 mE2 pE10 pE20.
apply/(iffP idP)=>/eqP.
+ move/(@conditional_independent_is_pairwise_independent _ _ _ mE2 mE1 pE10).
  move/pairwise_independentC.
  by move/(conditional_independence pE20)/eqP.
+ move/(@conditional_independent_is_pairwise_independent _ _ _ mE1 mE2 pE20).
  move/pairwise_independentC.
  by move/(conditional_independence pE10)/eqP.
Qed.

(* Lemma summation (I : choiceType) (A : {fset I}) E F (P : probability T R) : *)
(*   (* the sets are disjoint *) *)
(*   P (\bigcap_(i in [set` A]) F i) = 1 -> P E = \prod_(i <- A) ('P [E | F i] * P (F i)). *)
(* Proof. *)
(* move=> pF1. *)

Lemma bayes (P : probability T R) E F :
  d.-measurable E -> d.-measurable F ->
  'P[ E | F ] = ((fine ('P[F | E] * P E)) / (fine (P F)))%:E.
Proof.
rewrite /conditional_probability => mE mF.
have [PE0|PE0] := eqVneq (P E) 0.
  have -> : P (E `&` F) = 0.
    by apply/eqP; rewrite eq_le -{1}PE0 (@measureIl _ _ _ P E F mE mF)/= measure_ge0.
  by rewrite PE0 fine0 invr0 mulr0 mule0 mul0r.
by rewrite -{2}(@fineK _ (P E)) -?EFinM -?(mulrA (fine _)) ?mulVf ?fine_eq0 ?fin_num_measure// mul1r setIC//.
Qed.

End conditional_probability.
Notation "' P [ E1 | E2 ]" := (conditional_probability P E1 E2).

From mathcomp Require Import real_interval.

Section independent_RVs.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Local Open Scope ereal_scope.

Definition pairwise_independent_RV (X Y : {RV P >-> R}) :=
  forall s t, pairwise_independent P (X @^-1` s) (Y @^-1` t).

Lemma conditional_independent_RV (X Y : {RV P >-> R}) :
  pairwise_independent_RV X Y ->
  forall s t, P (Y @^-1` t) != 0 -> 'P [X @^-1` s | Y @^-1` t] = P (X @^-1` s).
Proof.
move=> iRVXY s t PYtne0.
exact: conditional_independence.
Qed.

Definition mutually_independent_RV (I : choiceType) (A : set I) (X : I -> {RV P >-> R}) :=
  forall x_ : I -> R, independent_events P A (fun i => X i @^-1` `[(x_ i), +oo[%classic).

Definition kwise_independent_RV (I : choiceType) (A : set I) (X : I -> {RV P >-> R}) k :=
  forall x_ : I -> R, kwise_independent P A (fun i => X i @^-1` `[(x_ i), +oo[%classic) k.

Lemma nwise_indep_is_mutual_indep_RV (I : choiceType) (A : {fset I}) (X : I -> {RV P >-> R}) n :
  #|` A | = n -> kwise_independent_RV [set` A] X n -> mutually_independent_RV [set` A] X.
Proof.
rewrite/mutually_independent_RV/kwise_independent_RV=> nA kwX s.
by apply: nwise_indep_is_mutual_indep; rewrite ?nA.
Qed.

(* alternative formalization
Definition inde_RV (I : choiceType) (A : set I) (X : I -> {RV P >-> R}) :=
  forall (s : I -> set R), mutually_independent P A (fun i => X i @^-1` s i).

Definition kwise_independent_RV (I : choiceType) (A : set I) (X : I -> {RV P >-> R}) k :=
  forall (s : I -> set R), kwise_independent P A (fun i => X i @^-1` s i) k.

this should be equivalent according to wikipedia https://en.wikipedia.org/wiki/Independence_(probability_theory)#For_real_valued_random_variables
*)

(* Remark 2.15 (i) *)
Lemma prob_inde_RV (I : choiceType) (A : set I) (X : I -> {RV P >-> R}) :
  mutually_independent_RV A X ->
    forall J : {fset I}, [set` J] `<=` A ->
      forall x_ : I -> R,
        P (\bigcap_(i in [set` J]) X i @^-1` `[(x_ i), +oo[%classic) =
          \prod_(i <- J) P (X i @^-1` `[(x_ i), +oo[%classic).
Proof.
move=> iRVX J JleA x_.
apply: (iRVX _).2 => //.
Qed.

(*
Lemma mutually_independent_RV' (I : choiceType) (A : set I)
  (X : I -> {RV P >-> R}) (S : I -> set R) :
  mutually_independent_RV A X -> 
  (forall i, A i -> measurable (S i)) ->
  mutually_independent P A (fun i => X i @^-1` S i).
Proof.
move=> miX mS.
split; first by move=> i Ai; exact/measurable_sfunP/(mS i Ai).
move=> B BA.
Abort.
*)

Lemma inde_expectation (I : choiceType) (A : set I) (X : I -> {RV P >-> R}) :
  mutually_independent_RV A X ->
    forall B : {fset I}, [set` B] `<=` A ->
    'E_P[\prod_(i <- B) X i] = \prod_(i <- B) 'E_P[X i].
Proof.
move=> AX B BA.
rewrite [in LHS]unlock.
rewrite /mutually_independent_RV in AX.
rewrite /independent_events in AX.
Abort.

End independent_RVs.

Section bool_to_real.
Context d (T : measurableType d) (R : realType) (P : probability T R) (f : {mfun T >-> bool}).
Definition bool_to_real : T -> R := (fun x => x%:R) \o (f : T -> bool).

Lemma measurable_bool_to_real : measurable_fun [set: T] bool_to_real.
Proof.
rewrite /bool_to_real.
apply: measurableT_comp => //=.
exact: (@measurable_funP _ _ _ _ f).
Qed.
(* HB.about isMeasurableFun.Build. *)
HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ bool_to_real measurable_bool_to_real.

Definition btr : {RV P >-> R} := bool_to_real.

End bool_to_real.

Section bernoulli.

Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Variable p : R.
Hypothesis p01 : (0 <= p <= 1)%R.

Definition bernoulli_RV (X : {dRV P >-> bool}) :=
  distribution P X = bernoulli p.

Lemma bernoulli_RV1 (X : {dRV P >-> bool}) : bernoulli_RV X ->
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

Lemma bernoulli_RV2 (X : {dRV P >-> bool}) : bernoulli_RV X ->
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

Lemma bernoulli_expectation (X : {dRV P >-> bool}) :
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

Lemma integrable_bernoulli (X : {dRV P >-> bool}) :
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
rewrite (@varianceE _ _ _ _ (btr P X));
  [|rewrite ?[X in _ \o X]bool_RV_sqr; exact: integrable_bernoulli..].
rewrite [X in 'E_P[X]]bool_RV_sqr !bernoulli_expectation//.
by rewrite expe2 -EFinD onemMr.
Qed.

Definition is_bernoulli_trial n (X : {dRV P >-> bool}^nat) :=
  (forall i, (i < n)%nat -> bernoulli_RV (X i)) /\ independent_RVs P `I_n X.

Definition bernoulli_trial n (X : {dRV P >-> bool}^nat) : {RV P >-> R} :=
  (\sum_(i<n) (btr P (X i)))%R. (* TODO: add HB instance measurablefun sum*)

Lemma expectation_bernoulli_trial (X : {dRV P >-> bool}^nat) n :
  is_bernoulli_trial n X -> 'E_P[@bernoulli_trial n X] = (n%:R * p)%:E.
Proof.
move=> bRV. rewrite /bernoulli_trial.
transitivity ('E_P[\sum_(s <- map (btr P \o X) (iota 0 n)) s]).
  by rewrite big_map -[in RHS](subn0 n) big_mkord.
rewrite expectation_sum; last first.
  by move=> Xi; move/mapP=> [k kn] ->; apply: integrable_bernoulli; apply bRV; rewrite mem_iota leq0n in kn.
rewrite big_map -[in LHS](subn0 n) big_mkord.
transitivity (\sum_(i < n) p%:E).
  apply: eq_bigr => k _.
  rewrite bernoulli_expectation//.
  apply bRV.
  by [].
by rewrite sumEFin big_const_ord iter_addr addr0 mulrC mulr_natr.
Qed.

Definition sumrfct (s : seq {mfun T >-> R}) := (fun x => \sum_(f <- s) f x)%R.

Lemma measurable_sumrfct s : measurable_fun setT (sumrfct s).
Proof.
rewrite /sumrfct.
pose n := size s.
apply/measurable_EFinP => /=.
have -> : (EFin \o (fun x : T => (\sum_(f <- s) f x)%R)) = (fun x : T => \sum_(i < n) (s`_i x)%:E)%R.
  apply: funext => x /=.
  rewrite sumEFin.
  congr (_%:E).
  rewrite big_tnth//.
  apply: eq_bigr => i _ /=.
  by rewrite (tnth_nth 0%R).
apply: emeasurable_sum => i.
by apply/measurable_EFinP.
Qed.

HB.about isMeasurableFun.Build.
HB.instance Definition _ s :=
  isMeasurableFun.Build _ _ _ _ (sumrfct s) (measurable_sumrfct s).

Lemma sumrfctE' (s : seq {mfun T >-> R}) x :
  ((\sum_(f <- s) f) x = sumrfct s x)%R.
Proof. by rewrite/sumrfct; elim/big_ind2 : _ => //= u a v b <- <-. Qed.

Lemma bernoulli_trial_ge0 (X : {dRV P >-> bool}^nat) n : is_bernoulli_trial n X ->
  (forall t, 0 <= bernoulli_trial n X t)%R.
Proof.
move=> [bRV Xn] t.
rewrite /bernoulli_trial.
have -> : (\sum_(i < n) btr P (X i))%R = (\sum_(s <- map (btr P \o X) (iota 0 n)) s)%R.
  by rewrite big_map -[in RHS](subn0 n) big_mkord.
have -> : (\sum_(s <- [seq (btr P \o X) i | i <- iota 0 n]) s)%R t = (\sum_(s <- [seq (btr P \o X) i | i <- iota 0 n]) s t)%R.
  by rewrite sumrfctE'.
rewrite big_map.
by apply: sumr_ge0 => i _/=; rewrite /bool_to_real/= ler0n.
Qed.

(* this seems to be provable like in https://www.cs.purdue.edu/homes/spa/courses/pg17/mu-book.pdf page 65 *)
Axiom taylor_ln_le : forall (delta : R), ((1 + delta) * ln (1 + delta) >= delta + delta^+2 / 3)%R.

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

Lemma sumr_map U d' (V : measurableType d') (l : seq U) Q (f : U -> {mfun V >-> R}) (x : V) :
  ((\sum_(i <- l | Q i) f i) x = \sum_(i <- l | Q i) f i x)%R.
Proof.
elim: l; first by rewrite !big_nil.
move=> a l ih.
rewrite !big_cons.
case: ifP => aQ//=.
by rewrite -ih.
Qed.

Lemma prodr_map U d' (V : measurableType d') (l : seq U) Q (f : U -> {mfun V >-> R}) (x : V) :
  ((\prod_(i <- l | Q i) f i) x = \prod_(i <- l | Q i) f i x)%R.
Proof.
elim: l; first by rewrite !big_nil.
move=> a l ih.
rewrite !big_cons.
case: ifP => aQ//=.
by rewrite -ih.
Qed.

Lemma independent_mmt_gen_fun (X : {dRV P >-> bool}^nat) n t :
  let mmtX (i : nat) : {RV P >-> R} := expR \o t \o* (btr P (X i)) in
  independent_RVs P `I_n X -> independent_RVs P `I_n mmtX.
Proof.
Admitted. (* from Reynald's PR, independent_RVs2_comp, "when applying a function, the sigma algebra only gets smaller" *)

Lemma expectation_prod_independent_RVs (X : {RV P >-> R}^nat) n :
  independent_RVs P `I_n X ->
  'E_P[\prod_(i < n) (X i)] = \prod_(i < n) 'E_P[X i].
Proof.
Admitted.

Lemma bernoulli_trial_mmt_gen_fun (X_ : {dRV P >-> bool}^nat) n (t : R) :
  is_bernoulli_trial n X_ ->
  let X := bernoulli_trial n X_ in
  'M_X t = \prod_(i < n) 'M_(btr P (X_ i)) t.
Proof.
move=> []bRVX iRVX /=.
rewrite /bernoulli_trial/mmt_gen_fun.
pose mmtX (i : nat) : {RV P >-> R} := expR \o t \o* (btr P (X_ i)).
have iRV_mmtX : independent_RVs P `I_n mmtX.
  exact: independent_mmt_gen_fun.
transitivity ('E_P[\prod_(i < n) mmtX i])%R.
  congr ('E_P[_]).
  apply: funext => x/=.
  rewrite sumr_map mulr_suml expR_sum prodr_map.
  exact: eq_bigr.
exact: expectation_prod_independent_RVs.
Qed.

Arguments sub_countable [T U].
Arguments card_le_finite [T U].

Lemma bernoulli_mmt_gen_fun (X : {dRV P >-> bool}) (t : R) :
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

Lemma iter_mule (n : nat) (x y : \bar R) : iter n ( *%E x) y = (x ^+ n * y)%E.
Proof. by elim: n => [|n ih]; rewrite ?mul1e// [LHS]/= ih expeS muleA. Qed.

Lemma binomial_mmt_gen_fun (X_ : {dRV P >-> bool}^nat) n (t : R) :
  is_bernoulli_trial n X_ ->
  let X := bernoulli_trial n X_ : {RV P >-> R} in
  'M_X t = ((p * expR t + (1-p))`^(n%:R))%:E.
Proof.
move: p01 => /andP[p0 p1] bX/=.
rewrite bernoulli_trial_mmt_gen_fun//.
under eq_bigr => i _.
  rewrite bernoulli_mmt_gen_fun; last exact: bX.1.
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

Lemma mmt_gen_fun_expectation (X_ : {dRV P >-> bool}^nat) (t : R) n :
  (0 <= t)%R ->
  is_bernoulli_trial n X_ ->
  let X := bernoulli_trial n X_ : {RV P >-> R} in
  'M_X t <= (expR (fine 'E_P[X] * (expR t - 1)))%:E.
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

Lemma end_thm24 (X_ : {dRV P >-> bool}^nat) n (t delta : R) :
  is_bernoulli_trial n X_ ->
  (0 < delta)%R ->
  let X := @bernoulli_trial n X_ in
  let mu := 'E_P[X] in
  let t := ln (1 + delta) in
  (expR (expR t - 1) `^ fine mu)%:E *
    (expR (- t * (1 + delta)) `^ fine mu)%:E <=
    ((expR delta / (1 + delta) `^ (1 + delta)) `^ fine mu)%:E.
Proof.
move=> bX d0 /=.
rewrite -EFinM lee_fin -powRM ?expR_ge0// ge0_ler_powR ?nnegrE//.
- by rewrite fine_ge0// expectation_ge0// => x; exact: (bernoulli_trial_ge0 bX).
- by rewrite mulr_ge0// expR_ge0.
- by rewrite divr_ge0 ?expR_ge0// powR_ge0.
- rewrite lnK ?posrE ?addr_gt0// addrAC subrr add0r ler_wpM2l ?expR_ge0//.
  by rewrite -powRN mulNr -mulrN expRM lnK// posrE addr_gt0.
Qed.

(* theorem 2.4 Rajani / thm 4.4.(2) mu-book *)
Theorem bernoulli_trial_inequality1 (X_ : {dRV P >-> bool}^nat) n (delta : R) :
  is_bernoulli_trial n X_ ->
  (0 < delta)%R ->
  let X := @bernoulli_trial n X_ in
  let mu := 'E_P[X] in
  P [set i | X i >= (1 + delta) * fine mu]%R <=
  ((expR delta / ((1 + delta) `^ (1 + delta))) `^ (fine mu))%:E.
Proof.
rewrite /= => bX delta0.
set X := @bernoulli_trial n X_.
set mu := 'E_P[X].
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
Theorem bernoulli_trial_inequality2 (X : {dRV P >-> bool}^nat) (delta : R) n :
  is_bernoulli_trial n X ->
  let X' := @bernoulli_trial n X in
  let mu := 'E_P[X'] in
  (0 < n)%nat ->
  (0 < delta < 1)%R ->
  P [set i | X' i >= (1 + delta) * fine mu]%R <=
  (expR (- (fine mu * delta ^+ 2) / 3))%:E.
Proof.
move=> bX X' mu n0 /andP[delta0 _].
apply: (@le_trans _ _ (expR ((delta - (1 + delta) * ln (1 + delta)) * fine mu))%:E).
  rewrite expRM expRB (mulrC _ (ln _)) expRM lnK; last rewrite posrE addr_gt0//.
  apply: (bernoulli_trial_inequality1 bX) => //.
apply: (@le_trans _ _ (expR ((delta - (delta + delta ^+ 2 / 3)) * fine mu))%:E).
  rewrite lee_fin ler_expR ler_wpM2r//.
    by rewrite fine_ge0//; apply: expectation_ge0 => t; exact: (bernoulli_trial_ge0 bX).
  rewrite lerB//.
  exact: taylor_ln_le.
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
Theorem bernoulli_trial_inequality3 (X : {dRV P >-> bool}^nat) (delta : R) n :
  is_bernoulli_trial n X -> (0 < delta < 1)%R ->
  let X' := @bernoulli_trial n X : {RV P >-> R} in
  let mu := 'E_P[X'] in
  P [set i | X' i <= (1 - delta) * fine mu]%R <= (expR (-(fine mu * delta ^+ 2) / 2)%R)%:E.
Proof.
move=> bX /andP[delta0 delta1] /=.
set X' := @bernoulli_trial n X : {RV P >-> R}.
set mu := 'E_P[X'].
have /andP[p0 p1] := p01.
apply: (@le_trans _ _ (((expR (- delta) / ((1 - delta) `^ (1 - delta))) `^ (fine mu))%:E)).
  (* using Markov's inequality somewhere, see mu's book page 66 *)
  have H1 t : (t < 0)%R ->
    P [set i | (X' i <= (1 - delta) * fine mu)%R] = P [set i | `|(expR \o t \o* X') i|%:E >= (expR (t * (1 - delta) * fine mu))%:E].
    move=> t0; apply: congr1; apply: eq_set => x /=.
    rewrite lee_fin ger0_norm ?expR_ge0// ler_expR (mulrC _ t) -mulrA.
    by rewrite -[in RHS]ler_ndivrMl// mulrA mulVf ?lt_eqF// mul1r.
  set t := ln (1 - delta).
  have ln1delta : (t < 0)%R.
    (* TODO: lacking a lemma here *)
    rewrite -oppr0 ltrNr -lnV ?posrE ?subr_gt0// ln_gt0//.
    by rewrite invf_gt1// ?subr_gt0// ltrBlDr ltrDl.
  have {H1}-> := H1 _ ln1delta.
  apply: (@le_trans _ _ (((fine 'E_P[normr \o expR \o t \o* X']) / (expR (t * (1 - delta) * fine mu))))%:E).
    rewrite EFinM lee_pdivl_mulr ?expR_gt0// muleC fineK.
    apply: (@markov _ _ _ P (expR \o t \o* X' : {RV P >-> R}) id (expR (t * (1 - delta) * fine mu))%R _ _ _ _) => //.
    - apply: expR_gt0.
    - rewrite norm_expR.
      have -> : 'E_P[expR \o t \o* X'] = 'M_X' t by [].
      by rewrite (binomial_mmt_gen_fun _ bX).
  apply: (@le_trans _ _ (((expR ((expR t - 1) * fine mu)) / (expR (t * (1 - delta) * fine mu))))%:E).
    rewrite norm_expR lee_fin ler_wpM2r ?invr_ge0 ?expR_ge0//.
    have -> : 'E_P[expR \o t \o* X'] = 'M_X' t by [].
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
Corollary bernoulli_trial_inequality4 (X : {dRV P >-> bool}^nat) (delta : R) n :
  is_bernoulli_trial n X -> (0 < delta < 1)%R ->
  (0 < n)%nat ->
  (0 < p)%R ->
  let X' := @bernoulli_trial n X in
  let mu := 'E_P[X'] in
  P [set i | `|X' i - fine mu | >=  delta * fine mu]%R <=
  (expR (- (fine mu * delta ^+ 2) / 3)%R *+ 2)%:E.
Proof.
move=> bX /andP[d0 d1] n0 p0 /=.
set X' := @bernoulli_trial n X.
set mu := 'E_P[X'].
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
- apply: (le_trans (@bernoulli_trial_inequality3 _ delta _ bX _)); first by rewrite d0 d1.
  rewrite lee_fin ler_expR !mulNr lerN2.
  rewrite ler_pM//; last by rewrite lef_pV2 ?posrE ?ler_nat.
  rewrite mulr_ge0 ?fine_ge0 ?sqr_ge0//.
  rewrite /mu unlock /expectation integral_ge0// => x _.
  by rewrite /X' lee_fin; apply: (bernoulli_trial_ge0 bX).
Qed.

(* Rajani thm 3.1 / mu-book thm 4.7 *)
Theorem sampling (X : {dRV P >-> bool}^nat) n (theta delta : R) :
  let X_sum := bernoulli_trial n X in
  let X' x := (X_sum x) / n%:R in
  (0 < p)%R ->
  is_bernoulli_trial n X ->
  (0 < delta <= 1)%R -> (0 < theta < p)%R -> (0 < n)%nat ->
  (3 / theta ^+ 2 * ln (2 / delta) <= n%:R)%R ->
  P [set i | `| X' i - p | <= theta]%R >= 1 - delta%:E.
Proof.
move=> X_sum X' p0 bX /andP[delta0 delta1] /andP[theta0 thetap] n0 tdn.
have E_X_sum: 'E_P[X_sum] = (p * n%:R)%:E.
  by rewrite /X_sum expectation_bernoulli_trial// mulrC.
have /andP[_ p1] := p01.
set epsilon := theta / p.
have epsilon01 : (0 < epsilon < 1)%R.
  by rewrite /epsilon ?ltr_pdivrMr ?divr_gt0 ?mul1r.
have thetaE : theta = (epsilon * p)%R.
  by rewrite /epsilon -mulrA mulVf ?mulr1// gt_eqF.
have step1 : P [set i | `| X' i - p | >= epsilon * p]%R <=
    ((expR (- (p * n%:R * (epsilon ^+ 2)) / 3)) *+ 2)%:E.
  rewrite [X in P X <= _](_ : _ =
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
  by apply: (@bernoulli_trial_inequality4 X epsilon _ bX).
have step2 : P [set i | `| X' i - p | >= theta]%R <=
    ((expR (- (n%:R * theta ^+ 2) / 3)) *+ 2)%:E.
  rewrite thetaE; move/le_trans : step1; apply.
  rewrite lee_fin ler_wMn2r// ler_expR mulNr lerNl mulNr opprK.
  rewrite -2![in leRHS]mulrA [in leRHS]mulrCA.
  rewrite /epsilon -mulrA mulVf ?gt_eqF// mulr1 -!mulrA !ler_wpM2l ?(ltW theta0)//.
  rewrite mulrCA ler_wpM2l ?(ltW theta0)//.
  rewrite [X in (_ * X)%R]mulrA mulVf ?gt_eqF// -[leLHS]mul1r [in leRHS]mul1r.
  by rewrite ler_wpM2r// invf_ge1.
suff : delta%:E >= P [set i | (`|X' i - p| >=(*NB: this >= in the pdf *) theta)%R].
  rewrite [X in P X <= _ -> _](_ : _ = ~` [set i | (`|X' i - p| < theta)%R]); last first.
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
Qed.

End bernoulli.
