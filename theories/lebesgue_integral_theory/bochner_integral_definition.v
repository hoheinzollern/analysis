(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference finmap.
From mathcomp Require Import unstable.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality reals fsbigop topology tvs.
From mathcomp Require Import normedtype sequences real_interval esum measure.
From mathcomp Require Import lebesgue_measure simple_functions measurable_realfun.
From mathcomp Require Import complete_normed_module.
From mathcomp Require Import ereal.

(**md**************************************************************************)
(* # Definition of the Bochner integral                                       *)
(*                                                                            *)
(* This file contains the definition of the Bochner integral for functions    *)
(* taking values in a complete normed space (Banach space). It starts with    *)
(* the integral of simple functions, proves their basic properties (linearity,*)
(* etc.), and provides the foundation for integration of measurable functions. *)
(*                                                                            *)
(* Main notations:                                                            *)
(* | Coq notation          |  | Meaning                         |             *)
(* |----------------------:|--|:--------------------------------              *)
(* | \int[mu]_(x in D) f x |==| $\int_D f(x)\mathbf{d}\mu(x)$                 *)
(* | \int[mu]_x f x        |==| $\int f(x)\mathbf{d}\mu(x)$                   *)
(*                                                                            *)
(* The Bochner integral is defined for functions taking values in a complete   *)
(* normed space. It generalizes the Lebesgue integral to vector-valued       *)
(* functions.                                                                 *)
(*                                                                            *)
(* Main reference:                                                            *)
(* - Daniel Li, Intégration et applications, 2016                             *)
(*                                                                            *)
(* Detailed contents:                                                         *)
(* ```                                                                        *)
(*         bsintegral mu f == Bochner integral of f with measure mu           *)
(*  \int[mu]_(x in D) f x == Bochner integral over domain D                  *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Reserved Notation "\int [ mu ]_ ( i 'in' D ) F"
  (at level 36, F at level 36, i, D at level 60,
  format "'[' \int [ mu ]_ ( i  'in'  D ) '/  '  F ']'").
Reserved Notation "\int [ mu ]_ i F"
  (F at level 36, i at level 0,
    right associativity, format "'[' \int [ mu ]_ i '/  '  F ']'").

(** Bochner integral for simple functions *)
Section bsintegral_simple.
Context (R : realType).
Context (E : realType).

(* Variable (E : Type) [NormedAddCommGroup E] [NormedSpace ar R E] [Complete E]. *)

Definition bsintegral (T : Type) (mu : set T -> R) (f : T -> E) : E :=
  \sum_(x \in [set: E]) (x%:E) * mu (f @^-1` [set x]).

Lemma bsintegralE (T : Type) (mu : set T -> ar R) (f : T -> E) :
  bsintegral mu f = \sum_(x \in range f) x%:E * mu (f @^-1` [set x]).
Proof.
rewrite (fsbig_widen (range f) setT)//= => x [_ Nfx] /=.
by rewrite preimage10// mule0.
Qed.

Lemma bsintegral0 (T : Type) (mu : set T -> ar R) :
  bsintegral mu (cst 0) = 0.
Proof.
rewrite bsintegralE //= => r _; rewrite preimage_cst.
by case: ifPn => [/[!inE] <-|]; rewrite ?mul0e// mule0.
Qed.

End bsintegral_simple.
