/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import TauCeti.RepresentationTheory.Induction.TrivialSubgroup
public import TauCeti.RepresentationTheory.Rep.ChangeOfGroup
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro

/-!
# Homology of modules induced from the trivial subgroup

By Shapiro's lemma, the representation `Ind_⊥^G X` induced from the trivial subgroup has vanishing
homology in positive degrees, and so does its restriction to any subgroup `S`, since that
restriction is again induced from the trivial subgroup (`Rep.resIndBotIso`).

The statements follow `ClassFieldTheory/Cohomology/IndCoind/TrivialCohomology.lean` in
`kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509`.

## Main statements

* `groupHomology.isZero_indBot_succ`: `Hₙ₊₁(G, Ind_⊥^G X) = 0`.
* `groupHomology.isZero_res_indBot_succ`: `Hₙ₊₁(S, Ind_⊥^G X) = 0` for every subgroup `S ≤ G`.
* `TauCeti.groupHomology.isZero_res_leftRegular_succ`: `Hₙ₊₁(S, k[G]) = 0`
  for every subgroup.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §6.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 6.3.
-/

public section

universe u

open CategoryTheory Rep

namespace groupHomology

variable {k G : Type u} [CommRing k] [Group G]

/-- Positive-degree homology of a representation induced from the trivial subgroup vanishes (Weibel
6.3.3). Unlike the Tate analogue `TauCeti.TateCohomology.isZero_indBot`, no finiteness is needed. -/
theorem isZero_indBot_succ (X : Type u) [AddCommGroup X] [Module k X] (n : ℕ) :
    Limits.IsZero (groupHomology (indBot k G X) (n + 1)) := by
  classical
  -- Shapiro's lemma (Weibel 6.3.2) identifies this with `Hₙ₊₁(⊥, X)`, and the trivial group has no
  -- positive-degree homology.
  exact (isZero_groupHomology_succ_of_subsingleton _ n).of_iso (indIso _ _ _)

/-- Positive-degree homology of the restriction to a subgroup of a representation induced from the
trivial subgroup vanishes. Unlike the Tate analogue `TauCeti.TateCohomology.isZero_res_indBot`, no
finiteness is needed. -/
theorem isZero_res_indBot_succ (S : Subgroup G) (X : Type u) [AddCommGroup X] [Module k X] (n : ℕ) :
    Limits.IsZero (groupHomology (res S.subtype (indBot k G X)) (n + 1)) :=
  (isZero_indBot_succ (G := S) (G ⧸ S →₀ X) n).of_iso
    ((groupHomology.functor k S (n + 1)).mapIso (resIndBotIso S X))

end groupHomology

namespace TauCeti.groupHomology

/-- Positive-degree homology of a subgroup with coefficients in the restricted left regular
representation vanishes, without any finiteness assumption. -/
theorem isZero_res_leftRegular_succ {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) (n : ℕ) :
    Limits.IsZero (groupHomology (res S.subtype (leftRegular k G)) (n + 1)) :=
  (_root_.groupHomology.isZero_res_indBot_succ S k n).of_iso
    ((_root_.groupHomology.functor k S (n + 1)).mapIso
      ((resFunctor S.subtype).mapIso indBotIsoLeftRegular.symm))

end TauCeti.groupHomology
