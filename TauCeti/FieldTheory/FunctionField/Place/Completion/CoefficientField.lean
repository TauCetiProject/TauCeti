/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.Basic
public import TauCeti.RingTheory.LocalRing.CoefficientField

/-!
# The coefficient field of the completion at a place

Let `P` be a place of `F / k` whose residue field `F_P` is separable over `k`; over a perfect
constant field this holds at every place with finite residue field, in particular at every place
of an algebraic function field. The completed valuation ring `𝒪̂_P` is complete for the adic
topology of its maximal ideal (`TauCeti.Place.isAdicComplete_completionIntegers`), so it contains
a unique copy of `F_P` over `k` mapping onto the residue field: a `k`-algebra embedding
`F_P → 𝒪̂_P` which reduces to the identity of `F_P`.

At a rational place this embedding is just the constant field `k`, and expansions in a
uniformizer `t` have coefficients in `k`. At a place of higher degree the coefficients of the
`P`-adic expansion `∑ aᵢ tⁱ` of a completed function are taken in the image of this embedding,
which is what makes them, and the residue `a₋₁`, elements of `F_P`.

## Main definitions

* `TauCeti.Place.completionResidueFieldSection`: the coefficient field `F_P →ₐ[k] 𝒪̂_P`.

## Main results

* `TauCeti.Place.residue_completionResidueFieldSection`: it reduces to the identification of
  `F_P` with the residue field of the completion.
* `TauCeti.Place.eq_completionResidueFieldSection`: it is the only `k`-algebra embedding of `F_P`
  with this property.
* `TauCeti.Place.sub_completionResidueFieldSection_mem_filtration_one` and
  `TauCeti.Place.completionEmbedding_sub_completionResidueFieldSection_mem_filtration_one`: every
  integral completed function, in particular every function regular at `P`, agrees with the
  coefficient-field lift of its value at `P` up to a function vanishing at `P`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §4.
-/

public section

namespace TauCeti.Place

open IsLocalRing

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)
  [Algebra.IsSeparable k P.ResidueField]

/-- Completion does not change the residue field, so it preserves its separability over the
constants. -/
instance isSeparable_completionPlace_residueField :
    Algebra.IsSeparable k P.completionPlace.ResidueField :=
  AlgEquiv.Algebra.isSeparable P.residueFieldEquivCompletion

/-- The residue field of the completion is formally étale over the constants, being separable;
this is the hypothesis under which `TauCeti.residueFieldSection` exists and is unique. -/
instance formallyEtale_completionPlace_residueField :
    Algebra.FormallyEtale k P.completionPlace.ResidueField :=
  Algebra.FormallyEtale.of_isSeparable k _

/-- The **coefficient field** of the completion at a place with separable residue field: the
unique `k`-algebra embedding of the residue field `F_P` into the completed valuation ring whose
reduction is the identification `TauCeti.Place.residueFieldEquivCompletion` of `F_P` with the
residue field of the completion. -/
noncomputable def completionResidueFieldSection :
    P.ResidueField →ₐ[k] P.completionPlace.integers :=
  (residueFieldSection k P.completionPlace.integers).comp
    P.residueFieldEquivCompletion.toAlgHom

/-- The coefficient field of the completion at `P` is the coefficient field of the complete local
ring `𝒪̂_P`, read through the identification of the residue fields. -/
theorem completionResidueFieldSection_apply (a : P.ResidueField) :
    P.completionResidueFieldSection a =
      residueFieldSection k P.completionPlace.integers (P.residueFieldEquivCompletion a) := (rfl)

/-- The coefficient field reduces to the identification of the residue fields. -/
@[simp]
theorem residue_completionResidueFieldSection (a : P.ResidueField) :
    residue P.completionPlace.integers (P.completionResidueFieldSection a) =
      P.residueFieldEquivCompletion a :=
  residue_residueFieldSection k P.completionPlace.integers _

/-- The coefficient field is the only `k`-algebra embedding of the residue field into the
completed valuation ring which reduces to the identification of the residue fields. -/
theorem eq_completionResidueFieldSection {s : P.ResidueField →ₐ[k] P.completionPlace.integers}
    (hs : ∀ a, residue P.completionPlace.integers (s a) = P.residueFieldEquivCompletion a) :
    s = P.completionResidueFieldSection := by
  have h := eq_residueFieldSection k P.completionPlace.integers
    (s := s.comp P.residueFieldEquivCompletion.symm.toAlgHom) fun a ↦ by simp [hs]
  ext a
  simpa [completionResidueFieldSection_apply] using
    congrArg (fun g ↦ (g (P.residueFieldEquivCompletion a) : P.Completion)) h

/-- An integral completed function agrees with the coefficient-field lift of its value at `P` up
to a completed function vanishing at `P`. -/
theorem sub_completionResidueFieldSection_mem_filtration_one (x : P.completionPlace.integers) :
    (x : P.Completion) - P.completionResidueFieldSection
      (P.residueFieldEquivCompletion.symm (residue P.completionPlace.integers x)) ∈
      P.completionPlace.filtration 1 :=
  P.completionPlace.residue_eq_iff_sub_mem_filtration_one.mp (by simp)

/-- A function regular at `P` agrees, in the completion, with the coefficient-field lift of its
value at `P` up to a completed function vanishing at `P`. -/
theorem completionEmbedding_sub_completionResidueFieldSection_mem_filtration_one
    (x : P.integers) :
    P.completionEmbedding x - P.completionResidueFieldSection (residue P.integers x) ∈
      P.completionPlace.filtration 1 := by
  have h := P.sub_completionResidueFieldSection_mem_filtration_one
    (P.completionIntegersEmbedding x)
  rwa [← residueFieldEquivCompletion_apply_residue, AlgEquiv.symm_apply_apply,
    completionIntegersEmbedding_apply] at h

end TauCeti.Place
