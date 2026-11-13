/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The degree of a compositum of finitely many intermediate fields

The degree of the compositum of two intermediate fields is at most the product of their degrees
(`IntermediateField.finrank_sup_le`). This file iterates that bound over finitely many
intermediate fields, and deduces that adjoining finitely many elements gives an extension of
degree at most the product of the degrees of their minimal polynomials.

Neither bound needs an algebraicity hypothesis: an infinite-dimensional compositum has `finrank`
equal to `0`, and so does the minimal polynomial of a transcendental element.

## Main results

* `IntermediateField.finrank_biSup_le_prod`, `IntermediateField.finrank_iSup_le_prod`:
  `[⨆ i, Eᵢ : K] ≤ ∏ i, [Eᵢ : K]` for finitely many intermediate fields `Eᵢ`.
* `IntermediateField.finrank_adjoin_range_le_prod`: `[K(x₁, …, xₙ) : K] ≤ ∏ i, deg xᵢ`.
-/

public section

open Module

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}

/-- The degree of the compositum of the intermediate fields `Eᵢ`, `i ∈ s`, is at most the product
of their degrees. -/
theorem finrank_biSup_le_prod (E : ι → IntermediateField K L) (s : Finset ι) :
    finrank K ↥(⨆ i ∈ s, E i) ≤ ∏ i ∈ s, finrank K (E i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [show ⨆ i ∈ (∅ : Finset ι), E i = ⊥ by simp, IntermediateField.finrank_bot,
      Finset.prod_empty]
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.prod_insert ha]
    exact (finrank_sup_le _ _).trans (Nat.mul_le_mul_left _ ih)

/-- The degree of the compositum of finitely many intermediate fields `Eᵢ` is at most the product
of their degrees. -/
theorem finrank_iSup_le_prod [Fintype ι] (E : ι → IntermediateField K L) :
    finrank K ↥(⨆ i, E i) ≤ ∏ i, finrank K (E i) := by
  rw [show ⨆ i, E i = ⨆ i ∈ Finset.univ, E i by simp]
  exact finrank_biSup_le_prod E Finset.univ

/-- Adjoining finitely many elements `xᵢ` gives an extension of degree at most the product of the
degrees of their minimal polynomials. If some `xᵢ` is transcendental, both sides are `0`. -/
theorem finrank_adjoin_range_le_prod [Fintype ι] (x : ι → L) :
    finrank K (adjoin K (Set.range x)) ≤ ∏ i, (minpoly K (x i)).natDegree := by
  rw [← Set.iUnion_singleton_eq_range, adjoin_iUnion]
  refine (finrank_iSup_le_prod _).trans (Finset.prod_le_prod fun i _ ↦ ?_)
  by_cases hx : IsIntegral K (x i)
  · exact (adjoin.finrank hx).le
  · -- A transcendental element generates an infinite-dimensional extension.
    have : ¬FiniteDimensional K K⟮x i⟯ := fun h ↦ hx <| by
      simpa using (IsIntegral.of_finite K (AdjoinSimple.gen K (x i))).map (val K⟮x i⟯)
    rw [finrank_of_not_finite this]
    exact Nat.zero_le _

end IntermediateField
