/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.UpperTriangularBlock

/-!
# Compact upper-triangular block operators and parametrices

An upper-triangular `2 × 2` block continuous linear map `[[A, B], [0, D]]` with compact blocks `A`,
`B`, and `D` is compact (`IsCompactOperator.upperTriangularBlock`). Consequently, if `P_A` and
`P_D` are left or right parametrices of `A` and `D` modulo compact operators, then
`ContinuousLinearMap.upperTriangularBlockParametrix P_A B P_D` is a left or right parametrix of
`ContinuousLinearMap.upperTriangularBlock A B D` modulo compact operators.
-/

public section

open scoped Pointwise

/-- An upper-triangular block operator whose three nonzero blocks are compact operators is
compact. -/
theorem IsCompactOperator.upperTriangularBlock {R E₁ E₂ F₁ F₂ : Type*} [Semiring R]
    [TopologicalSpace E₁] [AddCommMonoid E₁] [Module R E₁]
    [TopologicalSpace E₂] [AddCommMonoid E₂] [Module R E₂]
    [TopologicalSpace F₁] [AddCommMonoid F₁] [Module R F₁] [ContinuousAdd F₁]
    [TopologicalSpace F₂] [AddCommMonoid F₂] [Module R F₂]
    {A : E₁ →L[R] F₁} {B : E₂ →L[R] F₁} {D : E₂ →L[R] F₂}
    (hA : IsCompactOperator A) (hB : IsCompactOperator B) (hD : IsCompactOperator D) :
    IsCompactOperator (ContinuousLinearMap.upperTriangularBlock A B D) := by
  obtain ⟨K₁, hK₁, hf₁⟩ :=
    (hA.comp_clm (.fst R E₁ E₂)).add (hB.comp_clm (.snd R E₁ E₂))
  obtain ⟨K₂, hK₂, hf₂⟩ := hD.comp_clm (.snd R E₁ E₂)
  refine ⟨K₁ ×ˢ K₂, hK₁.prod hK₂, Filter.mem_of_superset (Filter.inter_mem hf₁ hf₂) ?_⟩
  rintro ⟨x₁, x₂⟩ ⟨hx₁, hx₂⟩
  simpa [ContinuousLinearMap.upperTriangularBlock_apply] using ⟨hx₁, hx₂⟩

namespace ContinuousLinearMap

variable {R E₁ E₂ F₁ F₂ : Type*} [Ring R]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module R E₁] [IsTopologicalAddGroup E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module R E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module R F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module R F₂]

/-- If `P_A` and `P_D` are left parametrices of `A` and `D` modulo compact operators, then
`upperTriangularBlockParametrix P_A B P_D` is a left parametrix of `upperTriangularBlock A B D`
modulo compact operators. -/
theorem isCompactOperator_upperTriangularBlockParametrix_comp_sub_one
    [IsTopologicalAddGroup E₂] [ContinuousAdd F₁]
    (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂)
    {P_A : F₁ →L[R] E₁} {P_D : F₂ →L[R] E₂}
    (hPA : IsCompactOperator (P_A ∘L A - 1 : E₁ →L[R] E₁))
    (hPD : IsCompactOperator (P_D ∘L D - 1 : E₂ →L[R] E₂)) :
    IsCompactOperator
      (upperTriangularBlockParametrix P_A B P_D ∘L upperTriangularBlock A B D - 1 :
        E₁ × E₂ →L[R] E₁ × E₂) := by
  rw [upperTriangularBlockParametrix_comp_sub_one]
  have hmid : (⇑(-(P_A ∘L B ∘L (P_D ∘L D - 1))) : E₂ → E₁) =
      -(⇑(P_A ∘L B) ∘ ⇑(P_D ∘L D - 1 : E₂ →L[R] E₂)) := by
    ext x
    simp
  exact .upperTriangularBlock hPA (hmid ▸ (hPD.clm_comp (P_A ∘L B)).neg) hPD

/-- If `P_A` and `P_D` are right parametrices of `A` and `D` modulo compact operators, then
`upperTriangularBlockParametrix P_A B P_D` is a right parametrix of `upperTriangularBlock A B D`
modulo compact operators. -/
theorem isCompactOperator_comp_upperTriangularBlockParametrix_sub_one
    [IsTopologicalAddGroup F₁] [IsTopologicalAddGroup F₂]
    (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂)
    {P_A : F₁ →L[R] E₁} {P_D : F₂ →L[R] E₂}
    (hPA : IsCompactOperator (A ∘L P_A - 1 : F₁ →L[R] F₁))
    (hPD : IsCompactOperator (D ∘L P_D - 1 : F₂ →L[R] F₂)) :
    IsCompactOperator
      (upperTriangularBlock A B D ∘L upperTriangularBlockParametrix P_A B P_D - 1 :
        F₁ × F₂ →L[R] F₁ × F₂) := by
  rw [comp_upperTriangularBlockParametrix_sub_one]
  have hmid : (⇑(-((A ∘L P_A - 1) ∘L B ∘L P_D)) : F₂ → F₁) =
      -(⇑(A ∘L P_A - 1 : F₁ →L[R] F₁) ∘ ⇑(B ∘L P_D)) := by
    ext y
    simp
  exact .upperTriangularBlock hPA (hmid ▸ (hPA.comp_clm (B ∘L P_D)).neg) hPD

end ContinuousLinearMap
