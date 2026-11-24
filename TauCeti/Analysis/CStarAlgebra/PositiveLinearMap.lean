/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Positive linear maps on unital C⋆-algebras

A positive linear map `ψ` on a unital C⋆-algebra is controlled by its value at `1`: every positive
`a` satisfies `0 ≤ ψ a ≤ ‖a‖ • ψ 1`, and the positive elements span the algebra.

## Main declarations

* `PositiveLinearMap.eq_zero_of_map_one_eq_zero`: a positive linear map on a unital C⋆-algebra
  that vanishes at `1` is zero.
-/

public section

/-- A positive map on a unital C⋆-algebra that vanishes at `1` is zero. -/
theorem PositiveLinearMap.eq_zero_of_map_one_eq_zero {A B : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [AddCommMonoid B] [PartialOrder B] [Module ℂ B]
    (ψ : A →ₚ[ℂ] B) (h1 : ψ 1 = 0) : ψ = 0 := by
  refine PositiveLinearMap.toLinearMap_injective <|
    LinearMap.ext_on (CStarAlgebra.span_nonneg (A := A)) fun a (ha : 0 ≤ a) => ?_
  refine le_antisymm ?_ (ψ.map_nonneg ha)
  calc ψ a ≤ ψ (algebraMap ℝ A ‖a‖) := ψ.monotone (ha.isSelfAdjoint.le_algebraMap_norm_self)
    _ = 0 := by
      rw [IsScalarTower.algebraMap_apply ℝ ℂ A, Algebra.algebraMap_eq_smul_one, map_smul, h1,
        smul_zero]
