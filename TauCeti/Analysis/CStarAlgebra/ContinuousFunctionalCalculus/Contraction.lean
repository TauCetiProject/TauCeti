/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Contractions in a unital C⋆-algebra

For a contraction `a` of a unital C⋆-algebra, `1 - a⋆a` is positive
(`CStarAlgebra.one_sub_star_mul_self_nonneg`); for a self-adjoint contraction this is `1 - a²`
(`IsSelfAdjoint.one_sub_mul_self_nonneg`), so `1 - a²` has the positive square root
`√(1 - a²)`.
These are the entries of the self-adjoint unitary `[[a, √(1 - a²)], [√(1 - a²), -a]]` dilating
`a`.
-/

public section

variable {A : Type*} [CStarAlgebra A]

section Order

variable [PartialOrder A] [StarOrderedRing A]

/-- For a contraction `a`, the element `1 - a⋆a` is positive. -/
theorem CStarAlgebra.one_sub_star_mul_self_nonneg {a : A} (ha : ‖a‖ ≤ 1) :
    0 ≤ 1 - star a * a := by
  rw [sub_nonneg]
  refine (star_mul_le_algebraMap_norm_sq a).trans ?_
  rw [← sub_nonneg, ← map_one (algebraMap ℝ A), ← map_sub]
  exact algebraMap_nonneg A (sub_nonneg.2 (pow_le_one₀ (norm_nonneg a) ha))

/-- For a self-adjoint contraction `a`, the element `1 - a²` is positive. -/
theorem IsSelfAdjoint.one_sub_mul_self_nonneg {a : A} (ha : IsSelfAdjoint a) (ha₁ : ‖a‖ ≤ 1) :
    0 ≤ 1 - a * a := by
  simpa only [ha.star_eq] using CStarAlgebra.one_sub_star_mul_self_nonneg ha₁

end Order
