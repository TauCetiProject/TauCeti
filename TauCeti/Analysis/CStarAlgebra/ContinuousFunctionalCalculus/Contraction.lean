/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Contractions in a C⋆-algebra

Compressing a self-adjoint contraction `p` by a positive contraction `e` of a possibly nonunital
C⋆-algebra stays below `e`: `e p e ≤ e` (`CStarAlgebra.mul_mul_le_of_nonneg_of_norm_le_one`).
Conversely, compressing a self-adjoint `p` by a projection `e` stays above a multiple of `e`:
`(1 - ‖p - e‖) e ≤ e p e` (`IsStarProjection.one_sub_norm_sub_smul_le_mul_mul`).

For a contraction `a` of a unital C⋆-algebra, `1 - a⋆a` is positive
(`CStarAlgebra.one_sub_star_mul_self_nonneg`); for a self-adjoint contraction this is `1 - a²`
(`IsSelfAdjoint.one_sub_mul_self_nonneg`), so `1 - a²` has the positive square root
`√(1 - a²)`.
These are the entries of the self-adjoint unitary `[[a, √(1 - a²)], [√(1 - a²), -a]]` dilating
`a`.
-/

public section

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Compressing a self-adjoint contraction `p` by a positive contraction `e` gives `e p e ≤ e`. -/
theorem CStarAlgebra.mul_mul_le_of_nonneg_of_norm_le_one {e p : A} (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    (hp : IsSelfAdjoint p) (hp1 : ‖p‖ ≤ 1) : e * p * e ≤ e := by
  have h := CStarAlgebra.star_left_conjugate_le_norm_smul e p hp
  rw [he0.star_eq] at h
  exact h.trans ((smul_le_of_le_one_left he0.isSelfAdjoint.mul_self_nonneg hp1).trans
    (CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one he0 he1))

/-- Compressing a self-adjoint `p` by a projection `e` gives at least `(1 - ‖p - e‖) e`:
`(1 - ‖p - e‖) e ≤ e p e`. -/
theorem IsStarProjection.one_sub_norm_sub_smul_le_mul_mul {e p : A} (he : IsStarProjection e)
    (hp : IsSelfAdjoint p) : (1 - ‖p - e‖) • e ≤ e * p * e := by
  have h := CStarAlgebra.star_left_conjugate_le_norm_smul e (-(p - e))
    (hp.sub he.isSelfAdjoint).neg
  have hee : e * e = e := he.isIdempotentElem.eq
  rw [he.isSelfAdjoint.star_eq, norm_neg, hee, mul_neg, neg_mul] at h
  -- `e p e = e + e (p - e) e` and `-e (p - e) e ≤ ‖p - e‖ e`.
  have hepe : e * p * e = e + e * (p - e) * e := by
    rw [mul_sub, sub_mul, hee, hee, add_sub_cancel]
  rw [hepe, sub_smul, one_smul, sub_eq_add_neg]
  exact add_le_add le_rfl (neg_le.1 h)

end NonUnital

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
