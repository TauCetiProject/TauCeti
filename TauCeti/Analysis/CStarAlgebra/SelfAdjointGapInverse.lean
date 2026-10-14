/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Spectral-gap inverse of a self-adjoint element

If a self-adjoint element `a` of a C⋆-algebra has a real spectral gap around
zero of radius `r > 0`, then `a` is invertible and its canonical ring inverse
has norm at most `r⁻¹`.

This quantitative bound is used in interval and exterior Sylvester estimates.

## Main result

* `IsSelfAdjoint.isUnit_and_norm_ringInverse_le` provides both `IsUnit a`
  and the norm bound for `Ring.inverse a` under the spectral-gap hypothesis.

## Source

Adapted from the Davis--Kahan/DKPS formalization (Kitware, Inc.),
`ForMathlib/Analysis/CStarAlgebra/SelfAdjointGapInverse.lean` at commit
`fc38eb4`, by Jon Crall and Claude Fable 5 (Apache 2.0).
-/

public section

namespace IsSelfAdjoint

variable {A : Type*} [CStarAlgebra A] {a : A} {r : ℝ}

/-- A positive gap around zero in the real spectrum of a self-adjoint element
makes it a unit and bounds the canonical ring inverse by the reciprocal gap. -/
theorem isUnit_and_norm_ringInverse_le (ha : IsSelfAdjoint a) (hr : 0 < r)
    (hσ : ∀ x ∈ spectrum ℝ a, r ≤ |x|) :
    IsUnit a ∧ ‖Ring.inverse a‖ ≤ r⁻¹ := by
  have hunit : IsUnit a := by
    refine spectrum.isUnit_of_zero_notMem ℝ (fun hzero => ?_)
    have hbound : r ≤ (0 : ℝ) := by
      simpa only [abs_zero] using hσ 0 hzero
    exact (not_le_of_gt hr) hbound
  refine ⟨hunit, ?_⟩
  rw [← cfc_ringInverse_id (R := ℝ) a hunit]
  refine norm_cfc_le (by positivity) fun x hx => ?_
  rw [Real.norm_eq_abs, abs_inv]
  exact inv_anti₀ hr (hσ x hx)

end IsSelfAdjoint
