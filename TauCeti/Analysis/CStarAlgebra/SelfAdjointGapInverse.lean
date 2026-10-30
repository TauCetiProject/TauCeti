/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Spectral intervals and the gap inverse of a self-adjoint element

For a self-adjoint element `a` of a C⋆-algebra, the norm equals the spectral radius, and one of
`‖a‖` and `-‖a‖` lies in the real spectrum of `a` when the algebra is nontrivial. Hence, for
`0 ≤ r`, `‖a‖ ≤ r` exactly when the real spectrum of `a` lies in the interval `[-r, r]`; this
turns spectral localisation into norm bounds and back.

If instead the real spectrum has a gap around zero of radius `r > 0`, then `a` is invertible and
its canonical ring inverse has norm at most `r⁻¹`. This quantitative bound is used in interval
and exterior Sylvester estimates.

## Main results

* `IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc`: for `0 ≤ r`, `‖a‖ ≤ r` if and only if
  `spectrum ℝ a ⊆ Set.Icc (-r) r`.
* `IsSelfAdjoint.isUnit_and_norm_ringInverse_le` provides both `IsUnit a`
  and the norm bound for `Ring.inverse a` under the spectral-gap hypothesis.

## Source

The interval characterisation follows the proof of Mathlib's
`CStarAlgebra.norm_le_iff_le_algebraMap` for nonnegative elements, using
`CStarAlgebra.norm_or_neg_norm_mem_spectrum` in place of `CStarAlgebra.norm_mem_spectrum_of_nonneg`.
The gap inverse is adapted from the Davis--Kahan/DKPS formalization (Kitware, Inc.),
`ForMathlib/Analysis/CStarAlgebra/SelfAdjointGapInverse.lean` at commit
`fc38eb4`, by Jon Crall and Claude Fable 5 (Apache 2.0).
-/

public section

namespace IsSelfAdjoint

variable {A : Type*} [CStarAlgebra A] {a : A} {r : ℝ}

/-- The norm of a self-adjoint element is at most `r ≥ 0` exactly when its real spectrum lies
in the interval `[-r, r]`. -/
theorem norm_le_iff_spectrum_subset_Icc (ha : IsSelfAdjoint a) (hr : 0 ≤ r) :
    ‖a‖ ≤ r ↔ spectrum ℝ a ⊆ Set.Icc (-r) r := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim a 0, hr]
  refine ⟨fun h x hx => ?_, fun h => ?_⟩
  · rw [Set.mem_Icc, ← abs_le, ← Real.norm_eq_abs]
    exact (spectrum.norm_le_norm_of_mem hx).trans h
  · rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum a with hmem | hmem
    · exact (h hmem).2
    · simpa using (h hmem).1

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
