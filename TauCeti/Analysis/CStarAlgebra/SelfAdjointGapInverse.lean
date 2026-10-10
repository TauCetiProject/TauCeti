/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Spectral-gap bound on the inverse of a self-adjoint element

For a self-adjoint element `a` in a C⋆-algebra, if every point of the real
spectrum has absolute value at least `r > 0`, then `a` is invertible and the
norm of its inverse is bounded by `r⁻¹`.

The norm/spectrum interval characterization for self-adjoint elements follows
directly from Mathlib's `norm_cfc_le_iff` applied to the identity function;
it does not require an additional public declaration.

## Main result

* `IsSelfAdjoint.norm_ringInverse_le`: a positive gap about zero in the real
  spectrum bounds the norm of the canonical ring inverse.

The inverse bound is an ingredient of interval/exterior Sylvester estimates
in the Davis--Kahan `sin Θ` theorem.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/Analysis/CStarAlgebra/SelfAdjointGapInverse.lean`
  at Davis--Kahan commit `fc38eb4`.
* Original declarations: `ForMathlib.IsSelfAdjoint.norm_le_of_spectrum_subset_Icc`
  and `ForMathlib.IsSelfAdjoint.exists_two_sided_inverse_of_spectrum_gap`
  (namespace adapted for Tau Ceti). The inverse estimate is stated in terms
  of `Ring.inverse` rather than an existentially chosen inverse.
* Spectra influence: none (Mathlib only).
-/

public section

namespace IsSelfAdjoint

variable {A : Type*} [CStarAlgebra A] {a : A} {r : ℝ}

/-- If the real spectrum of a self-adjoint element avoids `(-r, r)` for `r > 0`,
then the norm of its canonical inverse is at most `r⁻¹`. -/
theorem norm_ringInverse_le (ha : IsSelfAdjoint a) (hr : 0 < r)
    (hσ : ∀ x ∈ spectrum ℝ a, r ≤ |x|) : ‖Ring.inverse a‖ ≤ r⁻¹ := by
  have hunit : IsUnit a := by
    refine spectrum.isUnit_of_zero_notMem ℝ (fun hzero => ?_)
    have hbound : r ≤ (0 : ℝ) := by
      simpa only [abs_zero] using hσ 0 hzero
    exact (not_le_of_gt hr) hbound
  rw [← cfc_ringInverse_id (R := ℝ) a hunit]
  refine norm_cfc_le (by positivity) fun x hx => ?_
  rw [Real.norm_eq_abs, abs_inv]
  exact inv_anti₀ hr (hσ x hx)

end IsSelfAdjoint
