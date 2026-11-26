/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Complex Gaussian integral on `κ → ℂ`

Evaluates the standard Gaussian integral `∫ y : κ → ℂ, exp (-t ∑ j, ‖y j‖²) = (π / t) ^ card κ`
for `t > 0`.

## Main results

* `Real.integral_rexp_neg_mul_sum_norm_sq`: for `t > 0` and finite `κ`,
  `∫ y : κ → ℂ, rexp (-t * ∑ j : κ, ‖y j‖ ^ 2) = (π / t) ^ Fintype.card κ`.
-/

public section

open Fintype MeasureTheory

namespace Real

/-- The Gaussian integral of `exp (-t ∑ j, ‖y j‖²)` over `y : κ → ℂ` for `t > 0` is
`(π / t) ^ card κ`. -/
theorem integral_rexp_neg_mul_sum_norm_sq {κ : Type*} [Fintype κ] {t : ℝ} (ht : 0 < t) :
    ∫ y : κ → ℂ, rexp (-t * ∑ j : κ, ‖y j‖ ^ 2) = (π / t) ^ card κ := by
  have h_eq (y : κ → ℂ) : rexp (-t * ∑ j : κ, ‖y j‖ ^ 2) = ∏ j : κ, rexp (-t * ‖y j‖ ^ 2) := by
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h_eq]
  rw [integral_fintype_prod_volume_eq_prod (f := fun (_ : κ) (z : ℂ) ↦ rexp (-t * ‖z‖ ^ 2))]
  have h1 : ∫ z : ℂ, rexp (-t * ‖z‖ ^ 2) = π / t := by
    simpa [Complex.finrank_real_complex] using
      GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) ht
  rw [Finset.prod_const, Finset.card_univ, h1]

end Real
