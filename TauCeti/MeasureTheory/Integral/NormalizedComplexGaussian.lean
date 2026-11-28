/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Positivity

/-!
# Complex Gaussian integrals against normalized Lebesgue measure

On `ℂ`, the Gaussian `z ↦ exp (-a⁻¹ * ‖z‖ ^ 2)` for `a > 0` integrates to `π * a` against
Lebesgue measure (`TauCeti.integral_exp_neg_inv_mul_norm_sq_complex`). On a finite power `ι → ℂ`
equipped with the normalized measure `(NNReal.pi⁻¹ ^ Fintype.card ι) • volume` (so that
`exp (-∑ i, ‖y i‖ ^ 2)` has integral `1`), the Gaussian `exp (-a⁻¹ * ∑ i, ‖y i‖ ^ 2)` has integral
`a ^ Fintype.card ι` (`TauCeti.integral_exp_neg_inv_mul_sum_norm_sq_pi`), and any function
`f : (ι → ℂ) → E` dominated almost everywhere by `C * exp (-a⁻¹ * ∑ i, ‖y i‖ ^ 2)` has integral
of norm at most `C * a ^ Fintype.card ι`
(`TauCeti.norm_integral_le_of_norm_le_exp_neg_inv_mul_sum_norm_sq`).

## Main results

* `TauCeti.integral_exp_neg_inv_mul_norm_sq_complex`
* `TauCeti.integral_exp_neg_inv_mul_sum_norm_sq_pi`
* `TauCeti.norm_integral_le_of_norm_le_exp_neg_inv_mul_sum_norm_sq`

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/UpperBound/Kernels/JetConjugatesAndBounds.lean`, declarations
`New.integral_exp_neg_inv_mul_normalizedVolume` and `New.norm_integral_normalizedVolume_le`.
-/

public section

open MeasureTheory Real Finset

namespace TauCeti

/-- On `ℂ` with Lebesgue measure, `∫ z, exp (-a⁻¹ * ‖z‖ ^ 2) = π * a` for `a > 0`. -/
theorem integral_exp_neg_inv_mul_norm_sq_complex {a : ℝ} (ha : 0 < a) :
    ∫ z : ℂ, exp (-a⁻¹ * ‖z‖ ^ 2) = π * a := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) (b := a⁻¹) (inv_pos.mpr ha)
  simpa [Complex.finrank_real_complex, Real.rpow_one, div_inv_eq_mul] using h

/-- Against the normalized Lebesgue measure `(NNReal.pi⁻¹ ^ Fintype.card ι) • volume` on `ι → ℂ`,
the Gaussian `exp (-a⁻¹ * ∑ i, ‖y i‖ ^ 2)` has integral `a ^ Fintype.card ι` for `a > 0`. -/
theorem integral_exp_neg_inv_mul_sum_norm_sq_pi {ι : Type*} [Fintype ι] {a : ℝ} (ha : 0 < a) :
    ∫ y : ι → ℂ, exp (-a⁻¹ * ∑ i : ι, ‖y i‖ ^ 2)
      ∂((NNReal.pi⁻¹ ^ Fintype.card ι) • (volume : Measure (ι → ℂ))) = a ^ Fintype.card ι := by
  have h_prod : ∀ y : ι → ℂ,
      exp (-a⁻¹ * ∑ i : ι, ‖y i‖ ^ 2) = ∏ i : ι, exp (-a⁻¹ * ‖y i‖ ^ 2) := fun y ↦ by
    rw [mul_sum, exp_sum]
  simp_rw [h_prod]
  rw [integral_smul_nnreal_measure,
    integral_fintype_prod_volume_eq_pow (fun z : ℂ ↦ exp (-a⁻¹ * ‖z‖ ^ 2)),
    integral_exp_neg_inv_mul_norm_sq_complex ha]
  simp [NNReal.smul_def, mul_pow, pi_ne_zero]

/-- If `f : (ι → ℂ) → E` satisfies `‖f y‖ ≤ C * exp (-a⁻¹ * ∑ i, ‖y i‖ ^ 2)` almost everywhere
with respect to `(NNReal.pi⁻¹ ^ Fintype.card ι) • volume` for `a > 0`, then its integral has norm
at most `C * a ^ Fintype.card ι`. -/
theorem norm_integral_le_of_norm_le_exp_neg_inv_mul_sum_norm_sq {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a C : ℝ} (ha : 0 < a) {f : (ι → ℂ) → E}
    (hf : ∀ᵐ y ∂((NNReal.pi⁻¹ ^ Fintype.card ι) • (volume : Measure (ι → ℂ))),
      ‖f y‖ ≤ C * exp (-a⁻¹ * ∑ i : ι, ‖y i‖ ^ 2)) :
    ‖∫ y : ι → ℂ, f y ∂((NNReal.pi⁻¹ ^ Fintype.card ι) • (volume : Measure (ι → ℂ)))‖ ≤
      C * a ^ Fintype.card ι := by
  let μ : Measure (ι → ℂ) := (NNReal.pi⁻¹ ^ Fintype.card ι) • volume
  have h_int : ∫ y : ι → ℂ, exp (-a⁻¹ * ∑ i : ι, ‖y i‖ ^ 2) ∂μ = a ^ Fintype.card ι :=
    integral_exp_neg_inv_mul_sum_norm_sq_pi ha
  rw [← h_int, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (.const_mul ?_ C) hf
  exact .of_integral_ne_zero (h_int.trans_ne (by positivity))

end TauCeti
