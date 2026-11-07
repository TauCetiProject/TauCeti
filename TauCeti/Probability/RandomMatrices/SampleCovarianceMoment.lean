/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# First moment of sample covariance matrices

Building on `Matrix.re_trace_sampleCovariance`, the expected normalized trace is the mean of the
entrywise second moments. When both dimensions are nonempty and each entry has second moment one,
the expectation is one. Neither independence nor identical distribution is needed.

## Main declarations

* `TauCeti.Probability.integral_one_div_card_mul_re_trace_sampleCovariance`: the expectation identity.
* `TauCeti.Probability.integral_one_div_card_mul_re_trace_sampleCovariance_eq_one`: the unit-moment
  specialization.
-/

public section

open MeasureTheory

namespace TauCeti.Probability

variable {Ω 𝕜 p n : Type*} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype p] [Fintype n]
  {μ : Measure Ω} (X : Ω → Matrix p n 𝕜)

/-- The expected normalized trace of a sample covariance matrix is the average of the entrywise
second moments. The formula also holds when either index type is empty. -/
theorem integral_one_div_card_mul_re_trace_sampleCovariance
    (hX : ∀ i j, Integrable (fun ω ↦ ‖X ω i j‖ ^ 2) μ) :
    ∫ ω, (1 / (Fintype.card p : ℝ)) * RCLike.re (Matrix.sampleCovariance (X ω)).trace ∂μ =
      (1 / ((Fintype.card p : ℝ) * (Fintype.card n : ℝ))) *
        ∑ i, ∑ j, ∫ ω, ‖X ω i j‖ ^ 2 ∂μ := by
  simp_rw [Matrix.re_trace_sampleCovariance]
  simp_rw [← mul_assoc, ← one_div_mul_one_div]
  rw [integral_const_mul, integral_finsetSum _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦ hX i j]
  simp_rw [integral_finsetSum _ fun j _ ↦ hX _ j]

/-- If both dimensions are nonempty and every entry has second moment one, the expected
normalized trace is one. -/
theorem integral_one_div_card_mul_re_trace_sampleCovariance_eq_one [Nonempty p] [Nonempty n]
    (hsecond : ∀ i j, ∫ ω, ‖X ω i j‖ ^ 2 ∂μ = 1) :
    ∫ ω, (1 / (Fintype.card p : ℝ)) * RCLike.re (Matrix.sampleCovariance (X ω)).trace ∂μ =
      1 := by
  have hX : ∀ i j, Integrable (fun ω ↦ ‖X ω i j‖ ^ 2) μ :=
    fun i j ↦ Integrable.of_integral_ne_zero (by rw [hsecond i j]; exact one_ne_zero)
  rw [integral_one_div_card_mul_re_trace_sampleCovariance X hX]
  simp only [hsecond, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hp : (Fintype.card p : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

end TauCeti.Probability
