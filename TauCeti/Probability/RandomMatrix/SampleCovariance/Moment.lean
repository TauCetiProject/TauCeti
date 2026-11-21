/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# First moment of sample covariance matrices

Building on `Matrix.re_trace_sampleCovariance`, the expected normalized trace is the mean of the
entrywise second absolute moments, the integrals of `‖X ω i j‖ ^ 2`. When both dimensions are
nonempty and each entry has second absolute moment one, the expectation is one.

## Main declarations

* `TauCeti.Probability.integral_re_trace_sampleCovariance`: the unnormalized trace expectation.
* `TauCeti.Probability.integral_one_div_card_mul_re_trace_sampleCovariance`: the expectation
  identity.
* `TauCeti.Probability.integral_one_div_card_mul_re_trace_sampleCovariance_eq_one`: the normalized
  trace expectation for unit second absolute moments.
* `TauCeti.Probability.integral_trace_sampleCovariance_eq`: the trace identity over the scalar
  field for unit second absolute moments, including empty index types.
-/

public section

open MeasureTheory

namespace TauCeti.Probability

variable {Ω 𝕜 p n : Type*} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype p] [Fintype n]
  {μ : Measure Ω} (X : Ω → Matrix p n 𝕜)

/-- The expected real part of the trace is the sum of entrywise second absolute moments divided
by the column count. The formula holds for empty index types, using `1 / 0 = 0`. -/
theorem integral_re_trace_sampleCovariance
    (hX : ∀ i j, Integrable (fun ω ↦ ‖X ω i j‖ ^ 2) μ) :
    ∫ ω, RCLike.re (Matrix.sampleCovariance (X ω)).trace ∂μ =
      (1 / (Fintype.card n : ℝ)) * ∑ i, ∑ j, ∫ ω, ‖X ω i j‖ ^ 2 ∂μ := by
  simp_rw [Matrix.re_trace_sampleCovariance]
  rw [integral_const_mul, integral_finsetSum _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦ hX i j]
  simp_rw [integral_finsetSum _ fun j _ ↦ hX _ j]

/-- The expected normalized trace of a sample covariance matrix is the average of the entrywise
second absolute moments. The formula also holds when either index type is empty. -/
theorem integral_one_div_card_mul_re_trace_sampleCovariance
    (hX : ∀ i j, Integrable (fun ω ↦ ‖X ω i j‖ ^ 2) μ) :
    ∫ ω, (1 / (Fintype.card p : ℝ)) * RCLike.re (Matrix.sampleCovariance (X ω)).trace ∂μ =
      (1 / ((Fintype.card p : ℝ) * (Fintype.card n : ℝ))) *
        ∑ i, ∑ j, ∫ ω, ‖X ω i j‖ ^ 2 ∂μ := by
  rw [integral_const_mul, integral_re_trace_sampleCovariance X hX, ← mul_assoc,
    ← one_div_mul_one_div]

/-- With unit entrywise second absolute moments, the expected trace is the number of entries
divided by the column count. With empty columns, the inverse and trace are both zero. -/
theorem integral_trace_sampleCovariance_eq
    (hsecond : ∀ i j, ∫ ω, ‖X ω i j‖ ^ 2 ∂μ = 1) :
    ∫ ω, (X ω).sampleCovariance.trace ∂μ =
      (Fintype.card n : 𝕜)⁻¹ * (Fintype.card p * Fintype.card n : ℕ) := by
  have hint (i : p) (j : n) : Integrable (fun ω ↦ ‖X ω i j‖ ^ 2) μ :=
    Integrable.of_integral_ne_zero (by rw [hsecond i j]; exact one_ne_zero)
  have htrace (ω : Ω) :
      (X ω).sampleCovariance.trace = ((RCLike.re (X ω).sampleCovariance.trace : ℝ) : 𝕜) := by
    symm
    apply RCLike.conj_eq_iff_re.mp
    rw [← RCLike.star_def, ← Matrix.trace_conjTranspose,
      (Matrix.isHermitian_sampleCovariance _).eq]
  rw [integral_congr_ae (.of_forall htrace), integral_ofReal,
    integral_re_trace_sampleCovariance X hint]
  simp [hsecond]

/-- If both dimensions are nonempty and every entry has second absolute moment one, the expected
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
