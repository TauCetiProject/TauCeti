/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Closed forms for the real Gaussian density

Mathlib's `ProbabilityTheory.gaussianPDFReal μ v` is stated for a general mean `μ` and variance `v`.
This file records the specialization at the standard parameters `μ = 0`, `v = 1`, where the shift
and the variance both disappear and the density collapses to `(√(2π))⁻¹ · e^{-x²/2}`.

That closed form is what any calculation against the standard Gaussian weight rewrites by, and it
is a statement about the Gaussian distribution alone: it mentions no orthogonal family, so it
belongs here rather than in any of the families that consume it (the Hermite orthogonality
relation and the Gaussian Hermite basis both do).

## Main statements

* `TauCeti.Probability.gaussianPDFReal_zero_one` — `gaussianPDFReal 0 1 x = (√(2π))⁻¹ · e^{-x²/2}`.
* `TauCeti.Probability.gaussianPDFReal_eq_gaussianPDFReal_zero_one` — standardization: for a
  nonzero variance, `gaussianPDFReal m v x = φ ((x - m) / √v) / √v` with `φ = gaussianPDFReal 0 1`.
* `TauCeti.Probability.tendsto_mul_gaussianPDFReal_zero_one_cocompact` — `x φ(x) → 0` as
  `|x| → ∞`, for the standard Gaussian density `φ`.
-/

public section

namespace TauCeti.Probability

open Filter ProbabilityTheory Real
open scoped Topology NNReal

/-- The probability-density form of the standard Gaussian weight:
`gaussianPDFReal 0 1 x = (√(2π))⁻¹ · e^{-x²/2}`. -/
theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [show -x ^ 2 / 2 = -(x ^ 2 / 2) from by ring]

/-- Standardization of the Gaussian density: for a nonzero variance, the density of `N(m, v)` at
`x` is `φ ((x - m) / √v) / √v`, where `φ = gaussianPDFReal 0 1` is the standard Gaussian density. -/
theorem gaussianPDFReal_eq_gaussianPDFReal_zero_one (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    gaussianPDFReal m v x = gaussianPDFReal 0 1 ((x - m) / √(v : ℝ)) / √(v : ℝ) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, div_pow, Real.sq_sqrt hv'.le,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
  field_simp

/-- The standard Gaussian density decays faster than `1 / |x|`: `x φ(x) → 0` as `|x| → ∞`. -/
theorem tendsto_mul_gaussianPDFReal_zero_one_cocompact :
    Tendsto (fun x => x * gaussianPDFReal 0 1 x) (cocompact ℝ) (𝓝 0) := by
  have h := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := 1 / 2) one_half_pos 1).const_mul
    (√(2 * π))⁻¹
  rw [mul_zero] at h
  refine tendsto_zero_iff_norm_tendsto_zero.2 (h.congr fun x => ?_)
  simp only [gaussianPDFReal_zero_one, rpow_one, norm_mul, norm_eq_abs, abs_exp,
    abs_of_pos (inv_pos.2 (sqrt_pos.2 (by positivity : (0 : ℝ) < 2 * π)))]
  ring_nf

end TauCeti.Probability
