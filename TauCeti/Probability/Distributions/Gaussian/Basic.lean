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
* `TauCeti.Probability.tendsto_mul_gaussianPDFReal_zero_one_cocompact` — `x φ(x) → 0` as
  `|x| → ∞`, for the standard Gaussian density `φ`.
-/

public section

namespace TauCeti.Probability

open Filter ProbabilityTheory Real
open scoped Topology

/-- The probability-density form of the standard Gaussian weight:
`gaussianPDFReal 0 1 x = (√(2π))⁻¹ · e^{-x²/2}`. -/
theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [show -x ^ 2 / 2 = -(x ^ 2 / 2) from by ring]

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
