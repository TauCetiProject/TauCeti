/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.OwensT
public import TauCeti.Probability.Distributions.Gaussian.Basic
public import TauCeti.Probability.Distributions.Gaussian.Cdf

/-!
# Owen's T function and the standard Gaussian law

Write `φ = gaussianPDFReal 0 1` and `Φ = cdf (gaussianReal 0 1)` for the standard Gaussian density
and cumulative distribution function. This file proves the identities that tie Owen's T function
`Real.owensT` to them:

* the derivative in the first argument, `∂T(h, a)/∂h = -φ(h) * (Φ(a * h) - 1 / 2)`;
* the derivative `2 * φ(x) * Φ(α * x)` of `x ↦ Φ(x) - 2 * T(x, α)`, with limits `0` and `1` at
  `-∞` and `+∞`;
* the Gaussian integral identity `∫ t in Iic x, 2 * φ(t) * Φ(α * t) = Φ(x) - 2 * T(x, α)` and the
  normalization `∫ t, 2 * φ(t) * Φ(α * t) = 1`.

The function `t ↦ 2 * φ(t) * Φ(α * t)` is the density of the standard skew-normal law with shape
`α`, so these identities say that `Φ(x) - 2 * T(x, α)` is its cumulative distribution function.

## Main declarations

* `Real.hasDerivAt_owensT_left` — the derivative of Owen's T function in `h`.
* `TauCeti.Probability.hasDerivAt_cdf_gaussianReal_sub_two_mul_owensT` and
  `TauCeti.Probability.tendsto_cdf_gaussianReal_sub_two_mul_owensT_atBot`,
  `TauCeti.Probability.tendsto_cdf_gaussianReal_sub_two_mul_owensT_atTop` — derivative and limits
  of `Φ(x) - 2 * T(x, α)`.
* `TauCeti.Probability.integral_Iic_two_mul_gaussianPDFReal_mul_cdf_gaussianReal` and
  `TauCeti.Probability.integral_two_mul_gaussianPDFReal_mul_cdf_gaussianReal` — the Gaussian
  integral identity and the normalization.

## References

* D. B. Owen, *Tables for computing bivariate normal probabilities*, Annals of Mathematical
  Statistics 27 (1956), 1075–1090.
* A. Azzalini and A. Capitanio, *The Skew-Normal and Related Families*, Cambridge University
  Press, 2014.
-/

public section

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory TauCeti.Probability
open scoped Topology NNReal

namespace Real

/-- The derivative of Owen's T function in its first argument is
`-φ(h) * (Φ(a * h) - 1 / 2)`, where `φ` and `Φ` are the standard Gaussian density and cdf. -/
theorem hasDerivAt_owensT_left (h a : ℝ) :
    HasDerivAt (fun h => owensT h a)
      (-(gaussianPDFReal 0 1 h * (cdf (gaussianReal 0 1) (a * h) - 1 / 2))) h := by
  -- The derivative of the integrand factors as `-2π * φ(h) * (h * φ(h * t))`.
  have hsplit (t : ℝ) : -h * rexp (-h ^ 2 * (1 + t ^ 2) / 2) =
      -(2 * π * gaussianPDFReal 0 1 h) * (h * gaussianPDFReal 0 1 (h * t)) := by
    have hc : 2 * π * ((√(2 * π))⁻¹ * (√(2 * π))⁻¹) = 1 := by
      rw [← mul_inv, mul_self_sqrt (by positivity), mul_inv_cancel₀ (by positivity)]
    have hexp : rexp (-h ^ 2 * (1 + t ^ 2) / 2) = rexp (-h ^ 2 / 2) * rexp (-(h * t) ^ 2 / 2) := by
      rw [← exp_add]
      ring_nf
    rw [gaussianPDFReal_zero_one, gaussianPDFReal_zero_one, hexp]
    simp only [neg_div]
    linear_combination
      (h * rexp (-(h ^ 2 / 2)) * rexp (-((h * t) ^ 2 / 2))) * hc
  -- Substituting `s = h * t` leaves the Gaussian mass of `[0, a * h]`.
  have hmass : h * ∫ t in (0 : ℝ)..a, gaussianPDFReal 0 1 (h * t) =
      cdf (gaussianReal 0 1) (a * h) - 1 / 2 := by
    rw [← smul_eq_mul, intervalIntegral.smul_integral_comp_mul_left, mul_zero, mul_comm h a,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hasDerivAt_cdf_gaussianReal 0 one_ne_zero x)
        (integrable_gaussianPDFReal 0 1).intervalIntegrable,
      cdf_gaussianReal_zero_one 0]
    simp
  convert (hasDerivAt_intervalIntegral_owensT h a).const_mul (2 * π)⁻¹ using 1
  · funext x
    exact owensT_def x a
  · simp only [hsplit, intervalIntegral.integral_const_mul, hmass]
    field_simp

end Real

namespace TauCeti.Probability

/-- The function `x ↦ Φ(x) - 2 * T(x, α)` has derivative `2 * φ(x) * Φ(α * x)`, the standard
skew-normal density with shape `α`. -/
theorem hasDerivAt_cdf_gaussianReal_sub_two_mul_owensT (α x : ℝ) :
    HasDerivAt (fun x => cdf (gaussianReal 0 1) x - 2 * Real.owensT x α)
      (2 * gaussianPDFReal 0 1 x * cdf (gaussianReal 0 1) (α * x)) x := by
  convert (hasDerivAt_cdf_gaussianReal 0 one_ne_zero x).sub
    ((Real.hasDerivAt_owensT_left x α).const_mul 2) using 1
  ring

/-- `Φ(x) - 2 * T(x, α)` tends to `0` as `x → -∞`. -/
theorem tendsto_cdf_gaussianReal_sub_two_mul_owensT_atBot (α : ℝ) :
    Tendsto (fun x => cdf (gaussianReal 0 1) x - 2 * Real.owensT x α) atBot (𝓝 0) := by
  simpa using (tendsto_cdf_atBot (gaussianReal 0 1)).sub ((Real.tendsto_owensT_atBot α).const_mul 2)

/-- `Φ(x) - 2 * T(x, α)` tends to `1` as `x → ∞`. -/
theorem tendsto_cdf_gaussianReal_sub_two_mul_owensT_atTop (α : ℝ) :
    Tendsto (fun x => cdf (gaussianReal 0 1) x - 2 * Real.owensT x α) atTop (𝓝 1) := by
  simpa using (tendsto_cdf_atTop (gaussianReal 0 1)).sub ((Real.tendsto_owensT_atTop α).const_mul 2)

/-- The standard skew-normal density `t ↦ 2 * φ(t) * Φ(α * t)` is integrable. -/
theorem integrable_two_mul_gaussianPDFReal_mul_cdf_gaussianReal (α : ℝ) :
    Integrable fun t => 2 * gaussianPDFReal 0 1 t * cdf (gaussianReal 0 1) (α * t) := by
  refine ((integrable_gaussianPDFReal 0 1).const_mul 2).mono' ?_ (ae_of_all _ fun t => ?_)
  · exact ((measurable_const.mul (measurable_gaussianPDFReal 0 1)).mul
      ((monotone_cdf _).measurable.comp (measurable_const_mul α))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by
      have := gaussianPDFReal_nonneg 0 1 t
      have := cdf_nonneg (gaussianReal 0 1) (α * t)
      positivity)]
    have := gaussianPDFReal_nonneg 0 1 t
    exact mul_le_of_le_one_right (by positivity) (cdf_le_one _ _)

/-- **The skew-normal cdf through Owen's T function.** The standard skew-normal density with shape
`α` integrates over `(-∞, x]` to `Φ(x) - 2 * T(x, α)`. -/
theorem integral_Iic_two_mul_gaussianPDFReal_mul_cdf_gaussianReal (α x : ℝ) :
    ∫ t in Iic x, 2 * gaussianPDFReal 0 1 t * cdf (gaussianReal 0 1) (α * t) =
      cdf (gaussianReal 0 1) x - 2 * Real.owensT x α := by
  rw [integral_Iic_of_hasDerivAt_of_tendsto'
    (fun t _ => hasDerivAt_cdf_gaussianReal_sub_two_mul_owensT α t)
    (integrable_two_mul_gaussianPDFReal_mul_cdf_gaussianReal α).integrableOn
    (tendsto_cdf_gaussianReal_sub_two_mul_owensT_atBot α), sub_zero]

/-- The standard skew-normal density with shape `α` has total integral `1`. -/
theorem integral_two_mul_gaussianPDFReal_mul_cdf_gaussianReal (α : ℝ) :
    ∫ t, 2 * gaussianPDFReal 0 1 t * cdf (gaussianReal 0 1) (α * t) = 1 := by
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_cdf_gaussianReal_sub_two_mul_owensT α)
    (integrable_two_mul_gaussianPDFReal_mul_cdf_gaussianReal α)
    (tendsto_cdf_gaussianReal_sub_two_mul_owensT_atBot α)
    (tendsto_cdf_gaussianReal_sub_two_mul_owensT_atTop α), sub_zero]

end TauCeti.Probability
