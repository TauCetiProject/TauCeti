/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.SmallJumps
public import TauCeti.Probability.Distributions.Stable.Exponent
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Sine compensation for stable Levy measures

For a non-Gaussian scalar stable law, the compound-Poisson approximations are translated by the
negative integral of `sin` against the cutoff Levy measure. Below shape one, `sin` is integrable
against the full Levy measure and its integral is

`∫ x, sin x ∂stableLevyMeasure α β = β * tan (π * α / 2)`.

Thus the negative full sine compensation at full skewness is exactly the standardized `S1`
location. This identifies the endpoint needed for the one-sided support of a fully skewed stable
law.

The calculation writes the power kernel as a Gamma mixture of exponentials. The Laplace transform
of `sin` is elementary, and the remaining Mellin integral is the existing beta integral for
`1 / (1 + s ^ 2)`.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer, 2020,
  chapter 1.
-/

public section

noncomputable section

open MeasureTheory Real Set

namespace TauCeti.Probability

variable {alpha beta : ℝ}

/-- Below shape one, `sin` is integrable against every stable Levy measure. -/
theorem integrable_sin_stableLevyMeasure (halpha : alpha ∈ Ioo 0 1) (hbeta : |beta| ≤ 1) :
    Integrable sin (stableLevyMeasure alpha beta) := by
  have halpha2 : alpha ∈ Ioo 0 2 := ⟨halpha.1, halpha.2.trans (by norm_num)⟩
  have hin : IntegrableOn sin (Metric.ball (0 : ℝ) 1) (stableLevyMeasure alpha beta) := by
    have hid := (integrableOn_id_stableLevyMeasure_iff halpha2 hbeta one_pos).2 halpha.2
    refine Integrable.mono hid continuous_sin.aestronglyMeasurable.restrict ?_
    filter_upwards with x
    simpa only [Real.norm_eq_abs, id_eq] using Real.abs_sin_le_abs (x := x)
  have hout : IntegrableOn sin (Metric.ball (0 : ℝ) 1)ᶜ
      (stableLevyMeasure alpha beta) := by
    have htail : IntegrableOn sin {x : ℝ | (2 : ℝ)⁻¹ < |x|}
        (stableLevyMeasure alpha beta) := by
      have := isFiniteMeasure_stableLevyMeasure_restrict_abs_gt
        (α := alpha) (β := beta) (by positivity : (0 : ℝ) < 2⁻¹)
      exact Integrable.of_bound (by fun_prop) 1
        (ae_of_all _ fun x ↦ by simpa using abs_sin_le_one x)
    refine htail.mono_set fun x hx ↦ ?_
    have hx' : 1 ≤ |x| := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, mem_compl_iff, not_lt] using hx
    exact lt_of_lt_of_le (by norm_num : (2 : ℝ)⁻¹ < 1) hx'
  rw [← integrableOn_univ, ← Set.union_compl_self (Metric.ball (0 : ℝ) 1)]
  exact IntegrableOn.union hin hout

/-- For `0 < alpha < 1`, sine compensation against the stable Levy measure is the amount
subtracted from the standardized `S0` location to obtain the `S1` location. -/
theorem integral_sin_stableLevyMeasure (halpha : alpha ∈ Ioo 0 1) (hbeta : |beta| ≤ 1) :
    ∫ x, sin x ∂stableLevyMeasure alpha beta = beta * tan (π * alpha / 2) := by
  have halpha2 : alpha ∈ Ioo 0 2 := ⟨halpha.1, halpha.2.trans (by norm_num)⟩
  have hsin := integrable_sin_stableLevyMeasure halpha hbeta
  have hhalf := TauCeti.integral_Ioi_rpow_mul_sin halpha
  have hneg : (∫ x in Ioi (0 : ℝ), x ^ (-(alpha + 1)) • sin (-x)) =
      -(Gamma (alpha + 1))⁻¹ * (π / (2 * cos (π * alpha / 2))) := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), -(x ^ (-(alpha + 1)) • sin x) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
        rw [sin_neg]
        simp only [smul_eq_mul, mul_neg]
      _ = -(∫ x in Ioi (0 : ℝ), x ^ (-(alpha + 1)) • sin x) := by
        rw [integral_neg]
      _ = _ := by rw [hhalf]; ring
  rw [integral_stableLevyMeasure_eq halpha2 hbeta hsin]
  rw [hhalf, hneg]
  simp only [smul_eq_mul]
  have hGamma : Gamma (alpha + 1) ≠ 0 :=
    (Gamma_pos_of_pos (by linarith [halpha.1])).ne'
  have hcos : cos (π * alpha / 2) ≠ 0 := by
    apply (cos_pos_of_mem_Ioo ?_).ne'
    have hangle_pos : 0 < π * alpha / 2 :=
      div_pos (mul_pos pi_pos halpha.1) (by norm_num)
    have hangle_lt : π * alpha / 2 < π / 2 := by
      exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
        (by simpa only [mul_one] using mul_lt_mul_of_pos_left halpha.2 pi_pos)
    exact ⟨(neg_neg_of_pos pi_div_two_pos).trans hangle_pos, hangle_lt⟩
  rw [tan_eq_sin_div_cos]
  rw [add_comm 1 alpha]
  field_simp [hGamma, hcos, pi_ne_zero]
  ring

/-- Below shape one, the negative full sine compensation equals the standardized stable law's
`S1` location. -/
theorem neg_integral_sin_stableLevyMeasure_eq_stableS1Location
    (halpha : alpha ∈ Ioo 0 1) (hbeta : |beta| ≤ 1) :
    -(∫ x, sin x ∂stableLevyMeasure alpha beta) = stableS1Location alpha beta 1 0 := by
  rw [integral_sin_stableLevyMeasure halpha hbeta,
    stableS1Location_of_ne_one (by linarith [halpha.2]) beta (s := 1) 0]
  norm_num

end TauCeti.Probability
