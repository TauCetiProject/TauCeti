/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Approximation.Basic
public import TauCeti.Probability.Distributions.Stable.Tails
import TauCeti.Probability.ConditionalProbability
import TauCeti.Probability.Distributions.CompoundPoisson.Tail

/-!
# Tail constants of stable large-jump components

At every positive cutoff, the compensated compound-Poisson component of a non-Gaussian
stable law has the same right and left power-law tail constants as its Lévy intensity.
Normalization of the jump law cancels the Poisson rate, and the fixed sine compensator
does not affect the leading tail term. Both fully skewed boundaries and shape one are included.

These are tail asymptotics of the finite-intensity component. Transferring them to the stable
law additionally requires control of the independent small-jump remainder.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology ENNReal NNReal

namespace TauCeti.Probability

/-- The compensated large jumps have the right-tail constant of the stable Lévy intensity,
independently of the positive cutoff. At full negative skewness this constant is zero. -/
theorem tendsto_rpow_mul_stableCompensatedPoissonMeasure_real_Ioi
    {α β ε : ℝ} (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) :
    Tendsto (fun x : ℝ ↦ x ^ α *
      (stableCompensatedPoissonMeasure α β ε).real (Ioi x)) atTop
      (𝓝 (stableTailConstant α * (1 + β))) := by
  let ν := stableLevyMeasure α β
  let A := {y : ℝ | ε < |y|}
  let a := (ν A).toReal
  let c := ∫ y in A, sin y ∂ν
  let _ := isProbabilityMeasure_cond_stableLevyMeasure hα hβ hε
  have ha : a ≠ 0 := ENNReal.toReal_ne_zero.mpr
    ⟨(stableLevyMeasure_abs_gt_pos hα hβ hε).ne', stableLevyMeasure_abs_gt_ne_top hε⟩
  have hjump : Tendsto (fun x : ℝ ↦ x ^ α * (cond ν A).real (Ioi x)) atTop
      (𝓝 (stableTailConstant α * (1 + β) / a)) := by
    apply ((tendsto_rpow_mul_toReal_stableLevyMeasure_Ioi hα hβ).div_const a).congr'
    filter_upwards [eventually_gt_atTop ε] with x hx
    have hsub : Ioi x ⊆ A := by
      intro y hy
      exact hx.trans (hy.trans_le (le_abs_self y))
    rw [cond_real_of_subset measurableSet_Ioi hsub, mul_div_assoc]
    simp only [measureReal_def, ν, a]
  have hsum := tendsto_rpow_mul_compoundPoissonMeasure_real_Ioi (ν A).toNNReal hα.1 hjump
  rw [ENNReal.coe_toNNReal_eq_toReal, mul_div_cancel₀ _ ha] at hsum
  apply (hsum.rpow_mul_comp_add c).congr
  intro x
  have hpre : (fun y : ℝ ↦ y - c) ⁻¹' Ioi x = Ioi (x + c) := by
    ext y
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [stableCompensatedPoissonMeasure_def, map_measureReal_apply (by fun_prop)
    measurableSet_Ioi, hpre]

/-- The compensated large jumps have the left-tail constant of the stable Lévy intensity,
independently of the positive cutoff. At full positive skewness this constant is zero. -/
theorem tendsto_rpow_mul_stableCompensatedPoissonMeasure_real_Iio_neg
    {α β ε : ℝ} (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) :
    Tendsto (fun x : ℝ ↦ x ^ α *
      (stableCompensatedPoissonMeasure α β ε).real (Iio (-x))) atTop
      (𝓝 (stableTailConstant α * (1 - β))) := by
  have h := tendsto_rpow_mul_stableCompensatedPoissonMeasure_real_Ioi (β := -β) hα
    (by simpa only [abs_neg] using hβ) hε
  rw [← map_neg_stableCompensatedPoissonMeasure α β ε] at h
  simpa only [Measure.map_neg_real_Ioi, sub_eq_add_neg, neg_neg] using h

end TauCeti.Probability
