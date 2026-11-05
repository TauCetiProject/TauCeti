/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Approximation.Basic
public import TauCeti.Probability.Distributions.Stable.Tails
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
theorem tendsto_rpow_mul_real_stableCompensatedPoissonMeasure_Ioi
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
    rw [measureReal_def, cond_apply' measurableSet_Ioi, inter_eq_right.mpr hsub,
      ENNReal.toReal_mul, ENNReal.toReal_inv]
    dsimp [a, ν]
    ring
  have hsum := tendsto_rpow_mul_real_compoundPoissonMeasure_Ioi (ν A).toNNReal hα.1 hjump
  rw [ENNReal.coe_toNNReal_eq_toReal, mul_div_cancel₀ _ ha] at hsum
  -- Translation by the fixed compensator preserves a power-law tail constant.
  have hxadd : Tendsto (fun x : ℝ ↦ x + c) atTop atTop :=
    tendsto_atTop_add_const_right atTop c tendsto_id
  have hratio : Tendsto (fun x : ℝ ↦ x / (x + c)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := c)).div_atTop hxadd
    have h' : Tendsto (fun x : ℝ ↦ 1 - c / (x + c)) atTop (𝓝 1) := by
      simpa using h.const_sub 1
    apply h'.congr'
    filter_upwards [eventually_gt_atTop (-c)] with x hx
    field_simp [(by linarith : x + c ≠ 0)]
    ring
  have h := (hratio.rpow_const (p := α) (Or.inl one_ne_zero)).mul (hsum.comp hxadd)
  simp only [one_rpow, one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop (-c)] with x hx hxc
  have hx' : 0 < x + c := by linarith
  have hpre : (fun y : ℝ ↦ y - c) ⁻¹' Ioi x = Ioi (x + c) := by
    ext y
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [stableCompensatedPoissonMeasure_def, map_measureReal_apply (by fun_prop)
    measurableSet_Ioi, hpre]
  simp only [Function.comp_apply, ν, A]
  rw [div_rpow hx.le hx'.le]
  field_simp [(rpow_pos_of_pos hx' α).ne']

/-- The compensated large jumps have the left-tail constant of the stable Lévy intensity,
independently of the positive cutoff. At full positive skewness this constant is zero. -/
theorem tendsto_rpow_mul_real_stableCompensatedPoissonMeasure_Iio_neg
    {α β ε : ℝ} (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) :
    Tendsto (fun x : ℝ ↦ x ^ α *
      (stableCompensatedPoissonMeasure α β ε).real (Iio (-x))) atTop
      (𝓝 (stableTailConstant α * (1 - β))) := by
  let ν := stableLevyMeasure α β
  let A := {y : ℝ | ε < |y|}
  let a := (ν A).toReal
  let c := ∫ y in A, sin y ∂ν
  let _ := isProbabilityMeasure_cond_stableLevyMeasure hα hβ hε
  have ha : a ≠ 0 := ENNReal.toReal_ne_zero.mpr
    ⟨(stableLevyMeasure_abs_gt_pos hα hβ hε).ne', stableLevyMeasure_abs_gt_ne_top hε⟩
  have hjump : Tendsto (fun x : ℝ ↦ x ^ α * (cond ν A).real (Iio (-x))) atTop
      (𝓝 (stableTailConstant α * (1 - β) / a)) := by
    apply ((tendsto_rpow_mul_toReal_stableLevyMeasure_Iio hα hβ).div_const a).congr'
    filter_upwards [eventually_gt_atTop ε] with x hx
    have hsub : Iio (-x) ⊆ A := by
      intro y hy
      have hxy : x < -y := by
        simpa only [neg_neg] using neg_lt_neg (mem_Iio.mp hy)
      exact hx.trans (hxy.trans_le (neg_le_abs y))
    rw [measureReal_def, cond_apply' measurableSet_Iio, inter_eq_right.mpr hsub,
      ENNReal.toReal_mul, ENNReal.toReal_inv]
    dsimp [a, ν]
    ring
  have hsum := tendsto_rpow_mul_real_compoundPoissonMeasure_Iio_neg (ν A).toNNReal hα.1 hjump
  rw [ENNReal.coe_toNNReal_eq_toReal, mul_div_cancel₀ _ ha] at hsum
  -- Translation by the fixed compensator preserves a power-law tail constant.
  have hxadd : Tendsto (fun x : ℝ ↦ x - c) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-c) tendsto_id
  have hratio : Tendsto (fun x : ℝ ↦ x / (x - c)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := c)).div_atTop hxadd
    have h' : Tendsto (fun x : ℝ ↦ 1 + c / (x - c)) atTop (𝓝 1) := by
      simpa using h.const_add 1
    apply h'.congr'
    filter_upwards [eventually_gt_atTop c] with x hx
    field_simp [(by linarith : x - c ≠ 0)]
    ring
  have h := (hratio.rpow_const (p := α) (Or.inl one_ne_zero)).mul (hsum.comp hxadd)
  simp only [one_rpow, one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop c] with x hx hxc
  have hx' : 0 < x - c := by linarith
  have hpre : (fun y : ℝ ↦ y - c) ⁻¹' Iio (-x) = Iio (-(x - c)) := by
    ext y
    simp only [mem_preimage, mem_Iio]
    constructor <;> intro h <;> linarith
  rw [stableCompensatedPoissonMeasure_def, map_measureReal_apply (by fun_prop)
    measurableSet_Iio, hpre]
  simp only [Function.comp_apply, ν, A]
  rw [div_rpow hx.le hx'.le]
  field_simp [(rpow_pos_of_pos hx' α).ne']

end TauCeti.Probability
