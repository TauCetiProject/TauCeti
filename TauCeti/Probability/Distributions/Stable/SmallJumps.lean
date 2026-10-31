/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.LevyMeasure
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Small-jump moments of stable Lévy measures

On a neighbourhood of zero, the absolute `q`th jump moment of a non-Gaussian stable Lévy
measure is finite exactly when `α < q`. Its value is independent of skewness and is a
constant times `r ^ (q - α)`. In particular, the small-jump second moment tends to zero,
whereas the first absolute moment is finite exactly below shape one.

These estimates supply variance control for centered small-jump sums and first-moment
control for identifying the support endpoints of one-sided stable laws.
The proofs reuse the existing stable Lévy half-line decomposition and radial-power
integrability, with Mathlib's sharp interval-power criterion and power integral.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory Real Set Filter
open scoped Topology

namespace TauCeti.Probability

variable {α β q r : ℝ}

private lemma density_mul_abs_rpow (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    {x : ℝ} (hx : x ≠ 0) :
    stableLevyDensity α β x * |x| ^ q =
      (Gamma (1 + α) * sin (π * α / 2) / π) *
        (if 0 < x then 1 + β else 1 - β) * |x| ^ (q - α - 1) := by
  rw [stableLevyDensity_of_ne_zero hα hβ hx, mul_assoc,
    ← rpow_add (abs_pos.mpr hx)]
  congr 1
  congr 1
  ring

/-- Absolute jump powers above the stable shape are integrable on every bounded ball about
zero. This is local integrability of the Lévy measure, rather than a stable-law moment. -/
theorem integrableOn_abs_rpow_stableLevyMeasure (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (hq : α < q) (r : ℝ) :
    IntegrableOn (fun x : ℝ ↦ |x| ^ q) (Metric.ball 0 r) (stableLevyMeasure α β) := by
  rw [← integrable_indicator_iff measurableSet_ball,
    integrable_stableLevyDensity_smul_iff]
  have hp := (TauCeti.integrableOn_norm_rpow_ball (mu := (volume : Measure ℝ))
    (s := q - α - 1) (by simp only [Module.finrank_self, Nat.cast_one]; linarith)
    (R := r)).const_mul (2 * (Gamma (1 + α) * sin (π * α / 2) / π))
  have hd : Measurable (stableLevyDensity α β) :=
    measurable_stableLevyDensity.comp
      (measurable_const.prodMk measurable_id : Measurable fun x : ℝ ↦ ((α, β), x))
  refine ((integrable_indicator_iff measurableSet_ball).mpr hp).mono'
    (hd.aestronglyMeasurable.smul
      ((by fun_prop : Measurable fun x : ℝ ↦ |x| ^ q).aestronglyMeasurable.indicator
        measurableSet_ball)) ?_
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  by_cases hxr : x ∈ Metric.ball (0 : ℝ) r
  · simp only [indicator_of_mem hxr, smul_eq_mul]
    rw [Real.norm_of_nonneg (mul_nonneg (stableLevyDensity_nonneg _ _ _)
      (rpow_nonneg (abs_nonneg _) _)), density_mul_abs_rpow hα hβ hx]
    have hb : (if 0 < x then 1 + β else 1 - β) ≤ 2 := by
      split_ifs <;> linarith [(abs_le.mp hβ).1, (abs_le.mp hβ).2]
    simpa only [Real.norm_eq_abs, mul_comm (2 : ℝ)] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (stableLevyDensity_coefficient_pos hα).le)
      (rpow_nonneg (abs_nonneg x) (q - α - 1))
  · simp [indicator_of_notMem hxr]

private lemma lt_of_integrableOn_abs_rpow (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (hβ' : -1 < β) (hr : 0 < r)
    (h : IntegrableOn (fun x : ℝ ↦ |x| ^ q) (Metric.ball 0 r)
      (stableLevyMeasure α β)) : α < q := by
  have hh := (integrable_stableLevyDensity_smul_iff α β).mp
    ((integrable_indicator_iff measurableSet_ball).mpr h)
  have hsub : Ioo (0 : ℝ) r ⊆ Metric.ball 0 r := by
    intro x hx
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hx.1] using hx.2
  have hi := hh.integrableOn (s := Ioo 0 r)
  have heq : EqOn (fun x ↦ stableLevyDensity α β x •
      (Metric.ball (0 : ℝ) r).indicator (fun x ↦ |x| ^ q) x)
      (fun x : ℝ ↦ (Gamma (1 + α) * sin (π * α / 2) / π * (1 + β)) *
        x ^ (q - α - 1)) (Ioo 0 r) := by
    intro x hx
    dsimp only
    rw [indicator_of_mem (hsub hx), smul_eq_mul, density_mul_abs_rpow hα hβ hx.1.ne',
      ite_eq_left hx.1, abs_of_pos hx.1]
  have hp := (integrableOn_congr_fun heq measurableSet_Ioo).mp hi
  have hc : Gamma (1 + α) * sin (π * α / 2) / π * (1 + β) ≠ 0 :=
    (mul_pos (stableLevyDensity_coefficient_pos hα) (by linarith)).ne'
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mp
    ((integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _).mp hp)
  linarith

/-- The exact small-jump absolute-moment threshold. At the critical exponent the moment
diverges, including for either fully skewed Lévy measure. -/
theorem integrableOn_abs_rpow_stableLevyMeasure_iff (hα : α ∈ Ioo 0 2)
    (hβ : |β| ≤ 1) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ ↦ |x| ^ q) (Metric.ball 0 r) (stableLevyMeasure α β) ↔ α < q := by
  refine ⟨fun h ↦ ?_, fun hq ↦ integrableOn_abs_rpow_stableLevyMeasure hα hβ hq r⟩
  by_cases hb : -1 < β
  · exact lt_of_integrableOn_abs_rpow hα hβ hb hr h
  · have hreflect : MeasurePreserving (fun x : ℝ ↦ -x)
        (stableLevyMeasure α (-β)) (stableLevyMeasure α β) := by
      exact ⟨measurable_neg, by simpa using map_neg_stableLevyMeasure α (-β)⟩
    have hh := (hreflect.integrableOn_comp_preimage
      (MeasurableEquiv.neg ℝ).measurableEmbedding).mpr h
    have hpre : (fun x : ℝ ↦ -x) ⁻¹' Metric.ball 0 r = Metric.ball 0 r := by
      ext x
      simp [Metric.mem_ball]
    rw [hpre] at hh
    exact lt_of_integrableOn_abs_rpow (β := -β) hα (by simpa using hβ)
      (by linarith [(abs_le.mp hβ).1]) hr (by simpa only [Function.comp_def, abs_neg] using hh)

/-- The small-jump absolute `q`th moment is independent of skewness. The strict exponent
hypothesis ensures integrability, including at the singularity at zero. -/
theorem integral_abs_rpow_stableLevyMeasure_ball (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (hq : α < q) (hr : 0 ≤ r) :
    ∫ x in Metric.ball (0 : ℝ) r, |x| ^ q ∂stableLevyMeasure α β =
      2 * (Gamma (1 + α) * sin (π * α / 2) / π) * r ^ (q - α) / (q - α) := by
  have hi := (integrable_indicator_iff measurableSet_ball).mpr
    (integrableOn_abs_rpow_stableLevyMeasure hα hβ hq r)
  rw [← integral_indicator measurableSet_ball, integral_stableLevyMeasure_eq hα hβ hi]
  have hhalf : (∫ x in Ioi (0 : ℝ), x ^ (-(α + 1)) •
      (Metric.ball (0 : ℝ) r).indicator (fun x ↦ |x| ^ q) x) =
      r ^ (q - α) / (q - α) := by
    have heq : EqOn (fun x : ℝ ↦ x ^ (-(α + 1)) •
        (Metric.ball (0 : ℝ) r).indicator (fun x ↦ |x| ^ q) x)
        ((Ioo (0 : ℝ) r).indicator fun x ↦ x ^ (q - α - 1)) (Ioi 0) := by
      intro x (hx : 0 < x)
      by_cases hxr : x < r
      · have hxball : x ∈ Metric.ball (0 : ℝ) r := by
          simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hx] using hxr
        simp only [indicator_of_mem hxball, indicator_of_mem (s := Ioo (0 : ℝ) r) ⟨hx, hxr⟩,
          abs_of_pos hx, smul_eq_mul, ← rpow_add hx]
        congr 1
        ring
      · have hxball : x ∉ Metric.ball (0 : ℝ) r := by
          simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hx] using hxr
        simp [indicator_of_notMem hxball, hxr]
    rw [setIntegral_congr_fun measurableSet_Ioi heq, setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hr, integral_rpow (Or.inl (by linarith)),
      Real.zero_rpow (by linarith : q - α - 1 + 1 ≠ 0), sub_zero]
    have he : q - α - 1 + 1 = q - α := by ring
    rw [he]
  have hneg (x : ℝ) : (Metric.ball (0 : ℝ) r).indicator (fun x ↦ |x| ^ q) (-x) =
      (Metric.ball (0 : ℝ) r).indicator (fun x ↦ |x| ^ q) x := by
    simp [indicator, Metric.mem_ball]
  simp_rw [hneg, hhalf]
  simp only [smul_eq_mul]
  ring

/-- The sum of the absolute sizes of small stable jumps has finite expectation exactly
below shape one. In particular, shape one belongs to the divergent side. -/
theorem integrableOn_id_stableLevyMeasure_iff (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (hr : 0 < r) :
    IntegrableOn (fun x : ℝ ↦ x) (Metric.ball 0 r) (stableLevyMeasure α β) ↔ α < 1 := by
  rw [IntegrableOn, ← integrable_norm_iff (by fun_prop)]
  simpa only [IntegrableOn, Real.norm_eq_abs, rpow_one] using
    (integrableOn_abs_rpow_stableLevyMeasure_iff (q := 1) hα hβ hr)

/-- The exact second moment of stable jumps smaller than `r`, the quantity controlling
the variance of centered small-jump remainders. -/
theorem integral_sq_stableLevyMeasure_ball (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (hr : 0 ≤ r) :
    ∫ x in Metric.ball (0 : ℝ) r, x ^ 2 ∂stableLevyMeasure α β =
      2 * (Gamma (1 + α) * sin (π * α / 2) / π) * r ^ (2 - α) / (2 - α) := by
  simpa only [rpow_two, sq_abs] using
    integral_abs_rpow_stableLevyMeasure_ball hα hβ hα.2 hr

/-- Every finite absolute small-jump moment vanishes as its cutoff shrinks to zero. -/
theorem tendsto_integral_abs_rpow_stableLevyMeasure_ball_zero (hα : α ∈ Ioo 0 2)
    (hβ : |β| ≤ 1) (hq : α < q) :
    Tendsto (fun r : ℝ ↦ ∫ x in Metric.ball (0 : ℝ) r, |x| ^ q ∂stableLevyMeasure α β)
      (𝓝[≥] 0) (𝓝 0) := by
  have hp : 0 < q - α := sub_pos.mpr hq
  have ht := (((continuousAt_rpow_const (0 : ℝ) (q - α) (Or.inr hp.le)).tendsto.const_mul
    (2 * (Gamma (1 + α) * sin (π * α / 2) / π))).div_const (q - α)).mono_left
      (nhdsWithin_le_nhds (s := Ici (0 : ℝ)))
  simp only [Real.zero_rpow hp.ne', mul_zero, zero_div] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (integral_abs_rpow_stableLevyMeasure_ball hα hβ hq hr).symm

/-- The variance contribution of jumps below a shrinking cutoff tends to zero. -/
theorem tendsto_integral_sq_stableLevyMeasure_ball_zero (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) :
    Tendsto (fun r : ℝ ↦ ∫ x in Metric.ball (0 : ℝ) r, x ^ 2 ∂stableLevyMeasure α β)
      (𝓝[≥] 0) (𝓝 0) := by
  simpa only [rpow_two, sq_abs] using
    tendsto_integral_abs_rpow_stableLevyMeasure_ball_zero hα hβ hα.2

end TauCeti.Probability
