/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.TruncatedNormal.Basic

/-!
# Regularity of truncated normal cumulative distribution functions

For positive variance, truncation to an interval with extended bounds `l < r` has a
continuous cdf, strictly increasing between the bounds. Its value is positive exactly
above the lower bound and less than one exactly below the upper bound. These statements
include one-sided and unbounded intervals, and are independent of endpoint conventions.
They give the range and uniqueness criteria needed to invert the truncated cdf.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), Chapter 13.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

variable {m : ℝ} {v : ℝ≥0} {s : Set ℝ} {l r : EReal} {x : ℝ}

/-- Conditioning a positive-variance Gaussian on a set of positive mass gives a continuous
cdf, even when the conditioning set is not an interval. -/
theorem continuous_cdf_truncatedNormalMeasure (hv : v ≠ 0)
    (hs : gaussianReal m v s ≠ 0) : Continuous (cdf (truncatedNormalMeasure m v s)) := by
  let _ := isProbabilityMeasure_truncatedNormalMeasure hs
  have : NullSingletonClass (truncatedNormalMeasure m v s) := by
    rw [truncatedNormalMeasure_def]
    exact ⟨fun x ↦ cond_absolutelyContinuous
      (gaussianReal_absolutelyContinuous m hv (measure_singleton x))⟩
  exact Measure.continuous_cdf_of_noAtoms _

/-- The cdf of an interval-truncated positive-variance Gaussian is positive exactly above
its lower extended bound. -/
theorem cdf_truncatedNormalMeasure_pos_iff (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) :
    0 < cdf (truncatedNormalMeasure m v s) x ↔ l < (x : EReal) := by
  have hLR := measureReal_gaussianReal_preimage_Iic_lt (m := m) hv hlr
  have hmono : StrictMono fun t : EReal ↦
      (gaussianReal m v).real (Real.toEReal ⁻¹' Iic t) :=
    fun _ _ h ↦ measureReal_gaussianReal_preimage_Iic_lt hv h
  have hcut := hmono.lt_iff_lt (a := l) (b := (x : EReal))
  simp only [EReal.preimage_coe_Iic, ← cdf_eq_real] at hcut
  rw [cdf_truncatedNormalMeasure_eq hv hlr hs₁ hs₂]
  simpa only [lt_div_iff₀ (sub_pos.mpr hLR), zero_mul, sub_pos, lt_min_iff,
    lt_max_iff, lt_self_iff_false, false_or, hLR, true_and] using hcut

/-- The cdf of an interval-truncated positive-variance Gaussian is less than one exactly
below its upper extended bound. -/
theorem cdf_truncatedNormalMeasure_lt_one_iff (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) :
    cdf (truncatedNormalMeasure m v s) x < 1 ↔ (x : EReal) < r := by
  have hLR := measureReal_gaussianReal_preimage_Iic_lt (m := m) hv hlr
  have hmono : StrictMono fun t : EReal ↦
      (gaussianReal m v).real (Real.toEReal ⁻¹' Iic t) :=
    fun _ _ h ↦ measureReal_gaussianReal_preimage_Iic_lt hv h
  have hcut := hmono.lt_iff_lt (a := (x : EReal)) (b := r)
  simp only [EReal.preimage_coe_Iic, ← cdf_eq_real] at hcut
  rw [cdf_truncatedNormalMeasure_eq hv hlr hs₁ hs₂]
  simpa only [div_lt_one (sub_pos.mpr hLR), sub_lt_sub_iff_right, min_lt_iff,
    lt_self_iff_false, false_or, max_lt_iff, hLR, true_and] using hcut

/-- The cdf of an interval-truncated positive-variance Gaussian is strictly increasing
on the interval interior, including when either bound is infinite. -/
theorem strictMonoOn_cdf_truncatedNormalMeasure (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) :
    StrictMonoOn (cdf (truncatedNormalMeasure m v s)) (Real.toEReal ⁻¹' Ioo l r) := by
  intro x hx y hy hxy
  have hLx := measureReal_gaussianReal_preimage_Iic_lt (m := m) hv hx.1
  have hxR := measureReal_gaussianReal_preimage_Iic_lt (m := m) hv hx.2
  have hLy := measureReal_gaussianReal_preimage_Iic_lt (m := m) hv hy.1
  have hyR := measureReal_gaussianReal_preimage_Iic_lt (m := m) hv hy.2
  simp only [EReal.preimage_coe_Iic, ← cdf_eq_real] at hLx hxR hLy hyR
  simp only [cdf_truncatedNormalMeasure_eq hv hlr hs₁ hs₂,
    max_eq_right hLx.le, min_eq_right hxR.le, max_eq_right hLy.le, min_eq_right hyR.le]
  exact (div_lt_div_iff_of_pos_right
    (sub_pos.mpr (measureReal_gaussianReal_preimage_Iic_lt hv hlr))).2
      (sub_lt_sub_right (strictMono_cdf_gaussianReal m hv hxy) _)

end TauCeti.Probability
