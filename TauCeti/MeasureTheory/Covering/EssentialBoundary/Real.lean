/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Covering.EssentialBoundary
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Indicator

/-!
# Essential boundary points on the line

On an open interval `(a, b) ⊆ ℝ` without points of the essential boundary `∂ᵉs` of a
null-measurable set `s`, the set is almost everywhere empty or almost everywhere full
(`TauCeti.Real.measure_inter_Ioo_eq_zero_or_measure_Ioo_sdiff_eq_zero`).

## Proof

Let `F y = ∫_a^y 1_s`. At a point of density zero, `|F (x + h) - F x| ≤ |s ∩ [x - |h|, x + |h|]|`
is `o(h)`, so `F' x = 0`; at a point of density one the same argument for the complement gives
`F' x = 1`. So the derivative of `F` takes only the values `0` and `1` on `(a, b)`, and by the mean
value theorem so does the slope `|s ∩ (a, b]| / (b - a)`.

## Main results

* `TauCeti.Real.hasDerivAt_integral_indicator_of_hasDensityAt_zero` and
  `TauCeti.Real.hasDerivAt_integral_indicator_of_hasDensityAt_one`: the primitive of `1_s` is
  differentiable at points of density zero and one, with derivative the density.
* `TauCeti.Real.measure_inter_Ioo_eq_zero_or_measure_Ioo_sdiff_eq_zero`: on an interval without
  essential boundary points a null-measurable set is null or conull.
-/

public section

open Filter Set MeasureTheory Metric Asymptotics
open scoped Topology ENNReal Interval

namespace TauCeti.Real

variable {s : Set ℝ} {x : ℝ}

/-- `TauCeti.Real.hasDerivAt_integral_indicator_of_hasDensityAt_zero` for a measurable set. -/
private theorem hasDerivAt_integral_indicator_of_hasDensityAt_zero_aux (hs : MeasurableSet s)
    (a : ℝ)
    (h : HasDensityAt volume s x 0) :
    HasDerivAt (fun y => ∫ t in a..y, s.indicator (1 : ℝ → ℝ) t) 0 x := by
  have hint := intervalIntegrable_indicator_one (μ := volume) hs.nullMeasurableSet
  rw [hasDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  -- The proportion of `s` in small closed balls around `x` is below `c / 2`.
  have hev := (hasDensityAt_iff.1 h).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hc)))
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  rw [smul_zero, sub_zero, intervalIntegral.integral_interval_sub_left (hint a (x + h))
    (hint a x)]
  rcases eq_or_ne h 0 with rfl | h0
  · simp
  have hr : 0 < |h| := abs_pos.2 h0
  have hlt := hδP (y := |h|) (by simpa using hh) hr
  have hB : volume (closedBall x |h|) = ENNReal.ofReal (2 * |h|) := by
    rw [Real.volume_closedBall]
  -- So `|s ∩ B(x, |h|)| < c |h|`.
  have hm : volume (s ∩ closedBall x |h|) ≤ ENNReal.ofReal (c * |h|) := by
    rw [hB, ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_pos.2 (by positivity)).ne')
      (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_mul (by positivity)] at hlt
    exact hlt.le.trans_eq (by ring_nf)
  have hsub : Ι x (x + h) ⊆ closedBall x |h| := by
    refine (uIoc_subset_uIcc.trans (uIcc_subset_Icc ?_ ?_)).trans Real.closedBall_eq_Icc.ge
    · constructor <;> linarith [abs_nonneg h]
    · constructor <;> linarith [neg_abs_le h, le_abs_self h]
  simp only [intervalIntegral.norm_integral_eq_norm_integral_uIoc, integral_indicator_one hs,
    measureReal_restrict_apply hs, Real.norm_of_nonneg measureReal_nonneg]
  calc volume.real (s ∩ Ι x (x + h)) ≤ volume.real (s ∩ closedBall x |h|) :=
        measureReal_mono (inter_subset_inter_right _ hsub)
          (measure_ne_top_of_subset inter_subset_right
            (by simp [Real.volume_closedBall, ENNReal.mul_eq_top]))
    _ ≤ c * |h| := ENNReal.toReal_le_of_le_ofReal (by positivity) hm

/-- **The primitive of `1_s` at a point of density zero.** If a null-measurable set `s` has
density zero at `x`, then `y ↦ ∫_a^y 1_s` has derivative `0` at `x`. -/
theorem hasDerivAt_integral_indicator_of_hasDensityAt_zero (hs : NullMeasurableSet s) (a : ℝ)
    (h : HasDensityAt volume s x 0) :
    HasDerivAt (fun y => ∫ t in a..y, s.indicator (1 : ℝ → ℝ) t) 0 x := by
  obtain ⟨t, -, ht, hts⟩ := hs.exists_measurable_superset_ae_eq
  simp_rw [intervalIntegral.integral_congr_ae_restrict
    (ae_restrict_of_ae (indicator_ae_eq_of_ae_eq_set (f := (1 : ℝ → ℝ)) hts.symm))]
  exact hasDerivAt_integral_indicator_of_hasDensityAt_zero_aux ht a (h.congr_ae hts.symm)

/-- **The primitive of `1_s` at a point of density one.** If a null-measurable set `s` has
density one at `x`, then `y ↦ ∫_a^y 1_s` has derivative `1` at `x`. -/
theorem hasDerivAt_integral_indicator_of_hasDensityAt_one (hs : NullMeasurableSet s) (a : ℝ)
    (h : HasDensityAt volume s x 1) :
    HasDerivAt (fun y => ∫ t in a..y, s.indicator (1 : ℝ → ℝ) t) 1 x := by
  have h0 : HasDensityAt volume sᶜ x 0 :=
    (hasDensityAt_compl_zero_iff hs
      (Metric.eventually_measure_closedBall_ne_zero_ne_top volume x)).2 h
  have hc := hasDerivAt_integral_indicator_of_hasDensityAt_zero hs.compl a h0
  -- `1_s = 1 - 1_{sᶜ}`, so the primitive of `1_s` is `y - a` minus that of `1_{sᶜ}`.
  have hfun : (fun y => ∫ t in a..y, s.indicator (1 : ℝ → ℝ) t) =
      fun y => (y - a) - ∫ t in a..y, sᶜ.indicator (1 : ℝ → ℝ) t := by
    funext y
    have hsum : ∀ t, s.indicator (1 : ℝ → ℝ) t = 1 - sᶜ.indicator 1 t := fun t => by
      by_cases ht : t ∈ s <;> simp [ht]
    simp_rw [hsum]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegrable_indicator_one hs.compl a y)]
    simp
  rw [hfun]
  have h2 : HasDerivAt (fun y => (y - a) - ∫ t in a..y, sᶜ.indicator (1 : ℝ → ℝ) t) (1 - 0) x :=
    ((hasDerivAt_id' x).sub_const a).sub hc
  rwa [sub_zero] at h2

/-- **A set without essential boundary points in an interval is null or conull there.** If no
point of `(a, b)` lies in the essential boundary of a null-measurable set `s ⊆ ℝ`, then
`s ∩ (a, b)` or `(a, b) \ s` is Lebesgue-null. -/
theorem measure_inter_Ioo_eq_zero_or_measure_Ioo_sdiff_eq_zero (hs : NullMeasurableSet s)
    {a b : ℝ} (h : ∀ y ∈ Ioo a b, y ∉ essentialBoundary volume s) :
    volume (s ∩ Ioo a b) = 0 ∨ volume (Ioo a b \ s) = 0 := by
  rcases le_or_gt b a with hba | hab
  · simp [Ioo_eq_empty_of_le hba]
  classical
  let F := fun y => ∫ t in a..y, s.indicator (1 : ℝ → ℝ) t
  let g := fun y => if HasDensityAt volume s y 1 then (1 : ℝ) else 0
  have hderiv : ∀ y ∈ Ioo a b, HasDerivAt F (g y) y := by
    intro y hy
    have hy' := h y hy
    simp only [mem_essentialBoundary, mem_essentialInterior, mem_essentialExterior, not_and,
      not_not] at hy'
    by_cases h1 : HasDensityAt volume s y 1
    · simpa [g, h1] using hasDerivAt_integral_indicator_of_hasDensityAt_one hs a h1
    · simpa [g, h1] using hasDerivAt_integral_indicator_of_hasDensityAt_zero hs a (hy' h1)
  have hcont : ContinuousOn F (Icc a b) :=
    (intervalIntegral.continuous_primitive (intervalIntegrable_indicator_one hs) a).continuousOn
  obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope F g hab hcont hderiv
  have hFb : F b = volume.real (s ∩ Ioc a b) :=
    intervalIntegral.integral_indicator_one hs hab.le
  have hFa : F a = 0 := intervalIntegral.integral_same
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  have hfin : volume (s ∩ Ioc a b) ≠ ∞ :=
    measure_ne_top_of_subset inter_subset_right (by simp)
  rw [hFb, hFa, sub_zero] at hc
  by_cases h1 : HasDensityAt volume s c 1
  · -- The slope is one, so `s` fills `(a, b]`.
    simp only [g, h1, ↓reduceIte] at hc
    have hreal : volume.real (s ∩ Ioc a b) = b - a := by
      field_simp at hc
      linarith
    have hsdiff : volume (Ioc a b \ s) = volume (Ioc a b) - volume (s ∩ Ioc a b) := by
      rw [← sdiff_inter_self_eq_sdiff,
        measure_sdiff inter_subset_right (hs.inter measurableSet_Ioc.nullMeasurableSet) hfin]
    right
    refine measure_mono_null (sdiff_subset_sdiff_left Ioo_subset_Ioc_self) ?_
    simp [hsdiff, Real.volume_Ioc, ← ofReal_measureReal hfin, hreal]
  · -- The slope is zero, so `s` misses `(a, b]` up to a null set.
    simp only [g, h1, ↓reduceIte] at hc
    have hreal : volume.real (s ∩ Ioc a b) = 0 := by
      rcases div_eq_zero_iff.1 hc.symm with h' | h'
      · exact h'
      · exact absurd h' hba
    left
    refine measure_mono_null (inter_subset_inter_right _ Ioo_subset_Ioc_self) ?_
    rwa [measureReal_eq_zero_iff hfin] at hreal

end TauCeti.Real
