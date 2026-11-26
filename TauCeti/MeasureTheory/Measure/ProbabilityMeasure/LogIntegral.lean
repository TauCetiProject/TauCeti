/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Logarithmic integrals under weak convergence

For probability measures carried by the positive real axis, control of the logarithmic tails
at zero and infinity lets one pass from weak convergence to convergence of the mean logarithm.
The limit is also carried by the positive axis and has an integrable logarithm. A uniform second
moment bound suffices for the tail at infinity. This is the truncation step in the singular-value
approach to the circular law (T. Tao, *Topics in Random Matrix Theory*, §2.8.3).
-/

public section

namespace MeasureTheory.ProbabilityMeasure

open Filter Set Topology
open scoped BoundedContinuousFunction ENNReal NNReal

private noncomputable def clippedLog {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x ↦ Real.log (max a (min b x)))
    ((continuous_const.max (continuous_const.min continuous_id)).log
      (fun x ↦ (ha.trans_le (le_max_left a (min b x))).ne'))
    (max |Real.log a| |Real.log b|) (fun x ↦ by
      have hlo := Real.log_le_log ha (le_max_left a (min b x))
      have hhi := Real.log_le_log (ha.trans_le (le_max_left a (min b x)))
        (max_le hab (min_le_left b x))
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [le_max_left |Real.log a| |Real.log b|, neg_abs_le (Real.log a)]
      · linarith [le_max_right |Real.log a| |Real.log b|, le_abs_self (Real.log b)])

-- The infinite value at nonpositive inputs detects any mass accumulated at zero.
private noncomputable def logClippingError (a b x : ℝ) : ℝ≥0∞ :=
  if 0 < x then ENNReal.ofReal (max 0 (max (Real.log a - Real.log x) (Real.log x - Real.log b)))
  else ∞

private theorem lowerSemicontinuous_logClippingError (a b : ℝ) :
    LowerSemicontinuous (logClippingError a b) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro t
  by_cases ht : t = ∞
  · simp [ht]
  have hsuper : (logClippingError a b) ⁻¹' Ioi t =
      Iio (Real.exp (Real.log a - t.toReal)) ∪ Ioi (Real.exp (Real.log b + t.toReal)) := by
    ext x
    simp only [mem_preimage, mem_Ioi, mem_union, mem_Iio, logClippingError]
    by_cases hx : 0 < x
    · conv_lhs => rw [ite_eq_left hx, ← ENNReal.ofReal_toReal ht]
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg, lt_max_iff,
        or_iff_right (not_lt_of_ge ENNReal.toReal_nonneg), lt_max_iff,
        ← Real.log_lt_iff_lt_exp hx, ← Real.lt_log_iff_exp_lt hx]
      constructor <;> rintro (h | h)
      · left
        linarith
      · right
        linarith
      · left
        linarith
      · right
        linarith
    · rw [ite_eq_right hx]
      exact iff_of_true (lt_top_iff_ne_top.mpr ht)
        (Or.inl ((not_lt.mp hx).trans_lt (Real.exp_pos _)))
  rw [hsuper]
  exact isOpen_Iio.union isOpen_Ioi

private theorem logClippingError_eq {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b) (hx : 0 < x) :
    logClippingError a b x = ‖Real.log x - clippedLog ha hab x‖ₑ := by
  rw [logClippingError, ite_eq_left hx, ← ofReal_norm, Real.norm_eq_abs]
  simp only [clippedLog, BoundedContinuousFunction.coe_ofNormedAddCommGroup]
  by_cases hxa : x ≤ a
  · rw [max_eq_left ((min_le_right b x).trans hxa)]
    have hlo := Real.log_le_log hx hxa
    have hhi := Real.log_le_log hx (hxa.trans hab)
    rw [max_eq_left (by linarith : Real.log x - Real.log b ≤ Real.log a - Real.log x),
      max_eq_right (by linarith : 0 ≤ Real.log a - Real.log x), abs_of_nonpos (sub_nonpos.mpr hlo)]
    congr 1
    ring
  by_cases hbx : b ≤ x
  · rw [min_eq_left hbx, max_eq_right hab]
    have hlo := Real.log_le_log ha (lt_of_not_ge hxa).le
    have hhi := Real.log_le_log (ha.trans_le hab) hbx
    rw [max_eq_right (by linarith : Real.log a - Real.log x ≤ Real.log x - Real.log b),
      max_eq_right (sub_nonneg.mpr hhi), abs_of_nonneg (sub_nonneg.mpr hhi)]
  · rw [min_eq_right (lt_of_not_ge hbx).le, max_eq_right (lt_of_not_ge hxa).le]
    have hlo := Real.log_le_log ha (lt_of_not_ge hxa).le
    have hhi := Real.log_le_log hx (lt_of_not_ge hbx).le
    simp [max_eq_left (max_le (sub_nonpos.mpr hlo) (sub_nonpos.mpr hhi))]

private theorem lintegral_logClippingError_le (ν : ProbabilityMeasure ℝ)
    (hν : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) {a b : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) (hb : 1 ≤ b) :
    ∫⁻ x, logClippingError a b x ∂(ν : Measure ℝ) ≤
      (∫⁻ x in Ioo 0 a, ENNReal.ofReal (-Real.log x) ∂(ν : Measure ℝ)) +
      ∫⁻ x in Ioi b, ENNReal.ofReal (Real.log x) ∂(ν : Measure ℝ) := by
  have hm : Measurable (fun x : ℝ ↦ ENNReal.ofReal (-Real.log x)) := by fun_prop
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_add_left (hm.indicator measurableSet_Ioo)]
  apply lintegral_mono_ae
  filter_upwards [hν] with x hx
  rw [logClippingError, ite_eq_left hx]
  by_cases hxa : x < a
  · have hlo := Real.log_nonpos ha.le ha₁
    have hhi := Real.log_nonneg hb
    have hx₀ := Real.log_nonpos hx.le (hxa.le.trans ha₁)
    have hxNotMem : x ∉ Ioi b := not_lt.mpr (hxa.le.trans (ha₁.trans hb))
    simp only [indicator_of_mem (mem_Ioo.mpr ⟨hx, hxa⟩), indicator_of_notMem hxNotMem, add_zero]
    exact ENNReal.ofReal_le_ofReal (max_le (by linarith)
      (max_le (by linarith) (by linarith)))
  by_cases hbx : b < x
  · have hlo := Real.log_nonpos ha.le ha₁
    have hhi := Real.log_nonneg hb
    have hx₀ := Real.log_nonneg (hb.trans hbx.le)
    have hxNotMem : x ∉ Ioo 0 a := fun h ↦ hxa h.2
    simp only [indicator_of_notMem hxNotMem, indicator_of_mem (mem_Ioi.mpr hbx), zero_add]
    exact ENNReal.ofReal_le_ofReal (max_le hx₀ (max_le (by linarith) (by linarith)))
  · have hlo := Real.log_le_log ha (not_lt.mp hxa)
    have hhi := Real.log_le_log hx (not_lt.mp hbx)
    simp [max_eq_left (max_le (sub_nonpos.mpr hlo) (sub_nonpos.mpr hhi))]

private theorem log_integrable_and_clippedLog_bound (ν : ProbabilityMeasure ℝ)
    {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b) (hε : 0 ≤ ε)
    (h : ∫⁻ x, logClippingError a b x ∂(ν : Measure ℝ) ≤ ENNReal.ofReal ε) :
    (∀ᵐ x ∂(ν : Measure ℝ), 0 < x) ∧ Integrable Real.log (ν : Measure ℝ) ∧
      ‖(∫ x, Real.log x ∂(ν : Measure ℝ)) - ∫ x, clippedLog ha hab x ∂(ν : Measure ℝ)‖ ≤ ε := by
  have hfinite := h.trans_lt ENNReal.ofReal_lt_top
  have hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x := by
    filter_upwards [ae_lt_top (lowerSemicontinuous_logClippingError a b).measurable hfinite.ne]
      with x hx
    by_contra hn
    simp [logClippingError, hn] at hx
  have herr := lintegral_congr_ae (hpos.mono fun _ hx ↦ logClippingError_eq ha hab hx)
  have hclip := (clippedLog ha hab).integrable (ν : Measure ℝ)
  have hdiff : Integrable (fun x ↦ Real.log x - clippedLog ha hab x) (ν : Measure ℝ) :=
    ⟨Real.measurable_log.aestronglyMeasurable.sub hclip.1, by
      rw [hasFiniteIntegral_def, ← herr]
      exact hfinite⟩
  have hlog : Integrable Real.log (ν : Measure ℝ) := by
    exact (hdiff.add hclip).congr (Eventually.of_forall fun x ↦ sub_add_cancel _ _)
  refine ⟨hpos, hlog, ?_⟩
  rw [← integral_sub hlog hclip]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← ENNReal.ofReal_le_ofReal_iff hε, ofReal_integral_norm_eq_lintegral_eNorm hdiff, ← herr]
  exact h

/-- Weak convergence and vanishing logarithmic tails at zero and infinity give convergence of
the logarithmic integrals. The limit puts all its mass on the positive axis and has an integrable
logarithm. The tails are lower integrals, which take the value infinity for nonintegrable tails. -/
theorem tendsto_integral_log_of_log_tails {ι : Type*} {l : Filter ι} [l.NeBot]
    {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : Tendsto νs l (𝓝 ν))
    (hpos : ∀ᶠ i in l, ∀ᵐ x ∂(νs i : Measure ℝ), 0 < x)
    (hzero : ∀ ε : ℝ, 0 < ε → ∃ a > (0 : ℝ), ∀ᶠ i in l,
      ∫⁻ x in Ioo 0 a, ENNReal.ofReal (-Real.log x) ∂(νs i : Measure ℝ) ≤ ENNReal.ofReal ε)
    (hinfty : ∀ ε : ℝ, 0 < ε → ∃ b : ℝ, ∀ᶠ i in l,
      ∫⁻ x in Ioi b, ENNReal.ofReal (Real.log x) ∂(νs i : Measure ℝ) ≤ ENNReal.ofReal ε) :
    (∀ᵐ x ∂(ν : Measure ℝ), 0 < x) ∧ Integrable Real.log (ν : Measure ℝ) ∧
      Tendsto (fun i ↦ ∫ x, Real.log x ∂(νs i : Measure ℝ)) l
        (𝓝 (∫ x, Real.log x ∂(ν : Measure ℝ))) := by
  have happ (ε : ℝ) (hε : 0 < ε) : ∃ (a b : ℝ) (_ : 0 < a) (_ : a ≤ b),
      (∫⁻ x, logClippingError a b x ∂(ν : Measure ℝ)) ≤ ENNReal.ofReal ε ∧
      ∀ᶠ i in l, (∫⁻ x, logClippingError a b x ∂(νs i : Measure ℝ)) ≤ ENNReal.ofReal ε := by
    obtain ⟨a₀, ha₀, hz⟩ := hzero (ε / 2) (by positivity)
    obtain ⟨b₀, hi⟩ := hinfty (ε / 2) (by positivity)
    let a := min a₀ 1
    let b := max b₀ 1
    have ha : 0 < a := lt_min ha₀ one_pos
    have ha₁ : a ≤ 1 := min_le_right _ _
    have hb : 1 ≤ b := le_max_right _ _
    have hevent : ∀ᶠ i in l,
        (∫⁻ x, logClippingError a b x ∂(νs i : Measure ℝ)) ≤ ENNReal.ofReal ε := by
      filter_upwards [hz, hi, hpos] with i hzi hii hpi
      refine (lintegral_logClippingError_le (νs i) hpi ha ha₁ hb).trans ?_
      have hlo := lintegral_mono' (Measure.restrict_mono_set (νs i : Measure ℝ)
        (Ioo_subset_Ioo_right (b := (0 : ℝ)) (min_le_left a₀ 1)))
        (f := fun x ↦ ENNReal.ofReal (-Real.log x)) le_rfl
      have hhi := lintegral_mono' (Measure.restrict_mono_set (νs i : Measure ℝ)
        (Ioi_subset_Ioi (le_max_left b₀ 1))) (f := fun x ↦ ENNReal.ofReal (Real.log x)) le_rfl
      simpa [← ENNReal.ofReal_add (by positivity : 0 ≤ ε / 2) (by positivity : 0 ≤ ε / 2)] using
        add_le_add (hlo.trans hzi) (hhi.trans hii)
    exact ⟨a, b, ha, ha₁.trans hb,
      (TauCeti.le_liminf_lintegral_of_tendsto_probabilityMeasure
        (lowerSemicontinuous_logClippingError a b) hν).trans
        (liminf_le_of_frequently_le' hevent.frequently), hevent⟩
  obtain ⟨a, b, ha, hab, hlim, -⟩ := happ 1 one_pos
  obtain ⟨hp, hl, -⟩ := log_integrable_and_clippedLog_bound ν ha hab zero_le_one hlim
  refine ⟨hp, hl, Metric.tendsto_nhds.mpr fun ε hε ↦ ?_⟩
  obtain ⟨c, d, hc, hcd, hlim', hevent⟩ := happ (ε / 4) (by positivity)
  have hνerr := (log_integrable_and_clippedLog_bound ν hc hcd (by positivity) hlim').2.2
  have hweak := tendsto_iff_forall_integral_tendsto.mp hν (clippedLog hc hcd)
  filter_upwards [hevent, Metric.tendsto_nhds.mp hweak (ε / 4) (by positivity)] with i hi hw
  have hιerr := (log_integrable_and_clippedLog_bound (νs i) hc hcd (by positivity) hi).2.2
  rw [dist_eq_norm] at hw ⊢
  calc
    _ ≤ ‖_ - _‖ + ‖_ - _‖ := norm_sub_le_norm_sub_add_norm_sub _
      (∫ x, clippedLog hc hcd x ∂(νs i : Measure ℝ)) _
    _ ≤ ε / 4 + (ε / 4 + ε / 4) := by
      refine add_le_add hιerr ((norm_sub_le_norm_sub_add_norm_sub _
        (∫ x, clippedLog hc hcd x ∂(ν : Measure ℝ)) _).trans ?_)
      exact add_le_add hw.le ((norm_sub_rev _ _).le.trans hνerr)
    _ < ε := by linarith

/-- The positive logarithmic tail is bounded by the second moment divided by the cutoff.
This estimate applies to arbitrary measures, including empirical singular-value measures. -/
theorem _root_.MeasureTheory.Measure.setLIntegral_log_le_inv_mul_lintegral_sq
    (μ : Measure ℝ) {b : ℝ} (hb : 0 < b) :
    (∫⁻ x in Ioi b, ENNReal.ofReal (Real.log x) ∂μ) ≤
      ENNReal.ofReal b⁻¹ * ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μ := by
  rw [← lintegral_indicator measurableSet_Ioi,
    ← lintegral_const_mul _ (by fun_prop : Measurable fun x : ℝ ↦ ENNReal.ofReal (x ^ 2))]
  apply lintegral_mono
  intro x
  by_cases hx : b < x
  · simp only [indicator_of_mem (mem_Ioi.mpr hx)]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hb.le)]
    apply ENNReal.ofReal_le_ofReal
    have hx₀ := hb.trans hx
    exact (Real.log_le_self hx₀.le).trans (by
      rw [inv_mul_eq_div, le_div_iff₀ hb]
      nlinarith [mul_nonneg hx₀.le (sub_nonneg.mpr hx.le)])
  · have hxNotMem : x ∉ Ioi b := hx
    rw [indicator_of_notMem hxNotMem]
    exact zero_le

/-- Weak convergence of positive laws with an eventually bounded second moment and vanishing
logarithmic tail at zero gives convergence of the logarithmic integrals. -/
theorem tendsto_integral_log_of_log_tail_zero {ι : Type*} {l : Filter ι} [l.NeBot]
    {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ} {C : ℝ≥0}
    (hν : Tendsto νs l (𝓝 ν))
    (hpos : ∀ᶠ i in l, ∀ᵐ x ∂(νs i : Measure ℝ), 0 < x)
    (hsq : ∀ᶠ i in l, ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(νs i : Measure ℝ) ≤ (C : ℝ≥0∞))
    (hzero : ∀ ε : ℝ, 0 < ε → ∃ a > (0 : ℝ), ∀ᶠ i in l,
      ∫⁻ x in Ioo 0 a, ENNReal.ofReal (-Real.log x) ∂(νs i : Measure ℝ) ≤ ENNReal.ofReal ε) :
    (∀ᵐ x ∂(ν : Measure ℝ), 0 < x) ∧ Integrable Real.log (ν : Measure ℝ) ∧
      Tendsto (fun i ↦ ∫ x, Real.log x ∂(νs i : Measure ℝ)) l
        (𝓝 (∫ x, Real.log x ∂(ν : Measure ℝ))) := by
  apply tendsto_integral_log_of_log_tails hν hpos hzero
  intro ε hε
  let b := max 1 ((C : ℝ) / ε)
  have hb : 0 < b := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨b, ?_⟩
  filter_upwards [hsq] with i hi
  calc
    _ ≤ ENNReal.ofReal b⁻¹ * (C : ℝ≥0∞) := by
      refine ((νs i : Measure ℝ).setLIntegral_log_le_inv_mul_lintegral_sq hb).trans ?_
      gcongr
    _ ≤ ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (inv_nonneg.mpr hb.le)]
      apply ENNReal.ofReal_le_ofReal
      rw [inv_mul_eq_div, div_le_iff₀ hb, mul_comm, ← div_le_iff₀ hε]
      exact le_max_right _ _

end MeasureTheory.ProbabilityMeasure
