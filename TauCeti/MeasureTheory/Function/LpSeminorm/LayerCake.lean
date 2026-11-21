/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral

/-!
# An integral bound by superlevel-set norms

Integral Minkowski applied to the layer-cake representation bounds the `Lᵖ` seminorm of a
function by the integral of the `Lᵖ` seminorms of its superlevel indicators. This form is
useful when geometric inequalities control the measures of superlevel sets. Both sides
are extended nonnegative numbers, so no integrability or finite-norm hypothesis is needed.
The integral comparison is `TauCeti.lintegral_Lp_lintegral_le`. For `1 < p < ∞` and finite
`Lᵖ` seminorm, equality holds exactly when the norm of the function is constant on its
nonzero set, up to a null set (`TauCeti.eLpNorm_eq_lintegral_measure_norm_gt_iff`).
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {α F : Type*} [NormedAddCommGroup F] {f : α → F}

private def normLevelIndicator (f : α → F) (x : α) (t : ℝ) : ℝ≥0∞ :=
  (Iio ‖f x‖).indicator 1 t

private theorem lintegral_normLevelIndicator (x : α) :
    ∫⁻ t in Ioi (0 : ℝ), normLevelIndicator f x t = ‖f x‖ₑ := by
  rw [← ofReal_norm]
  simp [normLevelIndicator, lintegral_indicator, Measure.restrict_apply, Iio_inter_Ioi]

private theorem normLevelIndicator_rpow (x : α) (t : ℝ) {q : ℝ} (hq : 0 < q) :
    normLevelIndicator f x t ^ q = {z | t < ‖f z‖}.indicator 1 x := by
  by_cases hx : t < ‖f x‖ <;> simp [normLevelIndicator, hx, ENNReal.zero_rpow_of_pos hq]

variable [MeasurableSpace α] {μ : Measure α}

private theorem aemeasurable_uncurry_normLevelIndicator
    (hf : AEMeasurable (fun x ↦ ‖f x‖) μ) :
    AEMeasurable (Function.uncurry (normLevelIndicator f))
      (μ.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hset : NullMeasurableSet {z : α × ℝ | z.2 < ‖f z.1‖}
      (μ.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    nullMeasurableSet_lt measurable_snd.aemeasurable hf.comp_fst
  convert (aemeasurable_const (b := (1 : ℝ≥0∞))).indicator₀ hset using 1
  ext ⟨x, t⟩
  by_cases ht : t < ‖f x‖ <;> simp [Function.uncurry, normLevelIndicator, ht]

private theorem lintegral_normLevelIndicator_rpow (hf : AEMeasurable (fun x ↦ ‖f x‖) μ)
    (t : ℝ) {q : ℝ} (hq : 0 < q) :
    ∫⁻ x, normLevelIndicator f x t ^ q ∂μ = μ {x | t < ‖f x‖} := by
  simp_rw [normLevelIndicator_rpow _ _ hq]
  rw [lintegral_indicator₀ (nullMeasurableSet_lt aemeasurable_const hf)]
  exact setLIntegral_one _

/-- The `Lᵖ` seminorm is bounded by the integral of the `p`th roots of the measures of
norm-superlevel sets. This is integral Minkowski for the layer-cake representation,
valid also when either side is infinite. -/
theorem eLpNorm_le_lintegral_measure_norm_gt [SFinite μ] (hf : AEStronglyMeasurable f μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    eLpNorm f p μ ≤ ∫⁻ t in Ioi (0 : ℝ), μ {x | t < ‖f x‖} ^ (1 / p.toReal) := by
  have hp0 := (zero_lt_one.trans_le hp).ne'
  have h := lintegral_Lp_lintegral_le (aemeasurable_uncurry_normLevelIndicator hf.norm.aemeasurable)
    (by simpa using ENNReal.toReal_mono hp_top hp)
  have hpos := ENNReal.toReal_pos hp0 hp_top
  simpa only [lintegral_normLevelIndicator, ← eLpNorm'_eq_lintegral_eNorm,
    ← eLpNorm_eq_eLpNorm' hp0 hp_top hf,
    lintegral_normLevelIndicator_rpow hf.norm.aemeasurable _ hpos] using h

-- A nonzero proportional superlevel slice determines both the essential support and the height.
private theorem ae_eq_indicator_of_normLevelIndicator_rpow_eq {q : ℝ} (hq : 0 < q) {t : ℝ}
    {b : ℝ≥0∞} (hb₀ : b ≠ 0)
    (h : ∀ᵐ x ∂μ, normLevelIndicator f x t ^ q = b * ‖f x‖ₑ ^ q) :
    (fun x ↦ ‖f x‖) =ᵐ[μ] {x | t < ‖f x‖}.indicator
      (fun _ ↦ ((b⁻¹) ^ (1 / q)).toReal) := by
  filter_upwards [h] with x hx
  by_cases hb : b = ∞
  · have hz : ‖f x‖ₑ ^ q = 0 := by
      by_contra hne
      rw [hb, ENNReal.top_mul hne, normLevelIndicator_rpow x t hq] at hx
      by_cases hxt : x ∈ {z | t < ‖f z‖} <;> simp [hxt] at hx
    rw [hb, ENNReal.inv_top, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hq)]
    simp [eNorm_eq_zero.mp ((ENNReal.rpow_eq_zero_iff_of_pos hq).mp hz)]
  have hpow : ‖f x‖ₑ ^ q = b⁻¹ * {z | t < ‖f z‖}.indicator 1 x := by
    rw [← normLevelIndicator_rpow x t hq, hx, ENNReal.inv_mul_cancel_left hb₀ hb]
  by_cases hxt : t < ‖f x‖
  · simp only [mem_ofPred_eq, hxt, indicator_of_mem, Pi.one_apply, mul_one] at hpow
    rw [indicator_of_mem hxt]
    have he := congrArg (· ^ (1 / q)) hpow
    simpa only [one_div, ENNReal.rpow_rpow_inv hq.ne', ← ofReal_norm,
      ENNReal.toReal_ofReal (norm_nonneg _)] using congrArg ENNReal.toReal he
  · rw [indicator_of_notMem hxt, mul_zero, ENNReal.rpow_eq_zero_iff_of_pos hq] at hpow
    rw [indicator_of_notMem hxt]
    simp [eNorm_eq_zero.mp hpow]

private theorem exists_ae_eq_indicator_of_eq_layerCake [SFinite μ] {p : ℝ≥0∞}
    (hp : 1 < p.toReal) (hfin : eLpNorm f p μ ≠ ∞)
    (heq : eLpNorm f p μ = ∫⁻ t in Ioi (0 : ℝ), μ {x | t < ‖f x‖} ^ (1 / p.toReal)) :
    ∃ (s : Set α) (c : ℝ), NullMeasurableSet s μ ∧ 0 ≤ c ∧
      (fun x ↦ ‖f x‖) =ᵐ[μ] s.indicator (fun _ ↦ c) := by
  have hf := aestronglyMeasurable_of_eLpNorm_ne_top hfin
  have hq := zero_lt_one.trans hp
  obtain ⟨hp0, hpt⟩ := ENNReal.toReal_pos_iff.mp hq
  set N := ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ
  have hn : N ^ (1 / p.toReal) = eLpNorm f p μ := by
    rw [eLpNorm_eq_eLpNorm' hp0.ne' hpt.ne hf, eLpNorm'_eq_lintegral_eNorm]
  have hN : N ≠ ∞ := by
    intro h
    exact hfin (by simpa only [h, ENNReal.top_rpow_of_pos (one_div_pos.mpr hq)] using hn.symm)
  by_cases hN0 : N = 0
  · have hz : eLpNorm f p μ = 0 := by
      rw [← hn, hN0, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hq)]
    refine ⟨∅, 0, MeasurableSet.empty.nullMeasurableSet, le_rfl, ?_⟩
    filter_upwards [(eLpNorm_eq_zero_iff hp0.ne').mp hz] with x hx
    simp [hx]
  have hslices := lintegral_Lp_lintegral_eq_iff
    (aemeasurable_uncurry_normLevelIndicator hf.norm.aemeasurable) hp
  simp only [lintegral_normLevelIndicator,
    lintegral_normLevelIndicator_rpow hf.norm.aemeasurable _ hq] at hslices
  have hae := (hslices (heq ▸ hfin)).mp (hn.trans heq)
  have hR0 : (∫⁻ t in Ioi (0 : ℝ), μ {x | t < ‖f x‖} ^ (1 / p.toReal)) ≠ 0 := by
    rw [← heq, ← hn]
    exact (ENNReal.rpow_eq_zero_iff_of_pos (one_div_pos.mpr hq)).not.mpr hN0
  have hne : ∃ᵐ t : ℝ ∂volume.restrict (Ioi 0), μ {x | t < ‖f x‖} ≠ 0 := by
    rw [Filter.Frequently]
    exact fun h ↦ hR0 (lintegral_congr_ae (h.mono fun t ht ↦ by
      simp only [not_ne_iff.mp ht, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hq), Pi.zero_apply])
      |>.trans lintegral_zero_fun)
  obtain ⟨t, ht₀, hslice⟩ := (hne.and_eventually hae).exists
  refine ⟨_, _, nullMeasurableSet_lt aemeasurable_const hf.norm.aemeasurable,
    ENNReal.toReal_nonneg, ae_eq_indicator_of_normLevelIndicator_rpow_eq hq
      (mul_ne_zero ht₀ (ENNReal.inv_ne_zero.mpr hN)) hslice⟩

private theorem eq_layerCake_of_ae_norm_eq_indicator {s : Set α} {c : ℝ} {p : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (hp : 0 < p.toReal) (hs : NullMeasurableSet s μ) (hc : 0 ≤ c)
    (h : (fun x ↦ ‖f x‖) =ᵐ[μ] s.indicator (fun _ ↦ c)) :
    eLpNorm f p μ = ∫⁻ t in Ioi (0 : ℝ), μ {x | t < ‖f x‖} ^ (1 / p.toReal) := by
  obtain ⟨hp0, hpt⟩ := ENNReal.toReal_pos_iff.mp hp
  rw [← eLpNorm_norm f hf, eLpNorm_congr_ae h, eLpNorm_indicator_const hs hp0.ne' hpt.ne]
  have hlevel : ∀ t ∈ Ioi (0 : ℝ), μ {x | t < ‖f x‖} ^ (1 / p.toReal) =
      (Iio c).indicator (fun _ ↦ μ s ^ (1 / p.toReal)) t := by
    intro t ht
    have hm : μ {x | t < ‖f x‖} = μ {x | t < s.indicator (fun _ ↦ c) x} :=
      measure_congr (h.mono fun x hx ↦ by simp only [mem_ofPred_eq, hx])
    rw [hm]
    by_cases htc : t < c
    · have he : {x | t < s.indicator (fun _ ↦ c) x} = s := by
        ext x
        by_cases hx : x ∈ s <;> simp [hx, htc, not_lt_of_ge (mem_Ioi.mp ht).le]
      simp [he, htc]
    · have he : {x | t < s.indicator (fun _ ↦ c) x} = ∅ := by
        ext x
        by_cases hx : x ∈ s <;> simp [hx, htc, not_lt_of_ge (mem_Ioi.mp ht).le]
      simp [he, htc, hp]
  rw [setLIntegral_congr_fun measurableSet_Ioi hlevel]
  simp [lintegral_indicator, Measure.restrict_apply, Iio_inter_Ioi, ← ofReal_norm, abs_of_nonneg hc,
    mul_comm]

/-- At finite `Lᵖ` seminorm and `1 < p < ∞`, the layer-cake norm bound is an equality
exactly when the pointwise norm agrees a.e. with a constant times a set indicator. -/
theorem eLpNorm_eq_lintegral_measure_norm_gt_iff [SFinite μ] {p : ℝ≥0∞}
    (hp : 1 < p.toReal) (hfin : eLpNorm f p μ ≠ ∞) :
    (eLpNorm f p μ = ∫⁻ t in Ioi (0 : ℝ), μ {x | t < ‖f x‖} ^ (1 / p.toReal)) ↔
      ∃ (s : Set α) (c : ℝ), NullMeasurableSet s μ ∧ 0 ≤ c ∧
        (fun x ↦ ‖f x‖) =ᵐ[μ] s.indicator (fun _ ↦ c) := by
  refine ⟨exists_ae_eq_indicator_of_eq_layerCake hp hfin, ?_⟩
  rintro ⟨s, c, hs, hc, h⟩
  exact eq_layerCake_of_ae_norm_eq_indicator (aestronglyMeasurable_of_eLpNorm_ne_top hfin)
    (zero_lt_one.trans hp) hs hc h

end TauCeti
