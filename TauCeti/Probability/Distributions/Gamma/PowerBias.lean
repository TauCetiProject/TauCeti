/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.PowerBias
public import TauCeti.Probability.Distributions.Gamma.Basic
import TauCeti.Probability.Distributions.Gamma.PDF

/-!
# Power biasing of Gamma laws

Power biasing a Gamma law of shape `a` by exponent `q` changes its shape to `a + q` when
`q > -a`. At or below this sharp threshold, the normalizing power moment is infinite, so the
totalized power bias is the zero measure.
-/

public section

open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

/-- Power biasing a Gamma law adds the bias exponent to its shape parameter. -/
theorem powerBias_gammaMeasure {a r q : ℝ} (ha : 0 < a) (hr : 0 < r) (hq : -a < q) :
    (gammaMeasure a r).powerBias q = gammaMeasure (a + q) r := by
  have haq : 0 < a + q := by linarith
  have hqint : Integrable (fun x : ℝ => x ^ q) (gammaMeasure a r) :=
    (integrable_rpow_gammaMeasure_iff ha hr q).2 hq
  have hZ : ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂gammaMeasure a r =
      ENNReal.ofReal (r ^ (-q) * Real.Gamma (a + q) / Real.Gamma a) := by
    rw [Measure.lintegral_powerBiasWeight_eq_of_integrable
        ((ae_pos_gammaMeasure a r).mono fun x hx => hx.le) hqint,
      integral_rpow_gammaMeasure ha hr hq]
  have hw : Measurable fun x : ℝ => Real.toNNReal (x ^ q) :=
    Measure.measurable_powerBiasWeight q
  have hnorm : Measurable fun x : ℝ =>
      (ENNReal.ofReal (r ^ (-q) * Real.Gamma (a + q) / Real.Gamma a))⁻¹ *
        (Real.toNNReal (x ^ q) : ℝ≥0∞) :=
    measurable_const.mul hw.coe_nnreal_ennreal
  rw [Measure.powerBias_def, Measure.weighted_eq_withDensity _ hw.aemeasurable,
    hZ, gammaMeasure, ← withDensity_mul volume (measurable_gammaPDF a r) hnorm, gammaMeasure]
  apply withDensity_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rw [Pi.mul_apply, gammaPDF_of_neg hxneg, zero_mul, gammaPDF_of_neg hxneg]
  · rw [Pi.mul_apply, gammaPDF_of_nonneg hxpos.le, gammaPDF_of_nonneg hxpos.le,
      ENNReal.ofNNReal_toNNReal, ← ENNReal.ofReal_inv_of_pos]
    · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have h_exp : a + q - 1 = (a - 1) + q := by ring
      rw [h_exp, Real.rpow_add hxpos, Real.rpow_add hr, Real.rpow_neg hr.le]
      field_simp [Real.Gamma_ne_zero, (Real.rpow_pos_of_pos hr a).ne',
        (Real.rpow_pos_of_pos hr q).ne', (Real.rpow_pos_of_pos hxpos (a - 1)).ne',
        (Real.rpow_pos_of_pos hxpos q).ne']
    · positivity

/-- At or below the sharp Gamma moment threshold, power biasing gives the zero measure because its
normalizing moment is infinite. -/
theorem powerBias_gammaMeasure_of_le {a r q : ℝ} (ha : 0 < a) (hr : 0 < r) (hq : q ≤ -a) :
    (gammaMeasure a r).powerBias q = 0 := by
  have hμ : ∀ᵐ x ∂gammaMeasure a r, 0 < x := ae_pos_gammaMeasure a r
  have hnonneg : 0 ≤ᵐ[gammaMeasure a r] fun x : ℝ => x ^ q :=
    hμ.mono fun x hx => Real.rpow_nonneg hx.le q
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ q) (gammaMeasure a r) := by
    refine (Measure.measurable_powerBiasWeight q).coe_nnreal_real.aestronglyMeasurable.congr ?_
    filter_upwards [hμ] with x hx
    exact Real.coe_toNNReal _ (Real.rpow_nonneg hx.le q)
  have hnot : ¬Integrable (fun x : ℝ => x ^ q) (gammaMeasure a r) := by
    rw [integrable_rpow_gammaMeasure_iff ha hr q]
    linarith
  have hnotFinite : ¬HasFiniteIntegral (fun x : ℝ => x ^ q) (gammaMeasure a r) :=
    fun hfinite => hnot ⟨hmeas, hfinite⟩
  have htop : ∫⁻ x, ENNReal.ofReal (x ^ q) ∂gammaMeasure a r = ∞ := by
    apply top_unique
    rw [← not_lt, ← hasFiniteIntegral_iff_ofReal hnonneg]
    exact hnotFinite
  have hZ : ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂gammaMeasure a r = ∞ := by
    simpa only [ENNReal.ofNNReal_toNNReal] using htop
  rw [Measure.powerBias_def, Measure.weighted_eq_zero_of_lintegral_eq_top hZ]

/-- A power-biased Gamma law is a probability measure exactly above the sharp moment threshold. -/
theorem isProbabilityMeasure_powerBias_gammaMeasure_iff {a r q : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure ((gammaMeasure a r).powerBias q) ↔ -a < q := by
  constructor
  · intro hprob
    by_contra hq
    have hzero := powerBias_gammaMeasure_of_le ha hr (not_lt.mp hq)
    have hmass := hprob.measure_univ
    rw [hzero] at hmass
    simp at hmass
  · intro hq
    rw [powerBias_gammaMeasure ha hr hq]
    exact isProbabilityMeasure_gammaMeasure (by linarith) hr

end TauCeti.Probability
