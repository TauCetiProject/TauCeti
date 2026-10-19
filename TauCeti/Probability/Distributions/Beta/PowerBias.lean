/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.PowerBias
public import TauCeti.Probability.Distributions.Beta.Basic
import TauCeti.Probability.Distributions.Beta.PDF

/-!
# Power biasing of Beta laws

Power biasing a Beta law by `x ^ q` adds `q` to its first shape parameter. This is the
one-sided member of the more general mixed-power moment identity for the Beta family.
-/

public section

open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

/-- Power biasing a Beta law adds the exponent to its first shape parameter. -/
theorem powerBias_betaMeasure {a b q : ℝ} (ha : 0 < a) (hb : 0 < b) (hq : -a < q) :
    (betaMeasure a b).powerBias q = betaMeasure (a + q) b := by
  have haq : 0 < a + q := by linarith
  have hqint : Integrable (fun x : ℝ => x ^ q) (betaMeasure a b) := by
    simpa using (integrable_rpow_mul_one_sub_rpow_betaMeasure_iff ha hb
      (q := q) (s := 0)).2 ⟨haq, by simpa using hb⟩
  have hZ : ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂betaMeasure a b =
      ENNReal.ofReal (beta (a + q) b / beta a b) := by
    rw [Measure.lintegral_powerBiasWeight_eq_of_integrable
        ((ae_mem_Ioo_betaMeasure a b).mono fun x hx => hx.1.le) hqint]
    have hmom := integral_rpow_mul_one_sub_rpow_betaMeasure ha hb haq
      (by simpa using hb : 0 < b + 0) (q := q) (s := 0)
    simpa only [Real.rpow_zero, mul_one, add_zero] using congrArg ENNReal.ofReal hmom
  have hw : Measurable fun x : ℝ => Real.toNNReal (x ^ q) :=
    Measure.measurable_powerBiasWeight q
  have hnorm : Measurable fun x : ℝ =>
      (ENNReal.ofReal (beta (a + q) b / beta a b))⁻¹ *
        (Real.toNNReal (x ^ q) : ℝ≥0∞) :=
    measurable_const.mul hw.coe_nnreal_ennreal
  rw [Measure.powerBias_def, Measure.weighted_eq_withDensity _ hw.aemeasurable,
    hZ, betaMeasure, ← withDensity_mul volume (measurable_betaPDF a b) hnorm, betaMeasure]
  apply withDensity_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne 0, (volume : Measure ℝ).ae_ne 1]
    with x hx0 hx1
  rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
  · rw [Pi.mul_apply, betaPDF_eq_zero_of_nonpos hxneg.le, zero_mul,
      betaPDF_eq_zero_of_nonpos hxneg.le]
  rcases lt_or_gt_of_ne hx1 with hxlt | hxgt
  · rw [Pi.mul_apply, betaPDF_of_pos_lt_one hxpos hxlt,
      betaPDF_of_pos_lt_one hxpos hxlt, ENNReal.ofNNReal_toNNReal,
      ← ENNReal.ofReal_inv_of_pos]
    · have hratio : 0 < beta (a + q) b / beta a b :=
        div_pos (beta_pos haq hb) (beta_pos ha hb)
      have hdensity : 0 < 1 / beta a b * x ^ (a - 1) * (1 - x) ^ (b - 1) := by
        simpa [betaPDFReal, hxpos, hxlt] using betaPDFReal_pos hxpos hxlt ha hb
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hratio.le),
        ← ENNReal.ofReal_mul hdensity.le]
      congr 1
      have hexponent : a + q - 1 = q + (a - 1) := by ring
      rw [hexponent, Real.rpow_add hxpos]
      field_simp [ne_of_gt (beta_pos ha hb), ne_of_gt (beta_pos haq hb)]
    · exact div_pos (beta_pos haq hb) (beta_pos ha hb)
  · rw [Pi.mul_apply, betaPDF_eq_zero_of_one_le hxgt.le, zero_mul,
      betaPDF_eq_zero_of_one_le hxgt.le]

end TauCeti.Probability
