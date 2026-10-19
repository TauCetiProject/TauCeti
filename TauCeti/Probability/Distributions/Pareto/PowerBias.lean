/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.PowerBias
public import TauCeti.Probability.Distributions.Pareto.Basic
import TauCeti.Probability.Distributions.Pareto.PDF

/-!
# Power biasing of Pareto laws

Power biasing a Pareto law by `x ^ q` subtracts `q` from its shape parameter throughout the
sharp moment domain `q < r`.
-/

public section

open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

/-- Power biasing a Pareto law subtracts the exponent from its shape parameter. -/
theorem powerBias_paretoMeasure {t r q : ℝ} (ht : 0 < t) (hr : 0 < r) (hq : q < r) :
    (paretoMeasure t r).powerBias q = paretoMeasure t (r - q) := by
  have hrq : 0 < r - q := sub_pos.mpr hq
  have hqint : Integrable (fun x : ℝ => x ^ q) (paretoMeasure t r) :=
    (integrable_rpow_paretoMeasure_iff ht hr q).2 hq
  have hZ : ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂paretoMeasure t r =
      ENNReal.ofReal (r * t ^ q / (r - q)) := by
    rw [Measure.lintegral_powerBiasWeight_eq_of_integrable
        ((ae_mem_Ici_paretoMeasure t r).mono fun x hx => (ht.trans_le hx).le) hqint,
      integral_rpow_paretoMeasure ht hr hq]
  have hw : Measurable fun x : ℝ => Real.toNNReal (x ^ q) :=
    Measure.measurable_powerBiasWeight q
  have hnorm : Measurable fun x : ℝ =>
      (ENNReal.ofReal (r * t ^ q / (r - q)))⁻¹ *
        (Real.toNNReal (x ^ q) : ℝ≥0∞) :=
    measurable_const.mul hw.coe_nnreal_ennreal
  rw [Measure.powerBias_def, Measure.weighted_eq_withDensity _ hw.aemeasurable,
    hZ, paretoMeasure, ← withDensity_mul volume (measurable_paretoPDF t r) hnorm,
    paretoMeasure]
  apply withDensity_congr_ae
  filter_upwards with x
  by_cases hx : t ≤ x
  · have hxpos : 0 < x := ht.trans_le hx
    rw [Pi.mul_apply, paretoPDF_of_le hx, paretoPDF_of_le hx,
      ENNReal.ofNNReal_toNNReal, ← ENNReal.ofReal_inv_of_pos]
    · have hratio : 0 < r * t ^ q / (r - q) := by positivity
      have hdensity : 0 < r * t ^ r * x ^ (-(r + 1)) := by positivity
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hratio.le),
        ← ENNReal.ofReal_mul hdensity.le]
      congr 1
      have htq : t ^ q ≠ 0 := (Real.rpow_pos_of_pos ht q).ne'
      have htr : t ^ r = t ^ (r - q) * t ^ q := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
      have hxr : x ^ (-(r + 1)) * x ^ q = x ^ (-(r - q + 1)) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
      rw [htr]
      field_simp [hr.ne', hrq.ne', htq]
      rw [hxr]
    · positivity
  · have hxt : x < t := not_le.mp hx
    rw [Pi.mul_apply, paretoPDF_of_lt hxt, zero_mul, paretoPDF_of_lt hxt]

end TauCeti.Probability
