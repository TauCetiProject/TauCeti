/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.Weighted
public import TauCeti.Probability.Distributions.Gamma.Basic
import TauCeti.Probability.Distributions.Gamma.PDF

/-!
# Power-biased probability laws

Power biasing reweights a positive real-valued law by a real power of its coordinate.  The
normalization is inherited from `Measure.weighted`, so a zero or infinite power moment gives the
zero measure.  This file establishes the basic normalization and composition API and identifies
the power-biased Gamma law: biasing shape `a` by exponent `q` changes the shape to `a + q`.

This construction is useful for transporting moment formulas between members of a positive
distribution family.  In particular, its composition law turns successive biases into addition
of their exponents.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, Chapter 17.
-/

public section

open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory Real Set

namespace MeasureTheory.Measure

/-- The power bias of a real measure by exponent `q` is its normalized weighting by `x ^ q`.

The construction is the zero measure when the normalizing power moment is zero or infinite. -/
noncomputable def powerBias (μ : Measure ℝ) (q : ℝ) : Measure ℝ :=
  μ.weighted fun x => Real.toNNReal (x ^ q)

/-- The definition of a power-biased measure as a normalized weighted measure. -/
theorem powerBias_def (μ : Measure ℝ) (q : ℝ) :
    μ.powerBias q = μ.weighted fun x => Real.toNNReal (x ^ q) :=
  (rfl)

/-- The nonnegative weight defining power bias is measurable for every exponent. -/
theorem measurable_powerBiasWeight (q : ℝ) :
    Measurable fun x : ℝ => Real.toNNReal (x ^ q) := by
  apply Measurable.real_toNNReal
  apply measurable_of_continuousOn_compl_singleton 0
  intro x hx
  exact (Real.continuousAt_rpow_const x q (.inl hx)).continuousWithinAt

/-- Biasing by exponent zero leaves a probability measure unchanged. -/
@[simp]
theorem powerBias_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] : μ.powerBias 0 = μ := by
  rw [powerBias_def]
  rw [show (fun x : ℝ => Real.toNNReal (x ^ (0 : ℝ))) = 1 by funext x; simp]
  exact Measure.weighted_one μ

/-- The normalizing constant of power bias is the extended-real form of the corresponding power
moment whenever that moment is integrable. -/
theorem lintegral_powerBiasWeight_eq_of_integrable {μ : Measure ℝ} {q : ℝ}
    (hμ : 0 ≤ᵐ[μ] id) (hq : Integrable (fun x : ℝ => x ^ q) μ) :
    ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂μ =
      ENNReal.ofReal (∫ x, x ^ q ∂μ) := by
  change ∫⁻ x, ENNReal.ofReal (x ^ q) ∂μ = _
  rw [← ofReal_integral_eq_lintegral_ofReal hq
    (hμ.mono fun x hx => Real.rpow_nonneg hx q)]

/-- A positive finite power moment makes the corresponding power bias a probability measure. -/
theorem isProbabilityMeasure_powerBias {μ : Measure ℝ} {q : ℝ}
    (hpos : 0 < ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂μ)
    (hfin : ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂μ ≠ ∞) :
    IsProbabilityMeasure (μ.powerBias q) := by
  rw [powerBias_def]
  exact Measure.isProbabilityMeasure_weighted hpos hfin

/-- Under a valid first bias, a further real power is integrable exactly when the power with the
sum of the two exponents was integrable under the original law. -/
theorem integrable_rpow_powerBias_iff {μ : Measure ℝ} {q r : ℝ}
    (hμ : ∀ᵐ x ∂μ, 0 < x)
    (hpos : 0 < ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂μ)
    (hfin : ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂μ ≠ ∞) :
    Integrable (fun x : ℝ => x ^ r) (μ.powerBias q) ↔
      Integrable (fun x : ℝ => x ^ (q + r)) μ := by
  rw [powerBias_def, Measure.integrable_weighted_iff
    (measurable_powerBiasWeight q).aemeasurable hpos hfin]
  apply integrable_congr
  filter_upwards [hμ] with x hx
  rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.rpow_nonneg hx.le q),
    Real.rpow_add hx, smul_eq_mul]

/-- The totalized power integral under a valid power bias is the ratio of two power integrals of
the original law. The preceding integrability criterion identifies when this is an expectation. -/
theorem integral_rpow_powerBias {μ : Measure ℝ} {q r : ℝ}
    (hμ : ∀ᵐ x ∂μ, 0 < x)
    (hq : Integrable (fun x : ℝ => x ^ q) μ)
    (hpos : 0 < ∫ x, x ^ q ∂μ) :
    ∫ x, x ^ r ∂μ.powerBias q =
      (∫ x, x ^ (q + r) ∂μ) / ∫ x, x ^ q ∂μ := by
  rw [powerBias_def, Measure.integral_weighted (measurable_powerBiasWeight q).aemeasurable,
    lintegral_powerBiasWeight_eq_of_integrable (hμ.mono fun x hx => hx.le) hq,
    ENNReal.toReal_ofReal hpos.le, smul_eq_mul]
  rw [inv_mul_eq_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [hμ] with x hx
  rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.rpow_nonneg hx.le q),
    Real.rpow_add hx, smul_eq_mul]

/-- After a valid first bias, applying another power bias adds the two exponents. -/
theorem powerBias_powerBias {μ : Measure ℝ} {q r : ℝ}
    (hμ : ∀ᵐ x ∂μ, 0 < x)
    (hpos : 0 < ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂μ)
    (hfin : ∫⁻ x, (Real.toNNReal (x ^ q) : ℝ≥0∞) ∂μ ≠ ∞) :
    (μ.powerBias q).powerBias r = μ.powerBias (q + r) := by
  simp only [powerBias_def]
  rw [Measure.weighted_weighted (measurable_powerBiasWeight q).aemeasurable hpos hfin]
  apply Measure.weighted_congr
  filter_upwards [hμ] with x hx
  apply NNReal.eq
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (Real.rpow_nonneg hx.le q),
    Real.coe_toNNReal _ (Real.rpow_nonneg hx.le r),
    Real.coe_toNNReal _ (Real.rpow_nonneg hx.le (q + r)), Real.rpow_add hx]

end MeasureTheory.Measure

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
      rw [show a + q - 1 = (a - 1) + q by ring, Real.rpow_add hxpos,
        Real.rpow_add hr, Real.rpow_neg hr.le]
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
    change ∫⁻ x, ENNReal.ofReal (x ^ q) ∂gammaMeasure a r = ∞
    exact htop
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
