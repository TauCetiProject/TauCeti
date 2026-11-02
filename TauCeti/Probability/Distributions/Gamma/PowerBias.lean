/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.PowerBias
public import TauCeti.Probability.Distributions.Gamma.Basic
public import TauCeti.MeasureTheory.Measure.Typeclasses.Probability

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
  have := isProbabilityMeasure_gammaMeasure haq hr
  rw [gammaMeasure_eq_withDensity_ofReal (a + q)] at this ⊢
  rw [gammaMeasure_eq_withDensity_ofReal]
  have hc : 0 < Real.Gamma (a + q) / (Real.Gamma a * r ^ q) :=
    div_pos (Real.Gamma_pos_of_pos haq) (mul_pos (Real.Gamma_pos_of_pos ha) (rpow_pos_of_pos hr q))
  refine Measure.powerBias_withDensity_ofReal (measurable_gammaPDFReal a r).aemeasurable
    (ae_of_all _ (gammaPDFReal_nonneg ha hr)) hc ?_
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · simp [gammaPDFReal, not_le.2 hxneg]
  · have hexp : a + q - 1 = (a - 1) + q := by ring
    rw [gammaPDFReal_of_nonneg hxpos.le, gammaPDFReal_of_nonneg hxpos.le, hexp, rpow_add hxpos,
      rpow_add hr]
    have := (Real.Gamma_pos_of_pos ha).ne'
    have := (Real.Gamma_pos_of_pos haq).ne'
    have := (rpow_pos_of_pos hr q).ne'
    field_simp

/-- At or below the sharp Gamma moment threshold, power biasing gives the zero measure because its
normalizing moment is infinite. -/
theorem powerBias_gammaMeasure_of_le {a r q : ℝ} (ha : 0 < a) (hr : 0 < r) (hq : q ≤ -a) :
    (gammaMeasure a r).powerBias q = 0 :=
  Measure.powerBias_eq_zero_of_not_integrable
    ((ae_pos_gammaMeasure a r).mono fun _ hx => hx.le)
    (by rw [integrable_rpow_gammaMeasure_iff ha hr q]; linarith)

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
