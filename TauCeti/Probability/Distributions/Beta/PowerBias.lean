/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.PowerBias
public import TauCeti.Probability.Distributions.Beta.Basic

/-!
# Power-biased beta laws

The beta family is closed under power biasing (`MeasureTheory.Measure.powerBias`): multiplying the
density by `x ^ q` only shifts the first shape parameter, by `q`, and changes the normalizing
constant.

* `TauCeti.Probability.powerBias_betaMeasure` — `Beta(a, b)^⟨q⟩ = Beta(a + q, b)` for `q > -a`.
* `TauCeti.Probability.powerBias_betaMeasure_of_le` — for `q ≤ -a` the power bias is zero.
* `TauCeti.Probability.isProbabilityMeasure_powerBias_betaMeasure_iff` — the power bias is a
  probability measure exactly when `q > -a`.

The range of `q` is exactly the range on which `x ^ q` is integrable, so on it the power-biased law
is a probability measure. The identity is an instance of
`MeasureTheory.Measure.powerBias_withDensity_ofReal`: on the support of the law, the density times
`x ^ q` is a positive constant times the density with the shifted shape.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley, 1995, ch. 25.
-/

public section

open MeasureTheory ProbabilityTheory Real

namespace TauCeti.Probability

/-- Biasing the beta law of shapes `a` and `b` by `x ^ q` shifts the first shape to `a + q`. -/
theorem powerBias_betaMeasure {a b q : ℝ} (ha : 0 < a) (hb : 0 < b) (hq : -a < q) :
    (betaMeasure a b).powerBias q = betaMeasure (a + q) b := by
  have haq : 0 < a + q := by linarith
  have := isProbabilityMeasureBeta haq hb
  rw [betaMeasure_eq_withDensity_ofReal (a + q)] at this ⊢
  rw [betaMeasure_eq_withDensity_ofReal]
  refine Measure.powerBias_withDensity_ofReal (measurable_betaPDFReal a b).aemeasurable
    (ae_of_all _ (betaPDFReal_nonneg ha hb))
    (div_pos (beta_pos haq hb) (beta_pos ha hb)) (ae_of_all _ fun x => ?_)
  by_cases hx : 0 < x ∧ x < 1
  · have hexp : a + q - 1 = a - 1 + q := by ring
    rw [betaPDFReal, ite_eq_left hx, betaPDFReal, ite_eq_left hx, hexp, rpow_add hx.1]
    have := (beta_pos ha hb).ne'
    have := (beta_pos haq hb).ne'
    field_simp
  · simp [betaPDFReal, hx]

/-- At or below the sharp threshold `q ≤ -a` the power `x ^ q` is not integrable under the beta
law, so the totalized power bias is the zero measure. -/
theorem powerBias_betaMeasure_of_le {a b q : ℝ} (ha : 0 < a) (hb : 0 < b) (hq : q ≤ -a) :
    (betaMeasure a b).powerBias q = 0 := by
  refine Measure.powerBias_eq_zero_of_not_integrable
    ((ae_mem_Ioo_betaMeasure a b).mono fun _ hx => hx.1.le) fun h => ?_
  have := (integrable_rpow_mul_one_sub_rpow_betaMeasure_iff (q := q) (s := 0) ha hb).1
    (by simpa using h)
  linarith [this.1]

/-- A power-biased beta law is a probability measure exactly above the sharp threshold `-a`. -/
theorem isProbabilityMeasure_powerBias_betaMeasure_iff {a b q : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsProbabilityMeasure ((betaMeasure a b).powerBias q) ↔ -a < q := by
  refine ⟨fun hprob => not_le.1 fun hq => ?_, fun hq => ?_⟩
  · simpa [powerBias_betaMeasure_of_le ha hb hq] using hprob.measure_univ
  · rw [powerBias_betaMeasure ha hb hq]
    exact isProbabilityMeasureBeta (by linarith) hb

end TauCeti.Probability
