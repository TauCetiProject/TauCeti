/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Distributions.Pareto
public import TauCeti.Probability.PowerBias
import TauCeti.Probability.Distributions.Beta.Basic
import TauCeti.Probability.Distributions.Gamma.Basic
import TauCeti.Probability.Distributions.Pareto.Basic

/-!
# Power-biased gamma, beta and Pareto laws

The gamma, beta and Pareto families are closed under power biasing
(`MeasureTheory.Measure.powerBias`): multiplying the density by `x ^ q` only shifts one shape
parameter, by `q`, and changes the normalizing constant.

* `TauCeti.Probability.powerBias_gammaMeasure` — `Gamma(a, r)^⟨q⟩ = Gamma(a + q, r)` for
  `q > -a`;
* `TauCeti.Probability.powerBias_betaMeasure` — `Beta(a, b)^⟨q⟩ = Beta(a + q, b)` for `q > -a`;
* `TauCeti.Probability.powerBias_paretoMeasure` — the Pareto law of threshold `t` and shape `r`
  biased by `x ^ q` is the Pareto law of threshold `t` and shape `r - q`, for `q < r`.

Each range of `q` is exactly the range on which `x ^ q` is integrable, so on it the power-biased
law is a probability measure. Each identity is an instance of
`MeasureTheory.Measure.powerBias_withDensity_ofReal`: on the support of the law, the density times
`x ^ q` is a positive constant times the density with the shifted parameter.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, ch. 17 (gamma) and ch. 20 (Pareto); vol. 2, 2nd ed., Wiley, 1995,
  ch. 25 (beta).
-/

public section

open MeasureTheory ProbabilityTheory Real

namespace TauCeti.Probability

/-- Biasing the gamma law of shape `a` and rate `r` by `x ^ q` shifts the shape to `a + q`. -/
theorem powerBias_gammaMeasure {a r q : ℝ} (ha : 0 < a) (hr : 0 < r) (hq : -a < q) :
    (gammaMeasure a r).powerBias q = gammaMeasure (a + q) r := by
  have haq : 0 < a + q := by linarith
  have := isProbabilityMeasure_gammaMeasure haq hr
  rw [gammaMeasure_eq_withDensity_ofReal (a + q)] at this ⊢
  rw [gammaMeasure_eq_withDensity_ofReal]
  refine Measure.powerBias_withDensity_ofReal (measurable_gammaPDFReal a r)
    (ae_of_all _ (gammaPDFReal_nonneg ha hr)) (measurable_gammaPDFReal _ r)
    (div_pos (Gamma_pos_of_pos haq) (mul_pos (Gamma_pos_of_pos ha) (rpow_pos_of_pos hr q))) ?_
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx0
  rcases hx0.lt_or_gt with hx | hx
  · simp [gammaPDFReal, hx.not_ge]
  rw [gammaPDFReal_of_nonneg hx.le, gammaPDFReal_of_nonneg hx.le, rpow_add hr,
    show a + q - 1 = a - 1 + q by ring, rpow_add hx]
  have := (Gamma_pos_of_pos ha).ne'
  have := (Gamma_pos_of_pos haq).ne'
  have := (rpow_pos_of_pos hr q).ne'
  field_simp

/-- Biasing the beta law of shapes `a` and `b` by `x ^ q` shifts the first shape to `a + q`. -/
theorem powerBias_betaMeasure {a b q : ℝ} (ha : 0 < a) (hb : 0 < b) (hq : -a < q) :
    (betaMeasure a b).powerBias q = betaMeasure (a + q) b := by
  have haq : 0 < a + q := by linarith
  have := isProbabilityMeasureBeta haq hb
  rw [betaMeasure_eq_withDensity_ofReal (a + q)] at this ⊢
  rw [betaMeasure_eq_withDensity_ofReal]
  refine Measure.powerBias_withDensity_ofReal (measurable_betaPDFReal a b)
    (ae_of_all _ (betaPDFReal_nonneg ha hb)) (measurable_betaPDFReal _ b)
    (div_pos (beta_pos haq hb) (beta_pos ha hb)) (ae_of_all _ fun x => ?_)
  by_cases hx : 0 < x ∧ x < 1
  · rw [betaPDFReal, ite_eq_left hx, betaPDFReal, ite_eq_left hx,
      show a + q - 1 = a - 1 + q by ring, rpow_add hx.1]
    have := (beta_pos ha hb).ne'
    have := (beta_pos haq hb).ne'
    field_simp
  · simp [betaPDFReal, hx]

/-- Biasing the Pareto law of threshold `t` and shape `r` by `x ^ q` lowers the shape to
`r - q`. -/
theorem powerBias_paretoMeasure {t r q : ℝ} (ht : 0 < t) (hr : 0 < r) (hq : q < r) :
    (paretoMeasure t r).powerBias q = paretoMeasure t (r - q) := by
  have hrq : 0 < r - q := sub_pos.2 hq
  have := isProbabilityMeasure_paretoMeasure ht hrq
  rw [paretoMeasure_eq_withDensity_ofReal t (r - q)] at this ⊢
  rw [paretoMeasure_eq_withDensity_ofReal]
  refine Measure.powerBias_withDensity_ofReal (measurable_paretoPDFReal t r)
    (ae_of_all _ (paretoPDFReal_nonneg ht.le hr.le)) (measurable_paretoPDFReal t _)
    (div_pos (mul_pos hr (rpow_pos_of_pos ht q)) hrq) (ae_of_all _ fun x => ?_)
  by_cases hx : t ≤ x
  · have htr : t ^ r = t ^ q * t ^ (r - q) := by rw [← rpow_add ht, add_sub_cancel]
    rw [paretoPDFReal, ite_eq_left hx, paretoPDFReal, ite_eq_left hx, mul_assoc,
      ← rpow_add (ht.trans_le hx), show -(r + 1) + q = -(r - q + 1) by ring, htr]
    field_simp
  · simp [paretoPDFReal, hx]

end TauCeti.Probability
