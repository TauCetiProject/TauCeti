/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gamma
public import TauCeti.Probability.PowerBias
import TauCeti.Probability.Distributions.Gamma.Basic

/-!
# Power-biased gamma laws

The gamma family is closed under power biasing (`MeasureTheory.Measure.powerBias`): multiplying
the density by `x ^ q` only shifts the shape parameter, by `q`, and changes the normalizing
constant.

* `TauCeti.Probability.powerBias_gammaMeasure` — `Gamma(a, r)^⟨q⟩ = Gamma(a + q, r)` for
  `q > -a`.

The range of `q` is exactly the range on which `x ^ q` is integrable, so on it the power-biased law
is a probability measure. The identity is an instance of
`MeasureTheory.Measure.powerBias_withDensity_ofReal`: on the support of the law, the density times
`x ^ q` is a positive constant times the density with the shifted shape.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, ch. 17.
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

end TauCeti.Probability
