/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.PowerBias
public import TauCeti.Probability.Distributions.Pareto.Basic

/-!
# Power-biased Pareto laws

The Pareto family is closed under power biasing (`MeasureTheory.Measure.powerBias`): multiplying
the density by `x ^ q` only lowers the shape parameter, by `q`, and changes the normalizing
constant.

* `TauCeti.Probability.powerBias_paretoMeasure` — the Pareto law of threshold `t` and shape `r`
  biased by `x ^ q` is the Pareto law of threshold `t` and shape `r - q`, for `q < r`.

The range of `q` is exactly the range on which `x ^ q` is integrable, so on it the power-biased law
is a probability measure. The identity is an instance of
`MeasureTheory.Measure.powerBias_withDensity_ofReal`: on the support of the law, the density times
`x ^ q` is a positive constant times the density with the shifted shape.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, ch. 20.
-/

public section

open MeasureTheory ProbabilityTheory Real

namespace TauCeti.Probability

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
