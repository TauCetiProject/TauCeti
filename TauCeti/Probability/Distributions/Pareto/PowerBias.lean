/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.PowerBias
public import TauCeti.Probability.Distributions.Pareto.Basic
public import TauCeti.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Power-biased Pareto laws

The Pareto family is closed under power biasing (`MeasureTheory.Measure.powerBias`): multiplying
the density by `x ^ q` only lowers the shape parameter, by `q`, and changes the normalizing
constant.

* `TauCeti.Probability.powerBias_paretoMeasure` — the Pareto law of threshold `t` and shape `r`
  biased by `x ^ q` is the Pareto law of threshold `t` and shape `r - q`, for `q < r`.
* `TauCeti.Probability.powerBias_paretoMeasure_of_le` — for `r ≤ q` the power bias is zero.
* `TauCeti.Probability.isProbabilityMeasure_powerBias_paretoMeasure_iff` — the power bias is a
  probability measure exactly when `q < r`.

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
  refine Measure.powerBias_withDensity_ofReal (measurable_paretoPDFReal t r).aemeasurable
    (ae_of_all _ (paretoPDFReal_nonneg ht.le hr.le))
    (div_pos (mul_pos hr (rpow_pos_of_pos ht q)) hrq) (ae_of_all _ fun x => ?_)
  by_cases hx : t ≤ x
  · have htr : t ^ r = t ^ q * t ^ (r - q) := by rw [← rpow_add ht, add_sub_cancel]
    have hexp : -(r + 1) + q = -(r - q + 1) := by ring
    rw [paretoPDFReal, ite_eq_left hx, paretoPDFReal, ite_eq_left hx, mul_assoc,
      ← rpow_add (ht.trans_le hx), hexp, htr]
    field_simp
  · simp [paretoPDFReal, hx]

/-- At or above the sharp threshold `r ≤ q` the power `x ^ q` is not integrable under the Pareto
law, so the totalized power bias is the zero measure. -/
theorem powerBias_paretoMeasure_of_le {t r q : ℝ} (ht : 0 < t) (hr : 0 < r) (hq : r ≤ q) :
    (paretoMeasure t r).powerBias q = 0 :=
  Measure.powerBias_eq_zero_of_not_integrable
    ((ae_paretoMeasure_mem_Ici t r).mono fun _ hx => ht.le.trans hx)
    (by rw [integrable_rpow_paretoMeasure_iff ht hr q]; exact not_lt.2 hq)

/-- A power-biased Pareto law is a probability measure exactly below the sharp threshold `r`. -/
theorem isProbabilityMeasure_powerBias_paretoMeasure_iff {t r q : ℝ} (ht : 0 < t) (hr : 0 < r) :
    IsProbabilityMeasure ((paretoMeasure t r).powerBias q) ↔ q < r := by
  refine ⟨fun hprob => not_le.1 fun hq => ?_, fun hq => ?_⟩
  · simpa [powerBias_paretoMeasure_of_le ht hr hq] using hprob.measure_univ
  · rw [powerBias_paretoMeasure ht hr hq]
    exact isProbabilityMeasure_paretoMeasure ht (sub_pos.2 hq)

end TauCeti.Probability
