/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Beta.Basic

/-!
# The arcsine distribution

The arcsine distribution on the unit interval is the beta distribution with both shape
parameters equal to one half. This file records the measure-level definition, its exact
topological support, natural moments, mean, variance, and exponential-integrability domain.
These results let later density, distribution-function, and geometric constructions reuse the
existing beta theory without introducing a second measure.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley, 1995, Chapter 25.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- The arcsine law on `[0, 1]`, realized as the beta law with shapes `(1 / 2, 1 / 2)`. -/
def arcsineMeasure : Measure ℝ :=
  betaMeasure (1 / 2) (1 / 2)

/-- The arcsine law is the symmetric beta law with both shape parameters one half. -/
theorem arcsineMeasure_eq_betaMeasure :
    arcsineMeasure = betaMeasure (1 / 2) (1 / 2) :=
  (rfl)

/-- The arcsine law is a probability measure. -/
noncomputable instance isProbabilityMeasure_arcsineMeasure :
    IsProbabilityMeasure arcsineMeasure :=
  isProbabilityMeasureBeta (by norm_num) (by norm_num)

/-- An arcsine variable lies almost everywhere in the open unit interval. -/
theorem ae_mem_Ioo_arcsineMeasure : ∀ᵐ x ∂arcsineMeasure, x ∈ Ioo (0 : ℝ) 1 := by
  simpa only [arcsineMeasure] using ae_mem_Ioo_betaMeasure (1 / 2) (1 / 2)

/-- The topological support of the arcsine law is the closed unit interval. -/
@[simp]
theorem support_arcsineMeasure : arcsineMeasure.support = Icc 0 1 := by
  simpa only [arcsineMeasure] using
    support_betaMeasure (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num)

/-- Every natural power is integrable against the arcsine law. -/
theorem integrable_pow_arcsineMeasure (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) arcsineMeasure := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
  filter_upwards [ae_mem_Ioo_arcsineMeasure] with x hx
  simpa only [norm_pow, Real.norm_eq_abs, norm_one] using
    pow_le_one₀ (abs_nonneg x)
      (abs_le.mpr ⟨(show (-1 : ℝ) ≤ 0 by norm_num).trans hx.1.le, hx.2.le⟩)

/-- The natural moments of the arcsine law, inherited from its beta realization. -/
@[simp]
theorem integral_pow_arcsineMeasure (n : ℕ) :
    ∫ x, x ^ n ∂arcsineMeasure =
      Real.Gamma (1 / 2 + n) * Real.Gamma (1 / 2 + 1 / 2) /
        (Real.Gamma (1 / 2) * Real.Gamma (1 / 2 + 1 / 2 + n)) := by
  simpa only [arcsineMeasure] using
    integral_pow_betaMeasure (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num) n

/-- The mean of the arcsine law is one half. -/
@[simp]
theorem integral_id_arcsineMeasure : ∫ x, x ∂arcsineMeasure = 1 / 2 := by
  rw [arcsineMeasure, integral_id_betaMeasure (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)]
  norm_num

/-- The variance of the arcsine law is one eighth. -/
@[simp]
theorem variance_id_arcsineMeasure : variance id arcsineMeasure = 1 / 8 := by
  rw [arcsineMeasure, variance_id_betaMeasure (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)]
  norm_num

/-- Every exponential moment of the arcsine law exists. -/
@[simp]
theorem integrableExpSet_id_arcsineMeasure : integrableExpSet id arcsineMeasure = univ := by
  simpa only [arcsineMeasure] using
    integrableExpSet_id_betaMeasure (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num)

end TauCeti.Probability
