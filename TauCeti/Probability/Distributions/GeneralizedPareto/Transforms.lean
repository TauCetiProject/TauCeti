/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedPareto.Moments
import TauCeti.Probability.Moments.IntegrableExpMul

/-!
# Exponential integrability of generalized Pareto laws

At positive scale `s`, the exact exponential-integrability domain is the nonpositive
half-line for positive shape, `Iio s⁻¹` for zero shape, and all of `ℝ` for negative shape.
Thus positive shape has no positive exponential moment, including when its mean exists;
negative shape has every exponential moment because its support is bounded.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 4.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- The exact domain of exponential integrability of a positive-scale generalized Pareto law.
The positive-shape boundary includes zero; the zero-shape exponential boundary is excluded. -/
@[simp]
theorem integrableExpSet_id_generalizedParetoMeasure {s ξ : ℝ} (hs : 0 < s) :
    integrableExpSet id (generalizedParetoMeasure s ξ) =
      if 0 < ξ then Iic 0 else if ξ = 0 then Iio s⁻¹ else univ := by
  let _ := isProbabilityMeasure_generalizedParetoMeasure hs ξ
  have hpos := ae_pos_and_one_add_mul_div_pos_generalizedParetoMeasure s ξ
  by_cases hξ : 0 < ξ
  · simp only [hξ, ↓reduceIte]
    ext t
    simp only [integrableExpSet, mem_ofPred_eq, id_eq, mem_Iic]
    refine ⟨fun ht => le_of_not_gt fun htpos => ?_, fun ht =>
      TauCeti.integrable_exp_mul_of_ge t 0 ht measurable_id.aemeasurable
        (hpos.mono fun _ hx => hx.1.le)⟩
    obtain ⟨n, hn⟩ := exists_nat_gt ξ⁻¹
    have hnξ : ¬ (n : ℝ) * ξ < 1 := by
      have := mul_lt_mul_of_pos_right hn hξ
      rw [inv_mul_cancel₀ hξ.ne'] at this
      linarith
    exact TauCeti.not_integrable_exp_mul_of_not_integrable_pow n
      measurable_id.aemeasurable (hpos.mono fun _ hx => hx.1.le)
      (fun h => hnξ ((integrable_pow_generalizedParetoMeasure_iff hs n).1 h)) htpos ht
  · simp only [hξ, ↓reduceIte]
    by_cases hzero : ξ = 0
    · simp [hzero, generalizedParetoMeasure_zero hs,
        integrableExpSet_id_expMeasure (inv_pos.mpr hs)]
    · simp only [hzero, ↓reduceIte]
      have hneg : ξ < 0 := lt_of_le_of_ne (le_of_not_gt hξ) hzero
      apply Set.eq_univ_of_forall
      intro t
      apply integrable_exp_mul_of_mem_Icc (a := 0) (b := -s / ξ)
        measurable_id.aemeasurable
      filter_upwards [hpos] with x hx
      refine ⟨hx.1.le, ?_⟩
      apply (le_div_iff_of_neg hneg).2
      have hdiv : -1 < ξ * x / s := by linarith [hx.2]
      have hmul : -s < ξ * x := by
        have := (lt_div_iff₀ hs).1 hdiv
        linarith
      simpa only [id_eq, mul_comm] using hmul.le

end TauCeti.Probability
