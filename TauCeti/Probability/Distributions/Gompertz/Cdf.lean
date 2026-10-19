/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gompertz.PDF

/-!
# Gompertz cumulative distribution and hazard

On the nonnegative half-line the Gompertz survival function is
`exp (-η * (exp (b * x) - 1))`. In particular the cumulative hazard is
`η * (exp (b * x) - 1)` and the hazard is `η * b * exp (b * x)`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {η b x : ℝ}

/-- The Gompertz cdf is zero below zero and has its double-exponential formula above zero. -/
theorem cdf_gompertzMeasure_eq (hη : 0 < η) (hb : 0 < b) (x : ℝ) :
    cdf (gompertzMeasure η b) x =
      if x ≤ 0 then 0 else 1 - exp (-η * (exp (b * x) - 1)) := by
  let _ := isProbabilityMeasure_expMeasure one_pos
  let _ := isProbabilityMeasure_gompertzMeasure hη hb
  by_cases hx : x ≤ 0
  · rw [ite_eq_left hx, cdf_eq_real, measureReal_def]
    have hz : gompertzMeasure η b (Iic x) = 0 := by
      exact measure_mono_null (fun y hy => not_lt.mpr ((mem_Iic.mp hy).trans hx))
        (ae_iff.mp (ae_pos_gompertzMeasure η b))
    rw [hz, ENNReal.toReal_zero]
  · have hx' : 0 < x := lt_of_not_ge hx
    have he : 0 ≤ η * (exp (b * x) - 1) :=
      mul_nonneg hη.le (sub_nonneg.mpr (one_le_exp (by positivity)))
    have heq : (fun e : ℝ => log (1 + e / η) / b) ⁻¹' Iic x =ᵐ[expMeasure 1]
        Iic (η * (exp (b * x) - 1)) := by
      filter_upwards [ae_pos_expMeasure 1] with e he
      simp only [mem_preimage, mem_Iic, div_le_iff₀ hb,
        log_le_iff_le_exp (by positivity : 0 < 1 + e / η)]
      apply propext
      rw [mul_comm x b]
      constructor <;> intro hh
      · have hdiv : e / η ≤ exp (b * x) - 1 := by linarith
        have := (div_le_iff₀ hη).mp hdiv
        nlinarith
      · apply le_of_sub_nonneg
        have hnum : e ≤ (exp (b * x) - 1) * η := by nlinarith
        have := (div_le_iff₀ hη).mpr hnum
        linarith
    rw [ite_eq_right hx, cdf_eq_real, gompertzMeasure_of_pos hη hb,
      map_measureReal_apply (by fun_prop) measurableSet_Iic,
      measureReal_congr heq, ← cdf_eq_real, cdf_expMeasure_eq one_pos, ite_eq_left he, one_mul]
    congr 2
    ring

/-- The Gompertz survival function on the nonnegative half-line is strictly positive. -/
theorem one_sub_cdf_gompertzMeasure (hη : 0 < η) (hb : 0 < b) (hx : 0 ≤ x) :
    1 - cdf (gompertzMeasure η b) x = exp (-η * (exp (b * x) - 1)) := by
  rw [cdf_gompertzMeasure_eq hη hb]
  split_ifs with h
  · have : x = 0 := le_antisymm h hx
    simp [this]
  · ring

/-- The Gompertz hazard grows exponentially on the positive half-line. -/
theorem gompertzPDFReal_div_one_sub_cdf (hη : 0 < η) (hb : 0 < b) (hx : 0 < x) :
    gompertzPDFReal η b x / (1 - cdf (gompertzMeasure η b) x) = η * b * exp (b * x) := by
  rw [gompertzPDFReal_of_pos hη hb hx, one_sub_cdf_gompertzMeasure hη hb hx.le,
    mul_div_cancel_right₀ _ (exp_pos _).ne']

/-- The Gompertz cumulative hazard on the nonnegative half-line, including its value zero at
the origin. -/
theorem neg_log_one_sub_cdf_gompertzMeasure (hη : 0 < η) (hb : 0 < b) (hx : 0 ≤ x) :
    -log (1 - cdf (gompertzMeasure η b) x) = η * (exp (b * x) - 1) := by
  rw [one_sub_cdf_gompertzMeasure hη hb hx, log_exp, neg_mul, neg_neg]

end TauCeti.Probability
