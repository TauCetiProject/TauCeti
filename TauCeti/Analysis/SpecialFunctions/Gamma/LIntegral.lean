/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity

/-!
# Lower Lebesgue integral form of the Gamma integral

Provides the lower Lebesgue (`lintegral`) version of Mathlib's
`Real.integral_rpow_mul_exp_neg_mul_Ioi`.

## Main results

* `Real.lintegral_rpow_mul_exp_neg_mul_Ioi`: for `b > 0` and `r > 0`,
  `∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t ^ (b - 1) * rexp (-(r * t))) =`
  `ENNReal.ofReal ((1 / r) ^ b * Gamma b)`.
-/

public section

open MeasureTheory

namespace Real

/-- The Gamma integral as a lower Lebesgue integral on `(0, ∞)`. -/
theorem lintegral_rpow_mul_exp_neg_mul_Ioi {b r : ℝ} (hb : 0 < b) (hr : 0 < r) :
    ∫⁻ t : ℝ in Set.Ioi 0, ENNReal.ofReal (t ^ (b - 1) * rexp (-(r * t))) =
      ENNReal.ofReal ((1 / r) ^ b * Gamma b) := by
  have h_int : ∫ t : ℝ in Set.Ioi 0, t ^ (b - 1) * rexp (-(r * t)) =
      (1 / r) ^ b * Gamma b :=
    integral_rpow_mul_exp_neg_mul_Ioi hb hr
  have h_ne : (1 / r) ^ b * Gamma b ≠ 0 := by
    have := Gamma_pos_of_pos hb
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal (.of_integral_ne_zero (h_int.trans_ne h_ne))
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ by
      have := Set.mem_Ioi.1 ht
      positivity), h_int]

end Real
