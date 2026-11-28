/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exponential integrals with a linear weight

To the left of a fixed endpoint, an exponentially decaying weight absorbs a linear factor.
The integral bound is uniform in the left endpoint of the interval.
-/

public section

namespace Real

/-- Integrating the real power `x ^ t` against `1 + c - t` to the left of `c` costs at
most `x ^ c ((log x)⁻¹ + (log x)⁻²)`, independently of the left endpoint. -/
theorem intervalIntegral_rpow_mul_one_add_sub_le {x a c : ℝ} (hx : 1 < x) (hac : a ≤ c) :
    (∫ t in a..c, x ^ t * (1 + c - t)) ≤ x ^ c * ((log x)⁻¹ + (log x)⁻¹ ^ 2) := by
  let l := log x
  have hl : 0 < l := log_pos hx
  have hx₀ : 0 < x := zero_lt_one.trans hx
  let F (t : ℝ) := x ^ t * ((1 + c - t) / l + l⁻¹ ^ 2)
  have hF (t : ℝ) : HasDerivAt F (x ^ t * (1 + c - t)) t := by
    have h₁ := (hasDerivAt_id t).const_rpow hx₀
    have h₂ := (((hasDerivAt_id t).const_sub (1 + c)).div_const l).add_const (l⁻¹ ^ 2)
    convert h₁.mul h₂ using 1
    · rfl
    · simp only [id_eq, mul_one]
      dsimp only [l] at hl ⊢
      field_simp [hl.ne']
      ring
  have hcont : Continuous (fun t : ℝ ↦ x ^ t * (1 + c - t)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F)
    (fun t _ ↦ hF t) (hcont.intervalIntegrable a c)]
  have ha : 0 ≤ F a := by dsimp only [F]; positivity [sub_nonneg.mpr (by linarith : a ≤ 1 + c)]
  simpa only [F, add_sub_cancel_right, one_div] using sub_le_self (F c) ha

end Real
