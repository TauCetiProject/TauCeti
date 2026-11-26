/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# Power bounds for Gaussian weights

On the positive ray a Gaussian with a real power weight is bounded by a constant times any
power whose exponent is at most that of the weight. This gives a single bound usable both
near zero and at infinity.
-/

public section

namespace Real

/-- On the positive ray, `x ^ a * exp (-c * x²)` is bounded by a constant times `x ^ b`
whenever `b ≤ a` and `c > 0`. -/
theorem exists_rpow_mul_exp_neg_mul_sq_le_mul_rpow {a b c : ℝ} (hab : b ≤ a) (hc : 0 < c) :
    ∃ C ≥ 0, ∀ x : ℝ, 0 < x → x ^ a * exp (-c * x ^ 2) ≤ C * x ^ b := by
  obtain ⟨C, hC, h⟩ := TauCeti.exists_rpow_mul_exp_neg_mul_le
    (σ := (a - b) / 2) (by linarith) hc
  refine ⟨C, hC, fun x hx ↦ ?_⟩
  have hpow : (x ^ 2) ^ ((a - b) / 2) = x ^ (a - b) := by
    rw [← rpow_two, ← rpow_mul hx.le, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  have hbound := h (x ^ 2) (sq_nonneg x)
  rw [hpow, ← neg_mul] at hbound
  calc
    x ^ a * exp (-c * x ^ 2) = (x ^ (a - b) * exp (-c * x ^ 2)) * x ^ b := by
      rw [mul_right_comm, ← rpow_add hx, sub_add_cancel]
    _ ≤ C * x ^ b := mul_le_mul_of_nonneg_right hbound (rpow_nonneg hx.le _)

end Real
