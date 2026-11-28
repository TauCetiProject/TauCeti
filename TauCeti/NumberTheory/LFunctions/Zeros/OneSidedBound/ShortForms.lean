/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Archimedean size after prime-gain normalization

The divisibility gain of an unnormalized composite theta lift occurs with a factor of two in
its squared-norm bound. The logarithm of the normalizing scalar contains minus that gain;
rescaling cancels it and leaves only the analytic and rounding errors. This is the size
calculation of `New.Data.span_short_integralRamified_eq_top` in `New/Reduction/ShortAndEnough`
of lsernau/grh-lean (`72fead1`).
-/

public section

namespace TauCeti.OneSidedBound

open Real

/-- Multiplying by a scalar whose log norm removes `gain` cancels the gain term in the
squared norm. With `a = x * b`, the two costs `2 * f * a * (log b)^3`, the rounding cost
`2 * b`, and the projection cost `x^99` fit in `f * a * (log b)^4`. -/
theorem norm_sq_smul_le_exp_of_prime_gain_bound {𝕜 V : Type*}
    [SeminormedAddGroup 𝕜] [SeminormedAddGroup V] [SMulZeroClass 𝕜 V] [IsBoundedSMul 𝕜 V]
    (c : 𝕜) (v : V) {H gain f x b : ℝ}
    (hf : 1 ≤ f) (hx : 1 ≤ x) (hxb : x ^ 98 ≤ b) (hb : 5 ≤ log b)
    (hc : log ‖c‖ ≤ -gain + f * (x * b) * log b ^ 3 + b)
    (hv : ‖v‖ ^ 2 ≤ exp (H + 2 * gain + 2 * (f * (x * b) * log b ^ 3) + x ^ 99)) :
    ‖c • v‖ ^ 2 ≤ exp (H + f * (x * b) * log b ^ 4) := by
  have hb₀ : 0 ≤ b := (pow_nonneg (zero_le_one.trans hx) _).trans hxb
  have ha : 0 ≤ f * (x * b) := by positivity
  have hb_le : b ≤ f * (x * b) := by
    calc
      b ≤ x * b := le_mul_of_one_le_left hb₀ hx
      _ ≤ f * (x * b) := le_mul_of_one_le_left (by positivity) hf
  have hx_le : x ^ 99 ≤ f * (x * b) := by
    rw [pow_succ' x 98]
    exact (mul_le_mul_of_nonneg_left hxb (zero_le_one.trans hx)).trans
      (le_mul_of_one_le_left (by positivity) hf)
  have hgap : 1 ≤ log b - 4 := by linarith
  have hcub : (5 : ℝ) ^ 3 ≤ log b ^ 3 := by gcongr
  have hreserve : 3 ≤ log b ^ 3 * (log b - 4) :=
    (by linarith : 3 ≤ log b ^ 3).trans (le_mul_of_one_le_right (by positivity) hgap)
  have herr : 4 * (f * (x * b) * log b ^ 3) + 2 * b + x ^ 99 ≤
      f * (x * b) * log b ^ 4 := by
    nlinarith only [mul_le_mul_of_nonneg_right hreserve ha, hb_le, hx_le]
  have hnorm := le_exp_of_log_le hc
  calc
    ‖c • v‖ ^ 2 ≤ ‖c‖ ^ 2 * ‖v‖ ^ 2 := by
      rw [← mul_pow]
      gcongr
      exact norm_smul_le c v
    _ ≤ exp (-gain + f * (x * b) * log b ^ 3 + b) ^ 2 *
        exp (H + 2 * gain + 2 * (f * (x * b) * log b ^ 3) + x ^ 99) := by gcongr
    _ ≤ exp (H + f * (x * b) * log b ^ 4) := by
      rw [sq, ← exp_add, ← exp_add, exp_le_exp]
      linarith only [herr]

end TauCeti.OneSidedBound
