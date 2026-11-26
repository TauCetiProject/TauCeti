/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bounding powers of the logarithm by powers of the argument

Mathlib's `Real.log_le_rpow_div` bounds `log x ≤ x ^ ε / ε` for `0 ≤ x` and `0 < ε`. Applying it
at exponent `ε / p` and raising both sides to the `p`-th power extends the inequality to every
nonnegative real exponent `p` and every natural exponent `k` on `x ≥ 1`:

`(log x) ^ p ≤ (p / ε) ^ p * x ^ ε`.

The condition `1 ≤ x` is needed both for `0 ≤ log x` (when raising an inequality to a power) and
for the boundary case `p = 0`, where the statement reduces to `1 ≤ x ^ ε`.

## Main results

* `TauCeti.log_rpow_le_div_rpow_mul_rpow`: `(Real.log x) ^ p ≤ (p / ε) ^ p * x ^ ε` for `1 ≤ x`,
  `0 < ε`, and `0 ≤ p`.
* `TauCeti.log_pow_le_div_pow_mul_rpow`: `(Real.log x) ^ k ≤ ((k : ℝ) / ε) ^ k * x ^ ε` for
  `1 ≤ x`, `0 < ε`, and `k : ℕ`.
* `TauCeti.sqrt_mul_log_sq_le_div_sq_mul_rpow`:
  `√x * (Real.log x) ^ 2 ≤ (2 / ε) ^ 2 * x ^ (1 / 2 + ε)` for `1 ≤ x` and `0 < ε`.
-/

public section

open scoped Real

namespace TauCeti

/-- For `1 ≤ x`, `0 < ε`, and `0 ≤ p`, the `p`-th real power of `log x` is bounded by
`(p / ε) ^ p * x ^ ε`. -/
theorem log_rpow_le_div_rpow_mul_rpow {x ε p : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) (hp : 0 ≤ p) :
    Real.log x ^ p ≤ (p / ε) ^ p * x ^ ε := by
  rcases hp.eq_or_lt with rfl | hp
  · simpa using Real.one_le_rpow hx hε.le
  · have hx0 : 0 ≤ x := zero_le_one.trans hx
    have hlog : Real.log x ≤ x ^ (ε / p) / (ε / p) :=
      Real.log_le_rpow_div hx0 (div_pos hε hp)
    have hdiv : x ^ (ε / p) / (ε / p) = p / ε * x ^ (ε / p) := by
      field_simp
    calc
      Real.log x ^ p ≤ (p / ε * x ^ (ε / p)) ^ p :=
        Real.rpow_le_rpow (Real.log_nonneg hx) (hdiv ▸ hlog) hp.le
      _ = (p / ε) ^ p * (x ^ (ε / p)) ^ p :=
        Real.mul_rpow (div_nonneg hp.le hε.le) (Real.rpow_nonneg hx0 _)
      _ = (p / ε) ^ p * x ^ ε := by
        rw [← Real.rpow_mul hx0, div_mul_cancel₀ ε hp.ne']

/-- For `1 ≤ x`, `0 < ε`, and `k : ℕ`, `(log x) ^ k ≤ (k / ε) ^ k * x ^ ε`. -/
theorem log_pow_le_div_pow_mul_rpow {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) (k : ℕ) :
    Real.log x ^ k ≤ ((k : ℝ) / ε) ^ k * x ^ ε := by
  simpa only [Real.rpow_natCast] using
    log_rpow_le_div_rpow_mul_rpow hx hε (Nat.cast_nonneg k)

/-- For `1 ≤ x` and `0 < ε`, `√x * (log x) ^ 2 ≤ (2 / ε) ^ 2 * x ^ (1 / 2 + ε)`. -/
theorem sqrt_mul_log_sq_le_div_sq_mul_rpow {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    √x * Real.log x ^ 2 ≤ (2 / ε) ^ 2 * x ^ ((1 / 2 : ℝ) + ε) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  calc
    √x * Real.log x ^ 2 ≤ x ^ (1 / 2 : ℝ) * (((2 : ℝ) / ε) ^ 2 * x ^ ε) := by
      rw [← Real.sqrt_eq_rpow]
      exact mul_le_mul_of_nonneg_left (log_pow_le_div_pow_mul_rpow hx hε 2) (Real.sqrt_nonneg x)
    _ = (2 / ε) ^ 2 * (x ^ (1 / 2 : ℝ) * x ^ ε) := by ring
    _ = (2 / ε) ^ 2 * x ^ ((1 / 2 : ℝ) + ε) := by rw [← Real.rpow_add hx0]

end TauCeti
