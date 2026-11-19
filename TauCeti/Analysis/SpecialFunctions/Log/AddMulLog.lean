/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Solving `x ≤ a + b * log x`

If a positive real `x` satisfies `x ≤ a + b * log x` with `b ≥ 0`, then
`x ≤ 2 * a + 2 * b * (log (2 * b) - 1)`. This turns the implicit bound that effective methods
in Diophantine equations produce, where a quantity is bounded by a linear function of its own
logarithm, into an explicit bound. The proof bounds `log (x / (2 * b))` by `x / (2 * b) - 1`.

A typical source of such an implicit bound is a lower bound `(e * x) ^ (-C) ≤ q ^ (-x)`, as
produced by comparing a lower bound for linear forms in logarithms of the shape of Baker or Yu
with an exponentially small upper bound. Taking logarithms gives `x ≤ b + b * log x` with
`b = C / log q`, hence the explicit bound `x ≤ 2 * b * log (2 * b)`.

## Main results

* `Real.le_two_mul_add_of_le_add_mul_log`: `x ≤ a + b * log x` implies
  `x ≤ 2 * a + 2 * b * (log (2 * b) - 1)`.
* `Real.le_mul_log_of_rpow_neg_le_rpow_neg`: `(e * x) ^ (-C) ≤ q ^ (-x)` with `0 < x` and `1 < q`
  implies `x ≤ 2 * C / log q * log (2 * C / log q)`.

## References

* [J.-H. Evertse, *Diophantine Approximation*, lecture notes, Leiden/Mastermath, 2019],
  Chapter 5, proof of Theorem 5.12, p. 95.
-/

public section

namespace Real

/-- If `0 < x`, `0 ≤ b` and `x ≤ a + b * log x`, then `x ≤ 2 * a + 2 * b * (log (2 * b) - 1)`.
For `b = 0` this reads `x ≤ 2 * a`, by the convention `log 0 = 0`. -/
theorem le_two_mul_add_of_le_add_mul_log {a b x : ℝ} (hb : 0 ≤ b) (hx : 0 < x)
    (h : x ≤ a + b * log x) : x ≤ 2 * a + 2 * b * (log (2 * b) - 1) := by
  rcases hb.eq_or_lt with rfl | hb
  · simp only [zero_mul, add_zero, mul_zero] at h ⊢
    linarith
  have h2b : 0 < 2 * b := by positivity
  -- `log x - log (2 * b) = log (x / (2 * b)) ≤ x / (2 * b) - 1`.
  have hlog := log_le_sub_one_of_pos (div_pos hx h2b)
  rw [log_div hx.ne' h2b.ne'] at hlog
  have hmul : b * (x / (2 * b)) = x / 2 := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlog hb.le]

/-- If `0 ≤ C`, `0 < x`, `1 < q` and `(e * x) ^ (-C) ≤ q ^ (-x)`, then
`x ≤ 2 * C / log q * log (2 * C / log q)`. Taking logarithms gives
`x * log q ≤ C * (1 + log x)`, which `Real.le_two_mul_add_of_le_add_mul_log` solves. -/
theorem le_mul_log_of_rpow_neg_le_rpow_neg {C q x : ℝ} (hC : 0 ≤ C) (hq : 1 < q) (hx : 0 < x)
    (h : (exp 1 * x) ^ (-C) ≤ q ^ (-x)) : x ≤ 2 * C / log q * log (2 * C / log q) := by
  have hlogq : 0 < log q := log_pos hq
  -- taking logarithms: `x * log q ≤ C * (1 + log x)`
  have hlog := log_le_log (by positivity) h
  rw [log_rpow (by positivity), log_rpow (by positivity), log_mul (by positivity) hx.ne',
    log_exp] at hlog
  -- with `b = C / log q`, `x ≤ b + b * log x`
  have hxb : x ≤ C / log q + C / log q * log x := by
    rw [← mul_one_add, div_mul_eq_mul_div, le_div_iff₀ hlogq]
    linarith
  have h2b : 2 * C / log q = 2 * (C / log q) := mul_div_assoc _ _ _
  rw [h2b]
  linarith [le_two_mul_add_of_le_add_mul_log (div_nonneg hC hlogq.le) hx hxb]

end Real
