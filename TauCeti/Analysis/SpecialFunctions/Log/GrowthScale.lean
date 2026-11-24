/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Analysis.SpecialFunctions.Log.TwoAdd

/-!
# Logarithmic growth scales

Growth bounds for entire functions of order one, such as `1/Γ`, are naturally obtained in the
shape `A r log (1 + r) + B r` with `r = ‖s‖`. The single scale `(1 + r) log (2 + r)` absorbs both
terms for `r ≥ 0`, since `log (2 + r) ≥ log 2 ≥ 1/2`.

## Main results

* `Real.mul_mul_log_one_add_add_mul_le`: for `A, B, r ≥ 0`,
  `A r log (1 + r) + B r ≤ (A + 2 B) (1 + r) log (2 + r)`.
* `Real.log_mul_two_mul_add_le`: for `q ≥ 1`, `r ≥ 0` and `c ≥ 1`,
  `log (q (2 r + c)) ≤ 2 log (q (r + c))`.
* `Real.mul_log_le_mul_log_one_add`: for `1 ≤ t` and any `p : ℝ`,
  `p log t ≤ p log (1 + t) + |p| log 2`.
* `Real.mul_add_two_mul_log_le`: for `c ≥ 0` and `r ≥ 1`,
  `(c r + 2) log (c r + 2) ≤ (c + 2) (2 log (c + 2) + 1) r log (1 + r)`.
-/

public section

namespace Real

/-- The growth scale `(1 + r) log (2 + r)` absorbs both `r log (1 + r)` and `r`. -/
theorem mul_mul_log_one_add_add_mul_le {A B r : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 ≤ r) :
    A * r * log (1 + r) + B * r ≤ (A + 2 * B) * (1 + r) * log (2 + r) := by
  have hlog : log (1 + r) ≤ log (2 + r) := log_le_log (by linarith) (by linarith)
  have hlog₁ : 0 ≤ log (1 + r) := log_nonneg (by linarith)
  -- `log 2 ≥ 1 - 2⁻¹`.
  have hlog₂ : 1 / 2 ≤ log (2 + r) := by
    have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have := log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ 2 + r)
    norm_num at h
    linarith
  have h₁ : r * log (1 + r) ≤ (1 + r) * log (2 + r) :=
    mul_le_mul (by linarith) hlog hlog₁ (by linarith)
  -- `r ≤ 1 + r` and `1 ≤ 2 log (2 + r)`.
  have h₂ : r ≤ 2 * ((1 + r) * log (2 + r)) := by nlinarith
  calc
    A * r * log (1 + r) + B * r ≤
        A * ((1 + r) * log (2 + r)) + B * (2 * ((1 + r) * log (2 + r))) := by
      rw [mul_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_left h₁ hA) (mul_le_mul_of_nonneg_left h₂ hB)
    _ = (A + 2 * B) * (1 + r) * log (2 + r) := by ring

/-- Doubling the variable inside a shifted logarithmic scale `log (q (r + c))` at most doubles the
logarithm when `1 ≤ q`, `0 ≤ r`, and `1 ≤ c`. -/
theorem log_mul_two_mul_add_le {q r c : ℝ} (hq : 1 ≤ q) (hr : 0 ≤ r) (hc : 1 ≤ c) :
    log (q * (2 * r + c)) ≤ 2 * log (q * (r + c)) := by
  have hsq : q * (2 * r + c) ≤ (q * (r + c)) ^ 2 := by
    calc q * (2 * r + c) ≤ q * (r + c) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith) (zero_le_one.trans hq)
      _ ≤ q ^ 2 * (r + c) ^ 2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
      _ = (q * (r + c)) ^ 2 := (mul_pow _ _ _).symm
  exact (log_le_log (by positivity) hsq).trans_eq (by rw [log_pow, Nat.cast_ofNat])

/-- For `t ≥ 1` and any real exponent `p`, replacing `log t` by `log (1 + t)` changes `p * log t`
by at most `|p| * log 2`. -/
theorem mul_log_le_mul_log_one_add (p : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    p * log t ≤ p * log (1 + t) + |p| * log 2 := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlo : log t ≤ log (1 + t) := log_le_log ht0 (by linarith)
  have hhi : log (1 + t) - log t ≤ log 2 := by
    have h1 : log (1 + t) ≤ log (2 * t) := log_le_log (by linarith) (by linarith)
    rw [log_mul two_ne_zero ht0.ne'] at h1
    linarith
  have habs : |log t - log (1 + t)| ≤ log 2 := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hlo)]
    exact hhi
  have hmul : p * (log t - log (1 + t)) ≤ |p| * log 2 :=
    (le_abs_self _).trans <| by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left habs (abs_nonneg p)
  linarith

/-- For a nonnegative scale `c` and radius `r ≥ 1`, an affine logarithmic growth term is
bounded by a constant depending on `c` times `r * log (1 + r)`. -/
theorem mul_add_two_mul_log_le {c r : ℝ} (hc : 0 ≤ c) (hr : 1 ≤ r) :
    (c * r + 2) * log (c * r + 2) ≤
      (c + 2) * (2 * log (c + 2) + 1) * r * log (1 + r) := by
  let K := c + 2
  let D := K * (2 * log K + 1)
  have hK : 1 < K := by dsimp [K]; linarith
  have hL : 1 / 2 ≤ log (1 + r) := by
    convert one_half_le_log_two_add (r := r - 1) (by linarith) using 1
    congr 1
    ring
  have hy : 0 < c * r + 2 := by positivity
  have hyK : c * r + 2 ≤ K * r := by
    dsimp [K]
    nlinarith
  have hlog : log (c * r + 2) ≤ (2 * log K + 1) * log (1 + r) := by
    have h := log_le_log hy hyK
    rw [log_mul (by positivity : K ≠ 0) (by positivity : r ≠ 0)] at h
    have hrlog : log r ≤ log (1 + r) :=
      log_le_log (by positivity) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hL (log_pos hK).le]
  have hprod : (c * r + 2) * log (c * r + 2) ≤
      D * r * log (1 + r) := by
    have h := mul_le_mul hyK hlog (log_nonneg (by nlinarith : 1 ≤ c * r + 2))
      (by positivity : 0 ≤ K * r)
    dsimp [D]
    nlinarith [h]
  exact hprod

end Real
