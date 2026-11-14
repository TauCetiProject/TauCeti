/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithms of prime-power divisors of an integer

If `∏ p ∈ P, p ^ e p` divides a nonzero integer `z`, then the divisor is at most `|z|`, and taking
logarithms gives `∑ p ∈ P, e p * log p ≤ log |z|`.

## Main results

* `Int.sum_mul_log_le_log_abs`: `∑ p ∈ P, e p * log p ≤ log |z|` when `∏ p ∈ P, p ^ e p ∣ z ≠ 0`.
-/

public section

/-- If `∏ p ∈ P, p ^ e p` divides a nonzero integer `z`, then `∑ p ∈ P, e p * log p ≤ log |z|`. -/
theorem Int.sum_mul_log_le_log_abs {P : Finset ℕ} (e : ℕ → ℕ) {z : ℤ} (hz : z ≠ 0)
    (h : ∏ p ∈ P, (p : ℤ) ^ e p ∣ z) :
    ∑ p ∈ P, (e p : ℝ) * Real.log p ≤ Real.log |(z : ℝ)| := by
  have hd : ∏ p ∈ P, (p : ℤ) ^ e p ≠ 0 := ne_zero_of_dvd_ne_zero hz h
  have hle : ∏ p ∈ P, (p : ℝ) ^ e p ≤ |(z : ℝ)| := by
    exact_mod_cast Int.le_of_dvd (abs_pos.2 hz) ((dvd_abs _ _).2 h)
  have hpos : 0 < ∏ p ∈ P, (p : ℝ) ^ e p :=
    (Finset.prod_nonneg fun _ _ => by positivity).lt_of_ne' (by exact_mod_cast hd)
  calc ∑ p ∈ P, (e p : ℝ) * Real.log p = Real.log (∏ p ∈ P, (p : ℝ) ^ e p) := by
        rw [Real.log_prod fun p hp => (Finset.prod_ne_zero_iff.1 hpos.ne' p hp)]
        simp [Real.log_pow]
    _ ≤ Real.log |(z : ℝ)| := Real.log_le_log hpos hle
