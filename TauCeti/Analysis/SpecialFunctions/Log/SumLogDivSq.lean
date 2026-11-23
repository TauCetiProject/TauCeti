/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Explicit tails of `∑ log n / n²`

For a natural number `N ≥ 3`, the tail `∑_{n > N} log n / n²` is at most `(1 + log N) / N`.
The function `h(x) = (1 + log x) / x` is an antiderivative of `-log x / x²`, and for `x ≥ 4` one
step of the telescoping sum already dominates the term: `log x / x² ≤ h(x - 1) - h(x)`. This uses
`log (x - 1) ≥ log x - 1 / (x - 1)` and `x ≤ (x - 1) log x`, the latter from `log 4 ≥ 4 / 3`,
that is `exp 4 ≤ 64`.

These bounds control `-Re (L'/L)(σ, χ) = ∑ Λ(n) Re χ(n) / n^σ` at `σ = 2` once the first few
terms are handled explicitly, since `Λ(n) ≤ log n`.

## Main results

* `Real.sum_Ioc_log_div_sq_add_le`: for `3 ≤ N ≤ M`,
  `∑_{N < n ≤ M} log n / n² + (1 + log M) / M ≤ (1 + log N) / N`.
* `Real.sum_Ioc_log_div_sq_le`: for `3 ≤ N` and every `M`,
  `∑_{N < n ≤ M} log n / n² ≤ (1 + log N) / N`.
* `Real.summable_log_div_sq_of_lt`, `Real.tsum_log_div_sq_of_lt_le`: the series
  `∑_{n > N} log n / n²` converges, and for `3 ≤ N` its sum is at most `(1 + log N) / N`.
-/

public section

open Finset

namespace Real

/-- `log 4 ≥ 4 / 3`, since `exp 4 < 2.7182818286 ^ 4 < 64`. -/
private theorem four_div_three_le_log_four : 4 / 3 ≤ log 4 := by
  have h64 : exp 4 ≤ 64 := by
    rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, exp_natCast_mul]
    calc exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := by
          gcongr
          exact exp_one_lt_d9.le
      _ ≤ 64 := by norm_num
  have h : 4 ≤ log 64 := (le_log_iff_exp_le (by norm_num)).mpr h64
  rw [show (64 : ℝ) = 4 ^ 3 by norm_num, log_pow] at h
  push_cast at h
  linarith

/-- The telescoping step: for `x ≥ 4`, `log x / x² + h(x) ≤ h(x - 1)` with
`h(x) = (1 + log x) / x`. -/
private theorem log_div_sq_add_one_add_log_div_le {x : ℝ} (hx : 4 ≤ x) :
    log x / x ^ 2 + (1 + log x) / x ≤ (1 + log (x - 1)) / (x - 1) := by
  have hx1 : 0 < x - 1 := by linarith
  have hx0 : 0 < x := by linarith
  have hlog : log x - 1 / (x - 1) ≤ log (x - 1) := by
    have h := log_le_sub_one_of_pos (div_pos hx0 hx1)
    rw [log_div hx0.ne' hx1.ne', show x / (x - 1) - 1 = 1 / (x - 1) by field_simp; ring] at h
    linarith
  have hL : 4 / 3 ≤ log x :=
    four_div_three_le_log_four.trans (log_le_log (by norm_num) hx)
  -- `x ≤ (x - 1) log x` is the cross-multiplied form of the step.
  have hxL : x ≤ (x - 1) * log x := by nlinarith
  calc log x / x ^ 2 + (1 + log x) / x
      ≤ (1 + (log x - 1 / (x - 1))) / (x - 1) := by
        rw [div_add_div _ _ (by positivity) hx0.ne', div_le_div_iff₀ (by positivity) hx1]
        field_simp
        nlinarith
    _ ≤ (1 + log (x - 1)) / (x - 1) := by gcongr

/-- For `3 ≤ N ≤ M`, `∑_{N < n ≤ M} log n / n² + (1 + log M) / M ≤ (1 + log N) / N`. -/
theorem sum_Ioc_log_div_sq_add_le {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) :
    ∑ n ∈ Ioc N M, log n / (n : ℝ) ^ 2 + (1 + log M) / M ≤ (1 + log N) / N := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [sum_Ioc_succ_top hNM]
    have h := log_div_sq_add_one_add_log_div_le (x := ((M + 1 : ℕ) : ℝ))
      (by push_cast; exact_mod_cast (show 4 ≤ M + 1 by omega))
    rw [Nat.cast_add_one, add_sub_cancel_right] at h
    push_cast
    linarith

/-- For `3 ≤ N` and every `M`, `∑_{N < n ≤ M} log n / n² ≤ (1 + log N) / N`. -/
theorem sum_Ioc_log_div_sq_le {N : ℕ} (hN : 3 ≤ N) (M : ℕ) :
    ∑ n ∈ Ioc N M, log n / (n : ℝ) ^ 2 ≤ (1 + log N) / N := by
  rcases le_or_gt N M with hNM | hMN
  · have h := sum_Ioc_log_div_sq_add_le hN hNM
    have : 0 ≤ (1 + log M) / M := by
      have : 0 ≤ log M := log_natCast_nonneg M
      positivity
    linarith
  · rw [Ioc_eq_empty_of_le hMN.le, sum_empty]
    have : 0 ≤ log N := log_natCast_nonneg N
    positivity

private theorem sum_range_log_div_sq_of_lt_le {N : ℕ} (hN : 3 ≤ N) (K : ℕ) :
    ∑ n ∈ range K, (if N < n then log n / (n : ℝ) ^ 2 else 0) ≤ (1 + log N) / N := by
  rw [← sum_filter]
  refine le_trans (sum_le_sum_of_subset_of_nonneg (fun n hn ↦ ?_) fun n _ _ ↦ ?_)
    (sum_Ioc_log_div_sq_le hN K)
  · simp only [mem_filter, mem_range] at hn
    exact mem_Ioc.mpr ⟨hn.2, hn.1.le⟩
  · have : 0 ≤ log n := log_natCast_nonneg n
    positivity

/-- The series `∑_{n > N} log n / n²` converges. -/
theorem summable_log_div_sq_of_lt (N : ℕ) :
    Summable fun n : ℕ ↦ if N < n then log n / (n : ℝ) ^ 2 else 0 := by
  -- The tail beyond `3` is controlled by the telescoping bound, and it agrees with the tail
  -- beyond `N` from `N + 4` on.
  have h3 : Summable fun n : ℕ ↦ if 3 < n then log n / (n : ℝ) ^ 2 else 0 := by
    refine summable_of_sum_range_le (fun n ↦ ?_) (sum_range_log_div_sq_of_lt_le le_rfl)
    have : 0 ≤ log n := log_natCast_nonneg n
    split_ifs <;> positivity
  refine (summable_nat_add_iff (N + 4)).mp (((summable_nat_add_iff (N + 4)).mpr h3).congr
    fun n ↦ ?_)
  simp [show N < n + (N + 4) by omega, show 3 < n + (N + 4) by omega]

/-- For `3 ≤ N`, `∑_{n > N} log n / n² ≤ (1 + log N) / N`. -/
theorem tsum_log_div_sq_of_lt_le {N : ℕ} (hN : 3 ≤ N) :
    ∑' n : ℕ, (if N < n then log n / (n : ℝ) ^ 2 else 0) ≤ (1 + log N) / N := by
  refine tsum_le_of_sum_range_le (fun n ↦ ?_) (sum_range_log_div_sq_of_lt_le hN)
  have : 0 ≤ log n := log_natCast_nonneg n
  split_ifs <;> positivity

end Real
