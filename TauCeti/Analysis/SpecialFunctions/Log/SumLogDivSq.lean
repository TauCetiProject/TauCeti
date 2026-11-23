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

The series `∑ log n / n²` converges, and for a natural number `N ≥ 1` its tail
`∑_{n > N} log n / n²` is at most `(1 + log N) / N`. The function `h(x) = (1 + log x) / x` is an
antiderivative of `-log x / x²`, and for `x ≥ 3` one step of the telescoping sum already dominates
the term: `log x / x² ≤ h(x - 1) - h(x)`. For `x ≥ 4` this uses
`log (x - 1) ≥ log x - 1 / (x - 1)` and `x ≤ (x - 1) log x`, the latter from
`log 4 = 2 log 2 ≥ 4 / 3`; the step at `x = 3` and the case `N = 1` use the numerical bounds on
`log 2` and `log 3`.

These bounds control `-Re (L'/L)(σ, χ) = ∑ Λ(n) Re χ(n) / n^σ` at `σ = 2` once the first few
terms are handled explicitly, since `Λ(n) ≤ log n`.

## Main results

* `Real.sum_Ioc_log_div_sq_add_le`: for `2 ≤ N ≤ M`,
  `∑_{N < n ≤ M} log n / n² + (1 + log M) / M ≤ (1 + log N) / N`.
* `Real.sum_Ioc_log_div_sq_le`: for `1 ≤ N` and every `M`,
  `∑_{N < n ≤ M} log n / n² ≤ (1 + log N) / N`.
* `Real.summable_log_div_sq`: the series `∑ log n / n²` converges.
* `Real.tsum_log_div_sq_of_lt_le`: for `1 ≤ N`, `∑_{n > N} log n / n² ≤ (1 + log N) / N`.
-/

public section

open Finset

namespace Real

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
  have hL : 4 / 3 ≤ log x := by
    have h4 := log_le_log (by norm_num) hx
    rw [log_four_eq] at h4
    linarith [log_two_gt_d9]
  -- `x ≤ (x - 1) log x` is the cross-multiplied form of the step.
  have hxL : x ≤ (x - 1) * log x := by nlinarith
  calc log x / x ^ 2 + (1 + log x) / x
      ≤ (1 + (log x - 1 / (x - 1))) / (x - 1) := by
        rw [div_add_div _ _ (by positivity) hx0.ne', div_le_div_iff₀ (by positivity) hx1]
        field_simp
        nlinarith
    _ ≤ (1 + log (x - 1)) / (x - 1) := by gcongr

/-- For `2 ≤ N ≤ M`, `∑_{N < n ≤ M} log n / n² + (1 + log M) / M ≤ (1 + log N) / N`. -/
theorem sum_Ioc_log_div_sq_add_le {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ∑ n ∈ Ioc N M, log n / (n : ℝ) ^ 2 + (1 + log M) / M ≤ (1 + log N) / N := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [sum_Ioc_succ_top hNM]
    have h : log ((M : ℝ) + 1) / ((M : ℝ) + 1) ^ 2 + (1 + log ((M : ℝ) + 1)) / ((M : ℝ) + 1) ≤
        (1 + log (M : ℝ)) / M := by
      rcases (show M = 2 ∨ 3 ≤ M by omega) with rfl | hM
      · norm_num
        linarith [log_two_gt_d9, log_three_lt_d9]
      · have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
        have h := log_div_sq_add_one_add_log_div_le (x := (M : ℝ) + 1) (by linarith)
        rwa [add_sub_cancel_right] at h
    push_cast at h ⊢
    linarith

/-- For `1 ≤ N` and every `M`, `∑_{N < n ≤ M} log n / n² ≤ (1 + log N) / N`. -/
theorem sum_Ioc_log_div_sq_le {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    ∑ n ∈ Ioc N M, log n / (n : ℝ) ^ 2 ≤ (1 + log N) / N := by
  have hnn (n : ℕ) : 0 ≤ log n / (n : ℝ) ^ 2 := by
    have : 0 ≤ log n := log_natCast_nonneg n
    positivity
  have hM (M : ℕ) : 0 ≤ (1 + log M) / M := by
    have : 0 ≤ log M := log_natCast_nonneg M
    positivity
  rcases (show N = 1 ∨ 2 ≤ N by omega) with rfl | hN
  · -- Enlarge the range to `Ioc 1 M'` with `M' ≥ 3`, then split off the terms `n = 2, 3`.
    obtain ⟨M', hMM', hM'⟩ : ∃ M', M ≤ M' ∧ 3 ≤ M' := ⟨max M 3, le_max_left _ _, le_max_right _ _⟩
    calc ∑ n ∈ Ioc 1 M, log n / (n : ℝ) ^ 2 ≤ ∑ n ∈ Ioc 1 M', log n / (n : ℝ) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right hMM')
            fun n _ _ ↦ hnn n
      _ = log 2 / 2 ^ 2 + log 3 / 3 ^ 2 + ∑ n ∈ Ioc 3 M', log n / (n : ℝ) ^ 2 := by
          rw [← sum_Ioc_consecutive _ (show 1 ≤ 3 by norm_num) hM',
            sum_Ioc_succ_top (show 1 ≤ 2 by norm_num), sum_Ioc_succ_top le_rfl]
          norm_num
      _ ≤ log 2 / 2 ^ 2 + log 3 / 3 ^ 2 + (1 + log 3) / 3 := by
          have h := sum_Ioc_log_div_sq_add_le (show 2 ≤ 3 by norm_num) hM'
          have := hM M'
          push_cast at h
          linarith
      _ ≤ (1 + log ((1 : ℕ) : ℝ)) / ((1 : ℕ) : ℝ) := by
          norm_num
          linarith [log_two_lt_d9, log_three_lt_d9]
  rcases le_or_gt N M with hNM | hMN
  · linarith [sum_Ioc_log_div_sq_add_le hN hNM, hM M]
  · rw [Ioc_eq_empty_of_le hMN.le, sum_empty]
    exact hM N

private theorem sum_range_log_div_sq_of_lt_le {N : ℕ} (hN : 1 ≤ N) (K : ℕ) :
    ∑ n ∈ range K, (if N < n then log n / (n : ℝ) ^ 2 else 0) ≤ (1 + log N) / N := by
  rw [← sum_filter]
  refine le_trans (sum_le_sum_of_subset_of_nonneg (fun n hn ↦ ?_) fun n _ _ ↦ ?_)
    (sum_Ioc_log_div_sq_le hN K)
  · simp only [mem_filter, mem_range] at hn
    exact mem_Ioc.mpr ⟨hn.2, hn.1.le⟩
  · have : 0 ≤ log n := log_natCast_nonneg n
    positivity

/-- The series `∑ log n / n²` converges. -/
theorem summable_log_div_sq : Summable fun n : ℕ ↦ log n / (n : ℝ) ^ 2 := by
  -- The tail beyond `1` is controlled by the telescoping bound, and the term at `n = 1` is `0`.
  have h1 : Summable fun n : ℕ ↦ if 1 < n then log n / (n : ℝ) ^ 2 else 0 := by
    refine summable_of_sum_range_le (fun n ↦ ?_) (sum_range_log_div_sq_of_lt_le le_rfl)
    have : 0 ≤ log n := log_natCast_nonneg n
    split_ifs <;> positivity
  refine (summable_nat_add_iff 2).mp (((summable_nat_add_iff 2).mpr h1).congr fun n ↦ ?_)
  simp [show 1 < n + 2 by omega]

/-- For `1 ≤ N`, `∑_{n > N} log n / n² ≤ (1 + log N) / N`. -/
theorem tsum_log_div_sq_of_lt_le {N : ℕ} (hN : 1 ≤ N) :
    ∑' n : ℕ, (if N < n then log n / (n : ℝ) ^ 2 else 0) ≤ (1 + log N) / N := by
  refine tsum_le_of_sum_range_le (fun n ↦ ?_) (sum_range_log_div_sq_of_lt_le hN)
  have : 0 ≤ log n := log_natCast_nonneg n
  split_ifs <;> positivity

end Real
