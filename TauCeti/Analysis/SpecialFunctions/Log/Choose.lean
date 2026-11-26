/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# Logarithmic upper bound for binomial coefficients

We prove `Real.log_choose_le` (`log C(p, k) ≤ k * log (e * p / k)` for `k ≤ p`) from Mathlib's
`Real.sum_choose_le_exp_pow`.
-/

public section

namespace Real

/-- `log C(p, k) ≤ k * log (e * p / k)` for `k ≤ p` (needed so `0 < p.choose k`). -/
theorem log_choose_le {p k : ℕ} (hk : k ≤ p) :
    log (p.choose k) ≤ k * log (exp 1 * p / k) := by
  have hle : (p.choose k : ℝ) ≤ (exp 1 * p / k) ^ k := by
    simpa only [div_mul_eq_mul_div] using
      (Finset.single_le_sum (fun i _ ↦ Nat.cast_nonneg (p.choose i))
        (Finset.self_mem_range_succ k)).trans (sum_choose_le_exp_pow hk)
  exact (log_le_log (Nat.cast_pos.mpr (Nat.choose_pos hk)) hle).trans_eq (log_pow _ k)

end Real
