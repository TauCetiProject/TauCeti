/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The exponential series without its constant term

Mathlib's `NormedSpace.expSeries_div_hasSum_exp` expands `exp z` as `∑ₙ z ^ n / n!`. Dropping the
constant term `1` gives the series of `exp z - 1`, re-indexed from `0`, which is the form a power
series without constant term takes: `exp z - 1 = ∑ₙ z ^ (n + 1) / (n + 1)!`.

## Main results

* `Complex.hasSum_exp_sub_one`: `exp z - 1 = ∑ₙ z ^ (n + 1) / (n + 1)!` for every complex `z`.
-/

public section

open scoped Nat

namespace Complex

/-- The exponential series without its constant term: `exp z - 1 = ∑ₙ z ^ (n + 1) / (n + 1)!`. -/
theorem hasSum_exp_sub_one (z : ℂ) :
    HasSum (fun n : ℕ ↦ (((n + 1)! : ℂ))⁻¹ * z ^ (n + 1)) (exp z - 1) := by
  have h := (hasSum_nat_add_iff' 1).2 (NormedSpace.expSeries_div_hasSum_exp z)
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, ← exp_eq_exp_ℂ] at h
  simpa only [div_eq_inv_mul] using h

end Complex
