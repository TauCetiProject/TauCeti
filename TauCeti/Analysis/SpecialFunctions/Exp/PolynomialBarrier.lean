/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A polynomial-exponential barrier dominates a bounded function

If `r ≤ Mu` and `n` is larger than `|Mu| / ε + 1`, then the barrier
`ε * (exp a * (1 + n ^ 2))` with `a ≥ 0` exceeds `r`.

## Main results

* `Real.sub_mul_exp_mul_neg_of_lt`: the strict inequality
  `r - ε * (exp a * (1 + n ^ 2)) < 0`.
-/

public section

namespace Real

/-- The barrier `ε * (exp a * (1 + n ^ 2))` dominates an upper bound `r ≤ Mu` once the
radius `n` exceeds `|Mu| / ε + 1`, for `a ≥ 0` and `ε > 0`. -/
theorem sub_mul_exp_mul_neg_of_lt {a ε Mu r n : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    (hr : r ≤ Mu) (hn : |Mu| / ε + 1 < n) :
    r - ε * (exp a * (1 + n ^ 2)) < 0 := by
  have h1 : 1 ≤ exp a := one_le_exp ha
  have h2 : |Mu| < ε * n := by
    rw [← div_lt_iff₀' hε]
    linarith
  have h3 : n ≤ n ^ 2 := by
    have : 0 ≤ |Mu| / ε := by positivity
    nlinarith
  have h4 : ε * (1 + n ^ 2) ≤ ε * (exp a * (1 + n ^ 2)) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) h1) hε.le
  nlinarith [le_abs_self Mu]

end Real
