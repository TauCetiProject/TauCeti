/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic linearization of a positively scaled exponential inequality

For `a > 0`, an upper bound `a * exp s ≤ R` forces `0 < R` and is equivalent to
`0 < R ∧ log a + s ≤ log R`. Retaining the strict positivity conjunct is essential because
Mathlib's `Real.log` is extended to nonpositive inputs by `log 0 = 0`, whereas `a * exp s > 0`
excludes every `R ≤ 0`.

## Main results

* `Real.mul_exp_le_iff_log_add_le_log`: for `0 < a`,
  `a * exp s ≤ R ↔ 0 < R ∧ log a + s ≤ log R`.
-/

public section

namespace Real

/-- For `a > 0`, a scaled exponential bound `a * exp s ≤ R` is equivalent to `0 < R` together
with the linearized logarithmic inequality `log a + s ≤ log R`. The positivity conjunct cannot
be omitted because `a * exp s > 0` while `Real.log` is totalized at nonpositive arguments. -/
theorem mul_exp_le_iff_log_add_le_log {a s R : ℝ} (ha : 0 < a) :
    a * exp s ≤ R ↔ 0 < R ∧ log a + s ≤ log R := by
  have heq : exp (log a + s) = a * exp s := by
    rw [exp_add, exp_log ha]
  constructor
  · intro h
    have hR : 0 < R := lt_of_lt_of_le (mul_pos ha (exp_pos s)) h
    exact ⟨hR, (le_log_iff_exp_le hR).mpr (heq.trans_le h)⟩
  · rintro ⟨hR, h⟩
    exact heq.symm.trans_le ((le_log_iff_exp_le hR).mp h)

end Real
