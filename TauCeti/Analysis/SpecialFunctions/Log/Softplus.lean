/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exponential-sum reformulation of the softplus epigraph

The scalar softplus epigraph inequality `log (1 + exp x) ≤ t` is equivalent to the shifted
exponential-sum bound `exp (x - t) + exp (-t) ≤ 1`. Multiplying `1 + exp x ≤ exp t` by the
positive factor `exp (-t)` gives an equivalent convex inequality in two exponential terms, which
directly feeds the two-cone representation of softplus and its positive-scale perspective.

## Main results

* `Real.log_one_add_exp_le_iff`: `log (1 + exp x) ≤ t ↔ exp (x - t) + exp (-t) ≤ 1`.
-/

public section

namespace Real

/-- The softplus epigraph inequality `log (1 + exp x) ≤ t` is equivalent to the shifted
exponential-sum bound `exp (x - t) + exp (-t) ≤ 1`. -/
theorem log_one_add_exp_le_iff {x t : ℝ} :
    log (1 + exp x) ≤ t ↔ exp (x - t) + exp (-t) ≤ 1 := by
  have hdiv : exp (x - t) + exp (-t) = (1 + exp x) / exp t := by
    simp [exp_sub, exp_neg, add_div, add_comm]
  rw [log_le_iff_le_exp (add_pos zero_lt_one (exp_pos x)), hdiv, div_le_one (exp_pos t)]

end Real
