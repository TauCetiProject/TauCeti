/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Bringing a nonnegative number below a threshold by the time `log (1 + a / δ)`

For `δ > 0` and `a ≥ 0`, the factor `exp (-log (1 + a / δ)) = δ / (δ + a)` brings `a` strictly
below `δ`. So `T = log (1 + a / δ)` is a time `T ≥ 0`, continuous in `a`, with `e^{-T} a < δ`: the
canonical choice when a vector of norm `a` is to be brought into the ball of radius `δ` by a
contraction at unit exponential rate, such as the flow of a pseudo-gradient along a stable
subspace.

## Main results

* `Real.exp_neg_log_one_add_div_mul_lt`: `exp (-log (1 + a / δ)) * a < δ`.
-/

public section

namespace Real

/-- For `δ > 0` and `a ≥ 0`, the factor `exp (-log (1 + a / δ))` brings `a` strictly below `δ`. -/
theorem exp_neg_log_one_add_div_mul_lt {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) :
    exp (-log (1 + a / δ)) * a < δ := by
  have h1 : 0 < 1 + a / δ := by positivity
  rw [exp_neg, exp_log h1, inv_mul_lt_iff₀ h1, add_mul, one_mul, div_mul_cancel₀ _ hδ.ne']
  linarith

end Real
