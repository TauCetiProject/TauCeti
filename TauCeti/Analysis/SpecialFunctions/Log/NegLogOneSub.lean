/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The sharp upper bound for `-log (1 - x) - x`

For `|x| < 1` the quantity `-log (1 - x) - x` is the tail `∑_{k ≥ 2} x ^ k / k` of the
logarithmic series. This file bounds it above by `x ^ 2 / (2 * (1 - x))` on `0 ≤ x < 1`.

Mathlib bounds the same tail over the reals in `Real.abs_log_sub_add_sum_range_le`, whose case
`n = 1` reads `|x + log (1 - x)| ≤ x ^ 2 / (1 - |x|)`. That is the same shape with `1` in place
of `2` in the denominator, so it loses a factor of two. The sharp constant is available in
Mathlib only over `ℂ`, as `Complex.norm_log_one_sub_inv_sub_self_le`; the bound here is that
complex estimate read along the real axis, using `log (1 - x)⁻¹ = -log (1 - x)`.

Stating it is therefore not a wrapper: the weaker form needs no name, being already a Mathlib
lemma, and the sharp form has no real-variable statement to wrap.

## Main results

* `Real.neg_log_one_sub_sub_self_le` — `-log (1 - x) - x ≤ x ^ 2 / (2 * (1 - x))` for
  `0 ≤ x < 1`.
-/

public section

namespace Real

/-- **The tail `-log (1 - x) - x` is at most `x ^ 2 / (2 * (1 - x))` on `[0, 1)`.** The constant
is sharp: the two sides agree to second order at `x = 0`. -/
theorem neg_log_one_sub_sub_self_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) - x ≤ x ^ 2 / (2 * (1 - x)) := by
  -- Drop from the norm to the value itself, after reading the complex estimate along the reals.
  have hz : ‖(x : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg hx0]
  have key := Complex.norm_log_one_sub_inv_sub_self_le hz
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv,
    ← Complex.ofReal_log (by positivity), ← Complex.ofReal_sub, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hx0, Real.log_inv] at key
  exact ((Real.le_norm_self _).trans key).trans_eq <| by field_simp

end Real
