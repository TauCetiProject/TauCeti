/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Sums of principal logarithms of numbers near `1`

Mathlib's `Complex.norm_log_one_add_half_le_self` bounds a single principal logarithm,
`‖log (1 + z)‖ ≤ 3/2 ‖z‖` for `‖z‖ ≤ 1/2`. Summed over a finite family `u` of complex numbers
with `‖uₖ - 1‖ ≤ 1/2`, it bounds `∑ₖ log uₖ`, a logarithm of `∏ₖ uₖ`, by `3/2 ∑ₖ ‖uₖ - 1‖`. This
is the estimate that places an `m`-th root `exp ((∑ₖ log uₖ) / m)` of such a product near `1`.

## Main results

* `Complex.norm_sum_log_le_sum_norm_sub_one`: if `‖uₖ - 1‖ ≤ 1/2` for `k ∈ s`, then
  `‖∑ k ∈ s, log uₖ‖ ≤ 3/2 ∑ k ∈ s, ‖uₖ - 1‖`.
-/

public section

open Finset

namespace Complex

/-- **The sum of the principal logarithms of numbers near `1`.** If `‖uₖ - 1‖ ≤ 1/2` for every
`k ∈ s`, then `‖∑ k ∈ s, log uₖ‖ ≤ 3/2 ∑ k ∈ s, ‖uₖ - 1‖`. This sums
`Complex.norm_log_one_add_half_le_self` over `s`. -/
theorem norm_sum_log_le_sum_norm_sub_one {ι : Type*} {s : Finset ι} {u : ι → ℂ}
    (hu : ∀ k ∈ s, ‖u k - 1‖ ≤ 1 / 2) :
    ‖∑ k ∈ s, log (u k)‖ ≤ 3 / 2 * ∑ k ∈ s, ‖u k - 1‖ := by
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun k hk ↦ ?_)
  simpa using norm_log_one_add_half_le_self (hu k hk)

end Complex
