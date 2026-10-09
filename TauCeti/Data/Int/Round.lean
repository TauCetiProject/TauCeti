/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor

/-!
# Nearest multiples of an integer

Every integer `t` lies within `μ / 2` of a multiple of a positive integer `μ`: take `c` to be a
nearest integer to `t / μ`. It is stated without division, as `2 · |t - c μ| ≤ μ`.

## Main results

* `Int.exists_two_mul_abs_sub_mul_le` : `∃ c, 2 * |t - c * μ| ≤ μ` for `0 < μ`.
-/

public section

namespace Int

/-- Every integer lies within `μ / 2` of a multiple of a positive integer `μ`. -/
theorem exists_two_mul_abs_sub_mul_le (t : ℤ) {μ : ℤ} (hμ : 0 < μ) :
    ∃ c : ℤ, 2 * |t - c * μ| ≤ μ := by
  set c := round ((t : ℚ) / μ)
  refine ⟨c, ?_⟩
  have hμ' : (0 : ℚ) < μ := by exact_mod_cast hμ
  have hr : |(t : ℚ) / μ - c| ≤ 1 / 2 := abs_sub_round _
  have hrel : ((t - c * μ : ℤ) : ℚ) = μ * ((t : ℚ) / μ - c) := by
    push_cast
    field_simp
  have hq : 2 * |((t - c * μ : ℤ) : ℚ)| ≤ μ := by
    rw [hrel, abs_mul, abs_of_pos hμ']
    nlinarith
  exact_mod_cast hq

end Int
