/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Monotonicity of `(1 + 1/n)ⁿ`

In a linearly ordered field the sequence `(1 + 1/n)ⁿ` is nondecreasing in `n`
(`TauCeti.monotone_one_add_inv_pow`); Mathlib's `Real.one_add_inv_pow_le_exp` bounds it above by
`e`. A lower bound at one index therefore holds at every larger index. For example, the ratio
`(π/4) (1 + 1/n)^{2n}` between consecutive terms of the Minkowski discriminant bound
`(π/4)ⁿ (nⁿ/n!)²` is at least its value at any smaller degree.

The step from `n` to `n + 1` is Bernoulli's inequality (`one_add_mul_le_pow`) applied to
`(1 + 1/(n+1)) / (1 + 1/n) = 1 - 1/(n+1)²`.
-/

public section

namespace TauCeti

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- The sequence `(1 + 1/n)ⁿ` is nondecreasing. At `n = 0` it takes the value `1`, since the
exponent is `0`. -/
theorem monotone_one_add_inv_pow : Monotone fun n : ℕ ↦ (1 + (n : α)⁻¹) ^ n := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  have hn0 : (n : α) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- The ratio of consecutive bases is `1 - 1/(n+1)²`; Bernoulli bounds its `(n+1)`-st power
  -- below by `1 - 1/(n+1) = 1 / (1 + 1/n)`.
  have hratio : 1 + ((n + 1 : ℕ) : α)⁻¹ = (1 + (n : α)⁻¹) * (1 + -((n + 1 : α) ^ 2)⁻¹) := by
    push_cast
    field_simp
    ring
  have hle : ((n + 1 : α) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hbern := one_add_mul_le_pow (a := -((n + 1 : α) ^ 2)⁻¹) (by linarith) (n + 1)
  have hfac : (1 + (n : α)⁻¹) * (1 + ((n + 1 : ℕ) : α) * -((n + 1 : α) ^ 2)⁻¹) = 1 := by
    push_cast
    field_simp
    ring
  calc (1 + (n : α)⁻¹) ^ n
      = (1 + (n : α)⁻¹) ^ n *
          ((1 + (n : α)⁻¹) * (1 + ((n + 1 : ℕ) : α) * -((n + 1 : α) ^ 2)⁻¹)) := by
        rw [hfac, mul_one]
    _ = (1 + (n : α)⁻¹) ^ (n + 1) * (1 + ((n + 1 : ℕ) : α) * -((n + 1 : α) ^ 2)⁻¹) := by
        ring
    _ ≤ (1 + (n : α)⁻¹) ^ (n + 1) * (1 + -((n + 1 : α) ^ 2)⁻¹) ^ (n + 1) := by
        gcongr
    _ = (1 + ((n + 1 : ℕ) : α)⁻¹) ^ (n + 1) := by rw [hratio, mul_pow]

end TauCeti
