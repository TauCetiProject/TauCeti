/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Products of consecutive integers

Over `ℤ` the product `t * (t - 1)` of two consecutive integers is nonnegative, because no integer
lies strictly between `t - 1` and `t`. This is a genuinely integral statement: over `ℝ` it already
fails at `t = 1 / 2`, and over `ℕ` it is vacuous.

The unit-shifted form `0 ≤ s * (s - δ)` for `δ : ℤˣ` follows by rescaling, since the only units of
`ℤ` are `±1` and multiplying by one of them permutes the pair.

The same product is always even, so every integer satisfies `c ^ 2 ≡ c` modulo `2`, and the
halved product `n * (n - 1) / 2` is an exact quotient. It satisfies the addition law
`T(n + k) = T(n) + T(k) + n k` and the reflection `T(1 - n) = T(n)`.

## Main results

* `Int.zero_le_mul_sub_one` : `0 ≤ t * (t - 1)`.
* `Int.zero_le_mul_sub_units` : `0 ≤ s * (s - δ)` for a unit `δ`.
* `Int.two_dvd_sq_sub_self` : `2 ∣ c ^ 2 - c`.
* `Int.add_mul_add_sub_one_ediv_two` : the addition law for `n * (n - 1) / 2`.
* `Int.one_sub_mul_one_sub_sub_one_ediv_two` : the reflection `n ↦ 1 - n` fixes `n * (n - 1) / 2`.
-/

public section

namespace Int

/-- Two consecutive integers have nonnegative product: no integer lies strictly between `t - 1`
and `t`. -/
theorem zero_le_mul_sub_one (t : ℤ) : 0 ≤ t * (t - 1) := by
  rcases le_or_gt t 0 with ht | ht
  · nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -t) (by omega : (0 : ℤ) ≤ 1 - t)]
  · exact mul_nonneg (by omega) (by omega)

/-- The exceptional term of a unit exceptional value is nonnegative: rescaling by the unit turns
`s * (s - δ)` into a product of consecutive integers. Nonnegativity fails for the other odd
exceptional values, where already `1 * (1 - ε) < 0` for `ε ≥ 3`. -/
theorem zero_le_mul_sub_units (δ : ℤˣ) (s : ℤ) : 0 ≤ s * (s - (δ : ℤ)) := by
  have hδ : (δ : ℤ) * (δ : ℤ) = 1 := by
    rcases Int.units_eq_one_or δ with rfl | rfl <;> norm_num
  have hEq : ((δ : ℤ) * s) * ((δ : ℤ) * s - 1) = s * (s - (δ : ℤ)) := by
    linear_combination (s * s) * hδ
  rw [← hEq]
  exact zero_le_mul_sub_one _

/-- Every integer satisfies `c ^ 2 ≡ c` modulo `2`, since `c * (c - 1)` is even. -/
theorem two_dvd_sq_sub_self (c : ℤ) : (2 : ℤ) ∣ c ^ 2 - c := by
  rw [sq, ← mul_sub_one]
  exact (even_mul_pred_self c).two_dvd

/-- The addition law for the halved product of consecutive integers:
`T(n + k) = T(n) + T(k) + n k` for `T(m) = m (m - 1) / 2`. -/
theorem add_mul_add_sub_one_ediv_two (n k : ℤ) :
    (n + k) * (n + k - 1) / 2 = n * (n - 1) / 2 + k * (k - 1) / 2 + n * k := by
  have h (m : ℤ) : 2 * (m * (m - 1) / 2) = m * (m - 1) :=
    two_mul_ediv_two_of_even (even_mul_pred_self m)
  refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
  rw [mul_add, mul_add, h, h, h]
  ring

/-- The reflection `n ↦ 1 - n` fixes the halved product `n (n - 1) / 2` of consecutive
integers. -/
theorem one_sub_mul_one_sub_sub_one_ediv_two (n : ℤ) :
    (1 - n) * (1 - n - 1) / 2 = n * (n - 1) / 2 := by
  congr 1
  ring

end Int
