/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Products of consecutive integers

Over `ℤ` the product `t * (t - 1)` of two consecutive integers is nonnegative, because no integer
lies strictly between `t - 1` and `t`. This is a genuinely integral statement: over `ℝ` it already
fails at `t = 1 / 2`, and over `ℕ` it is vacuous.

More generally `0 ≤ s * (s - δ)` for every integer `δ` with `|δ| ≤ 1`: the shifts `δ = 1` and
`δ = -1` give consecutive products, and `δ = 0` gives a square. The bound on `δ` is sharp.

The consecutive product `t * (t - 1)` is always even, so every integer satisfies `c ^ 2 ≡ c`
modulo `2`, and the halved product `n * (n - 1) / 2` is an exact quotient. It satisfies the
addition law `T(n + k) = T(n) + T(k) + n k` and the reflection `T(1 - n) = T(n)`, and on natural
numbers it is the binomial coefficient `n.choose 2`. Likewise `3 ∣ c * (c ^ 2 - 1)` for every
integer `c`, and `24 ∣ c ^ 2 - 1` when `c` is coprime to `6`.

## Main results

* `Int.zero_le_mul_sub_one` : `0 ≤ t * (t - 1)`.
* `Int.zero_le_mul_sub_of_abs_le_one` : `0 ≤ s * (s - δ)` whenever `|δ| ≤ 1`.
* `Int.two_dvd_sq_sub_self` : `2 ∣ c ^ 2 - c`.
* `Int.three_dvd_mul_sq_sub_one` : `3 ∣ c * (c ^ 2 - 1)`.
* `Int.twentyFour_dvd_sq_sub_one_of_isCoprime_six` : `24 ∣ c ^ 2 - 1` for `IsCoprime c 6`.
* `Int.two_mul_mul_sub_one_ediv_two` : `n * (n - 1) / 2` is an exact quotient.
* `Int.add_mul_add_sub_one_ediv_two` : the addition law for `n * (n - 1) / 2`.
* `Int.one_sub_mul_one_sub_sub_one_ediv_two` : the reflection `n ↦ 1 - n` fixes `n * (n - 1) / 2`.
* `Int.natCast_choose_two` : `n.choose 2 = n * (n - 1) / 2` for a natural number `n`.
-/

public section

namespace Int

/-- Two consecutive integers have nonnegative product: no integer lies strictly between `t - 1`
and `t`. -/
theorem zero_le_mul_sub_one (t : ℤ) : 0 ≤ t * (t - 1) := by
  rw [mul_sub_one, ← sq, sub_nonneg]
  exact le_self_sq t

/-- For an integer `δ` with `|δ| ≤ 1`, the product `s * (s - δ)` is nonnegative: it is a square
for `δ = 0` and a product of consecutive integers for `δ = ±1`. The bound is sharp: if
`2 ≤ |δ|`, then `s * (s - δ) = 1 - |δ| < 0` at `s = Int.sign δ`. -/
theorem zero_le_mul_sub_of_abs_le_one {δ : ℤ} (hδ : |δ| ≤ 1) (s : ℤ) : 0 ≤ s * (s - δ) := by
  rcases abs_le_one_iff.mp hδ with rfl | rfl | rfl
  · rw [sub_zero]
    exact mul_self_nonneg s
  · exact zero_le_mul_sub_one s
  · -- for `δ = -1`, `s * (s + 1)` is the consecutive product `-s * (-s - 1)`
    linear_combination zero_le_mul_sub_one (-s)

/-- Every integer satisfies `c ^ 2 ≡ c` modulo `2`, since `c * (c - 1)` is even. -/
theorem two_dvd_sq_sub_self (c : ℤ) : (2 : ℤ) ∣ c ^ 2 - c := by
  rw [sq, ← mul_sub_one]
  exact (even_mul_pred_self c).two_dvd

/-- Every integer satisfies `3 ∣ c * (c ^ 2 - 1)` (`c ^ 3 ≡ c` modulo `3`). -/
theorem three_dvd_mul_sq_sub_one (c : ℤ) : (3 : ℤ) ∣ c * (c ^ 2 - 1) := by
  simpa [mul_sub, ← pow_succ'] using prime_dvd_pow_self_sub Nat.prime_three c

/-- For an integer `c` coprime to `6`, `24 ∣ c ^ 2 - 1`. -/
theorem twentyFour_dvd_sq_sub_one_of_isCoprime_six {c : ℤ} (hc : IsCoprime c 6) :
    (24 : ℤ) ∣ c ^ 2 - 1 := by
  have hc' : IsCoprime c (2 * 3) := hc
  have hodd : Odd c := isCoprime_two_right.mp hc'.of_mul_right_left
  have h3 : (3 : ℤ) ∣ c ^ 2 - 1 := prime_dvd_pow_sub_one Nat.prime_three hc'.of_mul_right_right
  exact IsCoprime.mul_dvd (by decide : IsCoprime (8 : ℤ) 3) (eight_dvd_sq_sub_one_of_odd hodd) h3

/-- The halved product `m (m - 1) / 2` of consecutive integers is an exact quotient. -/
@[simp]
theorem two_mul_mul_sub_one_ediv_two (m : ℤ) : 2 * (m * (m - 1) / 2) = m * (m - 1) :=
  two_mul_ediv_two_of_even (even_mul_pred_self m)

/-- The addition law for the halved product of consecutive integers:
`T(n + k) = T(n) + T(k) + n k` for `T(m) = m (m - 1) / 2`. -/
theorem add_mul_add_sub_one_ediv_two (n k : ℤ) :
    (n + k) * (n + k - 1) / 2 = n * (n - 1) / 2 + k * (k - 1) / 2 + n * k := by
  refine mul_left_cancel₀ two_ne_zero ?_
  simp only [mul_add, two_mul_mul_sub_one_ediv_two]
  ring

/-- The reflection `n ↦ 1 - n` fixes the halved product `n (n - 1) / 2` of consecutive
integers. -/
theorem one_sub_mul_one_sub_sub_one_ediv_two (n : ℤ) :
    (1 - n) * (1 - n - 1) / 2 = n * (n - 1) / 2 := by
  congr 1
  ring

/-- On natural numbers the halved product `n (n - 1) / 2` is the binomial coefficient
`n.choose 2`. -/
theorem natCast_choose_two (n : ℕ) : ((n.choose 2 : ℕ) : ℤ) = n * ((n : ℤ) - 1) / 2 := by
  rcases n with _ | n
  · simp
  · rw [Nat.choose_two_right, Int.natCast_ediv]
    push_cast
    rw [add_sub_cancel_right]

end Int
