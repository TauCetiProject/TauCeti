/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Int.Basic
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
`T(n + k) = T(n) + T(k) + n k` and the reflection `T(1 - n) = T(n)`, and on natural numbers it is
the binomial coefficient `n.choose 2`. Likewise `3 ∣ c * (c ^ 2 - 1)` for every integer `c`,
combining with `8 ∣ c ^ 2 - 1` for odd `c` to give `24 ∣ c * (c ^ 2 - 1)` (and `24 ∣ c ^ 2 - 1`
when `c` is coprime to `6`).

## Main results

* `Int.zero_le_mul_sub_one` : `0 ≤ t * (t - 1)`.
* `Int.zero_le_mul_sub_units` : `0 ≤ s * (s - δ)` for a unit `δ`.
* `Int.two_dvd_sq_sub_self` : `2 ∣ c ^ 2 - c`.
* `Int.three_dvd_mul_sq_sub_one` : `3 ∣ c * (c ^ 2 - 1)`.
* `Int.twentyFour_dvd_mul_sq_sub_one_of_odd` : `24 ∣ c * (c ^ 2 - 1)` for odd `c`.
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

/-- Every integer satisfies `3 ∣ c * (c ^ 2 - 1)` (`c ^ 3 ≡ c` modulo `3`). -/
theorem three_dvd_mul_sq_sub_one (c : ℤ) : (3 : ℤ) ∣ c * (c ^ 2 - 1) := by
  simpa [mul_sub, ← pow_succ'] using prime_dvd_pow_self_sub Nat.prime_three c

/-- For an odd integer `c`, `24 ∣ c * (c ^ 2 - 1)`. -/
theorem twentyFour_dvd_mul_sq_sub_one_of_odd {c : ℤ} (hc : Odd c) :
    (24 : ℤ) ∣ c * (c ^ 2 - 1) :=
  IsCoprime.mul_dvd (by decide : IsCoprime (8 : ℤ) 3)
    (dvd_mul_of_dvd_right (eight_dvd_sq_sub_one_of_odd hc))
    (three_dvd_mul_sq_sub_one c)

/-- For an integer `c` coprime to `6`, `24 ∣ c ^ 2 - 1`. -/
theorem twentyFour_dvd_sq_sub_one_of_isCoprime_six {c : ℤ} (hc : IsCoprime c 6) :
    (24 : ℤ) ∣ c ^ 2 - 1 := by
  have hc' : IsCoprime c (2 * 3) := hc
  have hodd : Odd c := isCoprime_two_right.mp hc'.of_mul_right_left
  have h3 : (3 : ℤ) ∣ c ^ 2 - 1 := prime_dvd_pow_sub_one Nat.prime_three hc'.of_mul_right_right
  exact IsCoprime.mul_dvd (by decide : IsCoprime (8 : ℤ) 3) (eight_dvd_sq_sub_one_of_odd hodd) h3

/-- The halved product `m (m - 1) / 2` of consecutive integers is an exact quotient. -/
theorem two_mul_mul_sub_one_ediv_two (m : ℤ) : 2 * (m * (m - 1) / 2) = m * (m - 1) :=
  two_mul_ediv_two_of_even (even_mul_pred_self m)

/-- The addition law for the halved product of consecutive integers:
`T(n + k) = T(n) + T(k) + n k` for `T(m) = m (m - 1) / 2`. -/
theorem add_mul_add_sub_one_ediv_two (n k : ℤ) :
    (n + k) * (n + k - 1) / 2 = n * (n - 1) / 2 + k * (k - 1) / 2 + n * k := by
  have h := two_mul_mul_sub_one_ediv_two
  refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
  rw [mul_add, mul_add, h, h, h]
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
  have h := two_mul_mul_sub_one_ediv_two n
  have h' : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  rcases n with _ | n
  · simp
  · have h'' : (2 : ℤ) * ((n + 1).choose 2 : ℕ) = ((n : ℤ) + 1) * n := by
      exact_mod_cast h'
    push_cast at h ⊢
    linarith

end Int
