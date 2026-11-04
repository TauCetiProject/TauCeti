/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.List.Prime
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Digits of `j + b * y` and factorials of digits

For a digit `j < b`, the base-`b` digits of `j + b * y` are `j` followed by the digits of `y`.
This gives the digit sum and the products over the digits of `j + b * y` in terms of those of
`y`. The product of the factorials of the base-`p` digits of `n` is prime to `p`, since every
digit is less than `p`. These facts index the digit induction in Stickelberger's congruence.

## Main results

* `Nat.sum_digits_add_mul`: the digit sum of `j + b * y` is `j` plus the digit sum of `y`.
* `Nat.prod_map_digits_add_mul`: `∏ g(dᵢ)` over the digits of `j + b * y` is `g j` times the
  product over the digits of `y`, whenever `g 0 = 1`.
* `Nat.Prime.not_dvd_prod_factorial_digits`: `p` does not divide the product of the factorials of
  the base-`p` digits of `n`.
-/

public section

namespace Nat

/-- The digit sum of `j + b * y`, for a digit `j < b`, is `j` plus the digit sum of `y`. -/
theorem sum_digits_add_mul {b j : ℕ} (hj : j < b) (y : ℕ) :
    (digits b (j + b * y)).sum = j + (digits b y).sum := by
  obtain _ | _ | b := b
  · omega
  · obtain rfl : j = 0 := by omega
    simp
  rcases eq_or_ne j 0 with rfl | hj0
  · rcases eq_or_ne y 0 with rfl | hy0
    · simp
    rw [digits_add _ (by omega) 0 y hj (Or.inr hy0)]
    simp
  rw [digits_add _ (by omega) j y hj (Or.inl hj0)]
  simp

/-- The product of `g` over the digits of `j + b * y`, for a digit `j < b` and `g 0 = 1`, is
`g j` times the product of `g` over the digits of `y`. -/
theorem prod_map_digits_add_mul {M : Type*} [Monoid M] {g : ℕ → M} (hg : g 0 = 1) {b j : ℕ}
    (hj : j < b) (y : ℕ) :
    ((digits b (j + b * y)).map g).prod = g j * ((digits b y).map g).prod := by
  obtain _ | _ | b := b
  · omega
  · obtain rfl : j = 0 := by omega
    simp [hg]
  rcases eq_or_ne j 0 with rfl | hj0
  · rcases eq_or_ne y 0 with rfl | hy0
    · simp [hg]
    rw [digits_add _ (by omega) 0 y hj (Or.inr hy0)]
    simp
  rw [digits_add _ (by omega) j y hj (Or.inl hj0)]
  simp

/-- A prime `p` does not divide the product of the factorials of the base-`p` digits of `n`. -/
theorem Prime.not_dvd_prod_factorial_digits {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ¬p ∣ ((digits p n).map factorial).prod := by
  rw [hp.prime.dvd_prod_iff]
  rintro ⟨_, hm, hdvd⟩
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hm
  exact absurd (hp.dvd_factorial.1 hdvd) (not_le.2 (digits_lt_base hp.one_lt hd))

end Nat
