/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# Parity and vanishing of the characters `χ₄` and `χ₈`

This file adds to Mathlib's `ZMod.χ₄` and `ZMod.χ₈` the facts that `χ₄` is odd and `χ₈` is even,
in the form used under reflection `b ↦ b'` with `n ∣ b + b'`, together with `χ₄ a ^ 2 = 1` for odd
`a` and the description of the zeros of `χ₈`.

## Main statements

* `ZMod.χ₄_neg`, `ZMod.χ₈_neg`: `χ₄` is odd and `χ₈` is even.
* `ZMod.χ₄_natCast_eq_neg_of_dvd_add`, `ZMod.χ₈_natCast_eq_of_dvd_add`: the same statements for
  natural numbers `b`, `b'` with `4 ∣ b + b'`, respectively `8 ∣ b + b'`.
* `ZMod.χ₈_intCast_eq_zero_iff`: `χ₈ a = 0` exactly when `a` is even.
-/

public section

namespace ZMod

/-- If `n ∣ b + b'`, then `b' = -b` in `ZMod n`. -/
theorem natCast_eq_neg_of_dvd_add {n b b' : ℕ} (h : n ∣ b + b') : (b' : ZMod n) = -b := by
  rw [eq_neg_iff_add_eq_zero, add_comm, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
  exact h

/-- The character `χ₄` is odd. -/
theorem χ₄_neg (x : ZMod 4) : χ₄ (-x) = -χ₄ x := by
  revert x
  decide

/-- The character `χ₈` is even. -/
theorem χ₈_neg (x : ZMod 8) : χ₈ (-x) = χ₈ x := by
  revert x
  decide

/-- If `4 ∣ b + b'`, then `χ₄ b' = -χ₄ b`, since `χ₄` is odd. -/
theorem χ₄_natCast_eq_neg_of_dvd_add {b b' : ℕ} (h : 4 ∣ b + b') : χ₄ b' = -χ₄ b := by
  rw [natCast_eq_neg_of_dvd_add h, χ₄_neg]

/-- If `8 ∣ b + b'`, then `χ₈ b' = χ₈ b`, since `χ₈` is even. -/
theorem χ₈_natCast_eq_of_dvd_add {b b' : ℕ} (h : 8 ∣ b + b') : χ₈ b' = χ₈ b := by
  rw [natCast_eq_neg_of_dvd_add h, χ₈_neg]

/-- For odd `a`, `χ₄ a * χ₄ a = 1`. -/
theorem χ₄_natCast_mul_self {a : ℕ} (ha : Odd a) : χ₄ a * χ₄ a = 1 := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp ha) with h | h
  · rw [χ₄_nat_one_mod_four h, one_mul]
  · rw [χ₄_nat_three_mod_four h, neg_one_mul, neg_neg]

/-- The character `χ₈` vanishes exactly at the even integers. -/
theorem χ₈_intCast_eq_zero_iff (a : ℤ) : χ₈ a = 0 ↔ 2 ∣ a := by
  rw [χ₈_int_eq_if_mod_eight, Int.dvd_iff_emod_eq_zero]
  split_ifs <;> simp_all

end ZMod
