/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import TauCeti.Data.ZMod.Divisibility

/-!
# Parity and vanishing of the characters `χ₄` and `χ₈`

This file adds to Mathlib's `ZMod.χ₄` and `ZMod.χ₈` the facts that `χ₄` is odd and `χ₈` is even,
in the form used under reflection `b ↦ b'` with `n ∣ b + b'`, together with `χ₄ a ^ 2 = 1` for odd
`a`, the normalization `a * χ₄ a ≡ 1 (mod 4)` for odd integers, and the description of the
zeros of `χ₈`.

## Main statements

* `ZMod.χ₄_neg`, `ZMod.χ₈_neg`: `χ₄` is odd and `χ₈` is even.
* `ZMod.χ₄_natCast_eq_neg_of_dvd_add`, `ZMod.χ₈_natCast_eq_of_dvd_add`: the same statements for
  natural numbers `b`, `b'` with `4 ∣ b + b'`, respectively `8 ∣ b + b'`.
* `ZMod.int_mul_χ₄_modEq_one`: sign-normalizing an odd integer gives `1` modulo `4`.
* `ZMod.χ₈_intCast_eq_zero_iff`: `χ₈ a = 0` exactly when `a` is even.
-/

public section

namespace ZMod

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

/-- Multiplying an odd integer by its `χ₄` value gives its unique sign choice congruent to
`1` modulo `4`. -/
theorem int_mul_χ₄_modEq_one {m : ℤ} (hm : Odd m) : m * χ₄ m ≡ 1 [ZMOD 4] := by
  have hm2 := Int.odd_iff.mp hm
  rw [χ₄_int_eq_if_mod_four, ite_eq_right (by omega)]
  split_ifs with h
  · simpa [Int.ModEq] using h
  · simp only [mul_neg_one, Int.ModEq]
    omega

/-- The character `χ₈` vanishes exactly at the even integers. -/
theorem χ₈_intCast_eq_zero_iff (a : ℤ) : χ₈ a = 0 ↔ 2 ∣ a := by
  rw [χ₈_int_eq_if_mod_eight, Int.dvd_iff_emod_eq_zero]
  split_ifs <;> simp_all

end ZMod
