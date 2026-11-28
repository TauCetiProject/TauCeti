/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.CardIntervalMod

/-!
# Bounds for the integers of an interval with given residue

Mathlib's `Int.Ico_filter_modEq_card` counts the integers of `[a, b)` congruent to `v` modulo
`r > 0` exactly, as a difference of two ceilings. For estimates, the useful consequence is the
uniform bound `(b - a) / r + 1`, independent of the residue `v`: a box of side `L` in `ℤ^n`
contains at most `(L / r + 1) ^ n` points of any one residue class modulo `r`.

For the naturals of `(a, b]`, `Nat.abs_card_Ioc_filter_modEq_sub_div_lt` is the two-sided form:
the count differs from `(b - a) / r` by less than one. This is the remainder bound for a sieve
on an arithmetic progression.
-/

public section

open Finset

namespace Int

/-- An interval `[a, b)` of integers with `a ≤ b` contains at most `(b - a) / r + 1` integers
congruent to `v` modulo `r > 0`, whatever the residue `v`. -/
theorem card_Ico_filter_modEq_le {r : ℤ} (hr : 0 < r) {a b : ℤ} (hab : a ≤ b) (v : ℤ) :
    (#{x ∈ Ico a b | x ≡ v [ZMOD r]} : ℚ) ≤ (b - a) / r + 1 := by
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  have hcard : ((#{x ∈ Ico a b | x ≡ v [ZMOD r]} : ℤ) : ℚ) =
      ((max (⌈(b - v) / (r : ℚ)⌉ - ⌈(a - v) / (r : ℚ)⌉) 0 : ℤ) : ℚ) := by
    rw [Ico_filter_modEq_card _ _ hr]
  rw [Int.cast_natCast] at hcard
  rw [hcard, Int.cast_max, Int.cast_zero, max_le_iff]
  have hba : (0 : ℚ) ≤ (b - a) / r := div_nonneg (by exact_mod_cast sub_nonneg.mpr hab) hr'.le
  refine ⟨?_, by linarith⟩
  have h₁ := Int.ceil_lt_add_one ((b - v) / (r : ℚ))
  have h₂ := Int.le_ceil ((a - v) / (r : ℚ))
  have hsplit : ((b : ℚ) - a) / r = (b - v) / r - (a - v) / r := by ring
  push_cast
  linarith

end Int

namespace Nat

/-- An interval `(a, b]` of naturals with `a ≤ b` contains `(b - a) / r` integers congruent to `v`
modulo `r > 0`, up to an error of absolute value less than one, whatever the residue `v`. -/
theorem abs_card_Ioc_filter_modEq_sub_div_lt {r : ℕ} (hr : 0 < r) {a b : ℕ} (hab : a ≤ b)
    (v : ℕ) : |(#{x ∈ Ioc a b | x ≡ v [MOD r]} : ℚ) - ((b : ℚ) - a) / r| < 1 := by
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  have hcard : ((#{x ∈ Ioc a b | x ≡ v [MOD r]} : ℤ) : ℚ) =
      ((max (⌊((b : ℚ) - v) / r⌋ - ⌊((a : ℚ) - v) / r⌋) 0 : ℤ) : ℚ) := by
    rw [Nat.Ioc_filter_modEq_card _ _ hr]
  rw [Int.cast_natCast] at hcard
  have hba : (0 : ℚ) ≤ ((b : ℚ) - a) / r :=
    div_nonneg (sub_nonneg.2 (by exact_mod_cast hab)) hr'.le
  have h₁ := Int.floor_le (((b : ℚ) - v) / r)
  have h₂ := Int.lt_floor_add_one (((b : ℚ) - v) / r)
  have h₃ := Int.floor_le (((a : ℚ) - v) / r)
  have h₄ := Int.lt_floor_add_one (((a : ℚ) - v) / r)
  have hsplit : ((b : ℚ) - a) / r = ((b : ℚ) - v) / r - ((a : ℚ) - v) / r := by ring
  have hnonneg : (0 : ℤ) ≤ ⌊((b : ℚ) - v) / r⌋ - ⌊((a : ℚ) - v) / r⌋ := by
    have h : (-1 : ℚ) < ((⌊((b : ℚ) - v) / r⌋ - ⌊((a : ℚ) - v) / r⌋ : ℤ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast h
  rw [hcard, max_eq_left hnonneg, abs_lt]
  push_cast
  constructor <;> linarith

end Nat
