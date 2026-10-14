/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Defs

import Mathlib.Data.Int.GCD
import Mathlib.Tactic.LinearCombination

/-!
# A primitive common denominator of two rationals

For rationals `x` and `y` there is an integer `a` clearing both denominators, `a x = b` and
`a y = c` with `b, c ∈ ℤ`, such that the triple `(a, b, c)` is primitive: some integer
combination of `a`, `b` and `c` equals `1`. Applied to the coefficients of a monic rational
quadratic `t² = x t + y`, it rescales the relation to a primitive integral one
`a t² - b t - c = 0`, which is how primitive quadratic equations of irrational numbers enter the
theory of lattices in quadratic fields (D. A. Cox, *Primes of the Form x² + ny²*, §7).

The integer `a` is the common denominator `x.den * y.den` divided by the greatest common divisor
of the three resulting integers.
-/

public section

namespace Rat

/-- **A primitive common denominator.** For rationals `x` and `y` there are integers `a`, `b`, `c`
with `a x = b` and `a y = c` such that `a`, `b` and `c` generate the unit ideal of `ℤ`. -/
theorem exists_primitive_common_denominator (x y : ℚ) :
    ∃ a b c : ℤ, (a : ℚ) * x = b ∧ (a : ℚ) * y = c ∧ ∃ u v w : ℤ, u * a + v * b + w * c = 1 := by
  -- Clear the denominators naively, then divide out the common factor `g`.
  set D : ℤ := x.den * y.den
  set B : ℤ := x.num * y.den
  set C : ℤ := y.num * x.den
  have hDx : (D : ℚ) * x = B := by
    simp only [D, B, Int.cast_mul, Int.cast_natCast]
    linear_combination (y.den : ℚ) * x.mul_den_eq_num
  have hDy : (D : ℚ) * y = C := by
    simp only [D, C, Int.cast_mul, Int.cast_natCast]
    linear_combination (x.den : ℚ) * y.mul_den_eq_num
  set g : ℤ := ((Int.gcd D (Int.gcd B C) : ℕ) : ℤ)
  have hg : g ≠ 0 := by
    have hD : D ≠ 0 := mul_ne_zero (by simp) (by simp)
    simp only [g, ne_eq, Nat.cast_eq_zero, Int.gcd_eq_zero_iff]
    exact fun h ↦ hD h.1
  obtain ⟨a, ha⟩ : g ∣ D := Int.gcd_dvd_left ..
  obtain ⟨b, hb⟩ : g ∣ B := (Int.gcd_dvd_right ..).trans (Int.gcd_dvd_left ..)
  obtain ⟨c, hc⟩ : g ∣ C := (Int.gcd_dvd_right ..).trans (Int.gcd_dvd_right ..)
  have hgq : (g : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hg
  refine ⟨a, b, c, ?_, ?_, Int.gcdA D (Int.gcd B C), Int.gcdB D (Int.gcd B C) * Int.gcdA B C,
    Int.gcdB D (Int.gcd B C) * Int.gcdB B C, ?_⟩
  · refine mul_left_cancel₀ hgq ?_
    rw [← mul_assoc, ← Int.cast_mul, ← ha, hDx, hb, Int.cast_mul]
  · refine mul_left_cancel₀ hgq ?_
    rw [← mul_assoc, ← Int.cast_mul, ← ha, hDy, hc, Int.cast_mul]
  · -- Bézout for `g = gcd D (gcd B C)`, divided by `g`.
    have h₁ := Int.gcd_eq_gcd_ab D (Int.gcd B C)
    have h₂ := Int.gcd_eq_gcd_ab B C
    refine mul_left_cancel₀ hg ?_
    linear_combination (-Int.gcdA D (Int.gcd B C)) * ha
      + (-Int.gcdB D (Int.gcd B C) * Int.gcdA B C) * hb
      + (-Int.gcdB D (Int.gcd B C) * Int.gcdB B C) * hc + (-Int.gcdB D (Int.gcd B C)) * h₂ - h₁

end Rat
