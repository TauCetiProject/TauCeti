/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Lemmas

import Mathlib.Data.Int.Cast.Lemmas

/-!
# Numerator and denominator of a rational multiplier between integers

If `a' = r * a` with `a, a' ∈ ℤ` and `r ∈ ℚ`, then the denominator of `r` divides `a` and the
numerator of `r` divides `a'`. This is Mathlib's `Rat.den_dvd` and `Rat.num_dvd` for the fraction
`a' /. a`, restated for a rational `r` given by the relation it satisfies rather than as an
explicit quotient, so that it applies with no case split on `a = 0` at the point of use. It is
what turns a rational scaling between two integral objects into integer divisibilities, as for
the scaling `(A, B) ↦ (r⁴A, r⁶B)` between two integral short Weierstrass equations.

## Main results

* `Rat.den_dvd_of_intCast_eq_mul_intCast`: `a' = r * a` implies `r.den ∣ a`.
* `Rat.num_dvd_of_intCast_eq_mul_intCast`: `a' = r * a` implies `r.num ∣ a'`.
-/

public section

namespace Rat

variable {a a' : ℤ} {r : ℚ}

/-- A rational `r` with `a' = r * a` for integers `a ≠ 0` and `a'` is the fraction `a' /. a`. -/
private theorem eq_divInt_of_intCast_eq_mul_intCast (h : (a' : ℚ) = r * a) (ha : a ≠ 0) :
    r = divInt a' a := by
  rw [divInt_eq_div, eq_div_iff (Int.cast_ne_zero.mpr ha)]
  exact h.symm

/-- **The denominator of a rational multiplier between integers divides the multiplicand**: if
`a' = r * a` with `a, a'` integers, then `r.den ∣ a`. -/
theorem den_dvd_of_intCast_eq_mul_intCast (h : (a' : ℚ) = r * a) : (r.den : ℤ) ∣ a := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact dvd_zero _
  · rw [eq_divInt_of_intCast_eq_mul_intCast h ha]
    exact den_dvd a' a

/-- **The numerator of a rational multiplier between integers divides the result**: if
`a' = r * a` with `a, a'` integers, then `r.num ∣ a'`. -/
theorem num_dvd_of_intCast_eq_mul_intCast (h : (a' : ℚ) = r * a) : r.num ∣ a' := by
  rcases eq_or_ne a 0 with rfl | ha
  · have : a' = 0 := by simpa using h
    simp [this]
  · rw [eq_divInt_of_intCast_eq_mul_intCast h ha]
    exact num_dvd a' ha

end Rat

end
