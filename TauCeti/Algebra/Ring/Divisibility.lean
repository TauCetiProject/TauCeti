/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.Algebra.Ring.Divisibility.Basic

/-!
# Divisibility up to a unit and a multiple of the divisor

In a commutative ring, whether `a` divides an element does not change when a multiple of `a` is
added to it and the result is multiplied by a unit. This combines `IsUnit.dvd_mul_left` with
`dvd_add_left`, in the shape produced by transformation formulas such as those of a change of
variables of a Weierstrass equation, where the new coefficient is a unit times the old one plus a
correction term.

## Main results

* `IsUnit.dvd_iff_of_eq_mul_add`: if `y = v * (x + a * z)` with `v` a unit, then `a ∣ y ↔ a ∣ x`.
-/

public section

variable {R : Type*} [CommRing R]

/-- Divisibility by `a` is unchanged by adding a multiple of `a` and multiplying by a unit: if
`y = v * (x + a * z)` with `v` a unit, then `a ∣ y ↔ a ∣ x`. -/
theorem IsUnit.dvd_iff_of_eq_mul_add {a x y v : R} (hv : IsUnit v) (z : R)
    (h : y = v * (x + a * z)) : a ∣ y ↔ a ∣ x := by
  rw [h, hv.dvd_mul_left, dvd_add_left (_root_.dvd_mul_right a z)]
