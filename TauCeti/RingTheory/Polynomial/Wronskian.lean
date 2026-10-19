/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Wronskian

/-!
# Further properties of the Wronskian of two polynomials

This file adds three facts about Mathlib's Wronskian `W(a, b) = a b' - a' b` of two polynomials:
it commutes with coefficient ring maps, it is unchanged when a constant multiple of `a` is
subtracted from `b`, and a root of multiplicity `n` of `b` is a root of multiplicity at least
`n - 1` of `W(a, b)`.

These are the steps of Thue's argument that transport vanishing of a polynomial pair at a point
to its Wronskian.

## Main results

* `Polynomial.map_wronskian`: `W(a, b)` commutes with coefficient ring maps.
* `Polynomial.wronskian_sub_C_mul_right`: `W(a, b - c a) = W(a, b)` for a constant `c`.
* `Polynomial.pow_sub_one_dvd_wronskian_right`: if `q ^ n ∣ b`, then `q ^ (n - 1) ∣ W(a, b)`.
-/

public section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The Wronskian commutes with coefficient ring maps. -/
@[simp]
theorem map_wronskian (f : R →+* S) (a b : R[X]) :
    (wronskian a b).map f = wronskian (a.map f) (b.map f) := by
  simp only [wronskian, Polynomial.map_sub, Polynomial.map_mul, derivative_map]

/-- The Wronskian `W(a, b)` does not change when a constant multiple of `a` is subtracted
from `b`. -/
@[simp]
theorem wronskian_sub_C_mul_right (a b : R[X]) (c : R) :
    wronskian a (b - C c * a) = wronskian a b := by
  simp only [wronskian, derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

/-- If `q ^ n` divides `b`, then `q ^ (n - 1)` divides the Wronskian `W(a, b)`. -/
theorem pow_sub_one_dvd_wronskian_right {a b q : R[X]} {n : ℕ} (h : q ^ n ∣ b) :
    q ^ (n - 1) ∣ wronskian a b :=
  dvd_sub (dvd_mul_of_dvd_right (pow_sub_one_dvd_derivative_of_pow_dvd h) _)
    (dvd_mul_of_dvd_right ((pow_dvd_pow q (Nat.sub_le n 1)).trans h) _)

end Polynomial
