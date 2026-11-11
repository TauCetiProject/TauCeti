/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Wronskian

/-!
# Further properties of the Wronskian of two polynomials

This file adds four facts about Mathlib's Wronskian `W(a, b) = a b' - a' b` of two polynomials:
it commutes with coefficient ring maps, it is unchanged when a constant multiple of `a` is
subtracted from `b`, a root of multiplicity `n` of `b` is a root of multiplicity at least
`n - 1` of `W(a, b)`, and its coefficient in degree `deg a + deg b - 1` is
`(deg b - deg a) · leadingCoeff a · leadingCoeff b`.

The first three are the steps of Thue's argument that transport vanishing of a polynomial pair
at a point to its Wronskian.

## Main results

* `Polynomial.map_wronskian`: `W(a, b)` commutes with coefficient ring maps.
* `Polynomial.wronskian_sub_C_mul_right`: `W(a, b - c a) = W(a, b)` for a constant `c`.
* `Polynomial.pow_sub_one_dvd_wronskian_right`: if `q ^ n ∣ b`, then `q ^ (n - 1) ∣ W(a, b)`.
* `Polynomial.coeff_wronskian_natDegree_add_natDegree_sub_one`: the coefficient of `W(a, b)` in
  degree `deg a + deg b - 1` is `(deg b - deg a) · leadingCoeff a · leadingCoeff b`.
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

/-- The coefficient of the Wronskian `W(a, b) = a b' - a' b` in degree `deg a + deg b - 1` is
`(deg b - deg a) · leadingCoeff a · leadingCoeff b`: in that degree, `a b'` and `a' b` have
coefficients `deg b` and `deg a` times `leadingCoeff a · leadingCoeff b`. For example, if
`deg b = deg a + 1`, then the coefficient of `W(a, b)` in degree `2 deg a` is
`leadingCoeff a · leadingCoeff b`. -/
theorem coeff_wronskian_natDegree_add_natDegree_sub_one (a b : R[X]) :
    (wronskian a b).coeff (a.natDegree + b.natDegree - 1) =
      ((b.natDegree : R) - a.natDegree) * (a.leadingCoeff * b.leadingCoeff) := by
  -- The coefficient of `p q'` in degree `deg p + deg q - 1` is `deg q · lc p · lc q`.
  have key (p q : R[X]) : (p * derivative q).coeff (p.natDegree + q.natDegree - 1) =
      q.natDegree * (p.leadingCoeff * q.leadingCoeff) := by
    rcases hq : q.natDegree with _ | n
    · simp [derivative_of_natDegree_zero hq]
    · rw [Nat.add_succ_sub_one, coeff_mul_add_eq_of_natDegree_le le_rfl
        ((natDegree_derivative_le q).trans_eq (by omega)), coeff_derivative]
      simp only [leadingCoeff, hq, Nat.cast_add_one]
      ring
  rw [wronskian, coeff_sub, key, mul_comm (derivative a), add_comm a.natDegree, key]
  ring

end Polynomial
