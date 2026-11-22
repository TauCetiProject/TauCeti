/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision
-- Non-public: `IsCoprime.wronskian_eq_zero_iff` in the proof of
-- `Polynomial.coeff_one_mul_coeff_zero_sub_ne_zero_of_isCoprime_of_max_natDegree_eq_one` only.
import Mathlib.RingTheory.Polynomial.Wronskian

/-!
# Coprime polynomials

Mathlib's `Polynomial.isCoprime_X_sub_C_of_isUnit_sub` says that `X - C a` and `X - C b` are
coprime when `a - b` is a unit. Substituting any polynomial `p` for `X` shows that `p - C a` and
`p - C b` are coprime as well (`Polynomial.isCoprime_sub_C_of_isUnit_sub`), for example the
binomials `X ^ n - C a` and `X ^ n - C b`.

Over a ring without zero divisors, if `p = a X + b` and `q = c X + d` are coprime polynomials with
`max p.natDegree q.natDegree = 1`, then the determinant `a d - b c` of their coefficient matrix is
nonzero (`Polynomial.coeff_one_mul_coeff_zero_sub_ne_zero_of_isCoprime_of_max_natDegree_eq_one`).
Over a field, this means that the coefficient matrix of a reduced non-constant rational function
`(a X + b) / (c X + d)` is invertible.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- If `a - b` is a unit, the translates `p - C a` and `p - C b` of a polynomial are coprime. -/
theorem isCoprime_sub_C_of_isUnit_sub (p : R[X]) {a b : R} (h : IsUnit (a - b)) :
    IsCoprime (p - C a) (p - C b) := by
  simpa using (isCoprime_X_sub_C_of_isUnit_sub h).map (aeval p).toRingHom

/-- Over a ring without zero divisors, if `p` and `q` are coprime and
`max p.natDegree q.natDegree = 1`, then `p.coeff 1 * q.coeff 0 - p.coeff 0 * q.coeff 1 ≠ 0`; for
`p = a X + b` and `q = c X + d` this is `a d - b c ≠ 0`. -/
theorem coeff_one_mul_coeff_zero_sub_ne_zero_of_isCoprime_of_max_natDegree_eq_one [NoZeroDivisors R]
    {p q : R[X]} (hpq : IsCoprime p q)
    (hmax : max p.natDegree q.natDegree = 1) :
    p.coeff 1 * q.coeff 0 - p.coeff 0 * q.coeff 1 ≠ 0 := by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one (le_of_max_le_left hmax.le)
  obtain ⟨c, d, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one (le_of_max_le_right hmax.le)
  -- the Wronskian `W(q, p) = q p' - q' p` is the constant `a d - b c`, and coprimality makes it
  -- vanish only when both derivatives `a` and `c` do
  have hw : wronskian (C c * X + C d) (C a * X + C b) = C (a * d - b * c) := by
    simp only [wronskian, derivative_add, derivative_C_mul_X, derivative_C, add_zero, map_sub,
      map_mul]
    ring
  intro hdet
  simp only [coeff_add, coeff_mul_X, coeff_C_zero, coeff_C_succ, add_zero, mul_coeff_zero,
    coeff_X_zero, mul_zero, zero_add] at hdet
  obtain ⟨hc, ha⟩ := hpq.symm.wronskian_eq_zero_iff.mp (by rw [hw, hdet, map_zero])
  simp only [derivative_add, derivative_C_mul_X, derivative_C, add_zero, C_eq_zero] at hc ha
  simp [ha, hc] at hmax

end Polynomial
