/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Coprimality of translates and equality from divisibility of polynomials

Mathlib's `Polynomial.isCoprime_X_sub_C_of_isUnit_sub` says that `X - C a` and `X - C b` are
coprime when `a - b` is a unit. Substituting any polynomial `p` for `X` shows that `p - C a` and
`p - C b` are coprime as well (`Polynomial.isCoprime_sub_C_of_isUnit_sub`), for example the
binomials `X ^ n - C a` and `X ^ n - C b`.

Over a commutative semiring, if a polynomial `p` with invertible leading and constant coefficients
divides `q`, with `q.natDegree ≤ p.natDegree` and `q.coeff 0 = p.coeff 0`, then `q = p`
(`Polynomial.eq_of_dvd_of_natDegree_le_of_coeff_zero`).
-/

public section

namespace Polynomial

/-- If `a - b` is a unit, the translates `p - C a` and `p - C b` of a polynomial are coprime. -/
theorem isCoprime_sub_C_of_isUnit_sub {R : Type*} [CommRing R] (p : R[X]) {a b : R}
    (h : IsUnit (a - b)) : IsCoprime (p - C a) (p - C b) := by
  simpa using (isCoprime_X_sub_C_of_isUnit_sub h).map (aeval p).toRingHom

/-- Over a commutative semiring, if `p` has invertible leading and constant coefficients, `p ∣ q`,
`q.natDegree ≤ p.natDegree`, and `q.coeff 0 = p.coeff 0`, then `q = p`. -/
theorem eq_of_dvd_of_natDegree_le_of_coeff_zero {R : Type*} [CommSemiring R] {p q : R[X]}
    (hp : IsUnit p.leadingCoeff) (hp0 : IsUnit (p.coeff 0)) (hdvd : p ∣ q)
    (hdeg : q.natDegree ≤ p.natDegree) (h0 : q.coeff 0 = p.coeff 0) : q = p := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim q p
  obtain ⟨k, rfl⟩ := hdvd
  have hk0 : k.coeff 0 = 1 :=
    hp0.mul_left_cancel (by simpa only [mul_coeff_zero, mul_one] using h0)
  have hk_ne : k ≠ 0 := by rintro rfl; simp at hk0
  have hlc : p.leadingCoeff * k.leadingCoeff ≠ 0 :=
    fun h ↦ leadingCoeff_ne_zero.mpr hk_ne (hp.mul_right_eq_zero.mp h)
  have hk_deg : k.natDegree = 0 := by have := natDegree_mul' hlc; omega
  rw [eq_C_of_natDegree_eq_zero hk_deg, hk0, C_1, mul_one]

end Polynomial
