/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Coeff
public import Mathlib.Algebra.Polynomial.Monic
import TauCeti.Algebra.MonoidAlgebra.Degree
import Mathlib.Algebra.Ring.Regular

/-!
# Laurent polynomials with unit highest coefficient are regular

Multiplication by a monomial shifts the highest exponent without changing its coefficient.
Mathlib's polynomial theorem for a unit leading coefficient gives a non-zero-divisor, whose
regularity extends to Laurent polynomials by clearing denominator monomials. The coefficient
ring need not be commutative and can have zero divisors. The result survives any coefficient
homomorphism, including a quotient map.
-/

public section

namespace LaurentPolynomial

open AddMonoidAlgebra

variable {R S : Type*}

/-- A polynomial with unit leading coefficient remains regular in the Laurent polynomial
ring over any ring, by clearing denominator monomials on both sides. -/
theorem isRegular_toLaurent_of_isUnit_leadingCoeff [Ring R] {p : Polynomial R}
    (hp : IsUnit p.leadingCoeff) : IsRegular p.toLaurent := by
  constructor
  · apply isLeftRegular_of_non_zero_divisor
    intro q hq
    obtain ⟨n, q', hn⟩ := exists_T_pow q
    have hz : (p * q').toLaurent = 0 := by
      rw [map_mul, hn, ← mul_assoc, hq, zero_mul]
    have hq' : q' = 0 := (Polynomial.isUnit_leadingCoeff_mul_right_eq_zero_iff hp).mp
      (Polynomial.toLaurent_eq_zero.mp hz)
    apply (isUnit_T (R := R) n).isRegular.right.mul_right_eq_zero_iff.mp
    rw [← hn, hq', map_zero]
  · apply isRightRegular_of_non_zero_divisor
    intro q hq
    obtain ⟨n, q', hn⟩ := exists_T_pow q
    have hz : (q' * p).toLaurent = 0 := by
      rw [map_mul, hn, mul_assoc, T_mul, ← mul_assoc, hq, zero_mul]
    have hq' : q' = 0 := (Polynomial.isUnit_leadingCoeff_mul_left_eq_zero_iff hp).mp
      (Polynomial.toLaurent_eq_zero.mp hz)
    apply (isUnit_T (R := R) n).isRegular.right.mul_right_eq_zero_iff.mp
    rw [← hn, hq', map_zero]

/-- Unit highest coefficient implies regularity over any ring, without commutativity or a
non-zero-divisor hypothesis on the other coefficients. -/
theorem isRegular_of_isUnit_leadingCoeff [Ring R] {p : LaurentPolynomial R}
    (hp : IsUnit (p.leadingCoeff ((↑) : ℤ → WithBot ℤ))) : IsRegular p := by
  induction p using induction_on_mul_T with
  | mul_T p n =>
    rw [leadingCoeff_toLaurent_mul_T] at hp
    exact (isRegular_toLaurent_of_isUnit_leadingCoeff hp).mul (isUnit_T _).isRegular

/-- A Laurent polynomial with unit highest coefficient stays regular after any coefficient
homomorphism into a ring, including a zero ring or a ring with zero divisors. -/
theorem isRegular_mapRingHom_of_isUnit_leadingCoeff [Semiring R] [Ring S] (φ : R →+* S)
    {p : LaurentPolynomial R}
    (hp : IsUnit (p.leadingCoeff ((↑) : ℤ → WithBot ℤ))) :
    IsRegular (mapRingHom ℤ φ p) :=
  isRegular_of_isUnit_leadingCoeff
    (isUnit_leadingCoeff_mapRingHom WithBot.coe_injective φ hp)

end LaurentPolynomial
