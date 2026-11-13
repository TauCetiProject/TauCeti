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
# Laurent polynomials with regular highest coefficients

A polynomial with left-regular, right-regular or two-sided regular leading coefficient has the
same regularity after polynomial inclusion. The analogous statements for Laurent polynomials
use `AddMonoidAlgebra.leadingCoeff ((↑) : ℤ → WithBot ℤ)`. Coefficient rings may be noncommutative
or nonreduced. A Laurent polynomial over a semiring with unit highest coefficient maps to a
regular element under every coefficient homomorphism into a ring, including quotient rings.
These cancellation results supply separated principal-ideal intersections modulo coefficients.
-/

public section

namespace LaurentPolynomial

open AddMonoidAlgebra

variable {R S : Type*}

/-- A polynomial over any ring with left-regular leading coefficient is left-regular after
polynomial inclusion into the Laurent ring. -/
theorem isLeftRegular_toLaurent_of_isLeftRegular_leadingCoeff [Ring R] {p : Polynomial R}
    (hp : IsLeftRegular p.leadingCoeff) : IsLeftRegular p.toLaurent := by
  apply isLeftRegular_of_non_zero_divisor
  intro q hq
  obtain ⟨n, q', hn⟩ := exists_T_pow q
  have hz : (p * q').toLaurent = 0 := by
    rw [map_mul, hn, ← mul_assoc, hq, zero_mul]
  have hcoef := congrArg
    (fun r : Polynomial R ↦ r.coeff (p.natDegree + q'.natDegree))
    (Polynomial.toLaurent_eq_zero.mp hz)
  rw [Polynomial.coeff_mul_degree_add_degree, Polynomial.coeff_zero] at hcoef
  have hq' : q' = 0 := Polynomial.leadingCoeff_eq_zero.mp
    (hp.mul_left_eq_zero_iff.mp hcoef)
  apply (isUnit_T (R := R) n).isRegular.right.mul_right_eq_zero_iff.mp
  rw [← hn, hq', map_zero]

/-- A polynomial over any ring with right-regular leading coefficient is right-regular after
polynomial inclusion into the Laurent ring. -/
theorem isRightRegular_toLaurent_of_isRightRegular_leadingCoeff [Ring R] {p : Polynomial R}
    (hp : IsRightRegular p.leadingCoeff) : IsRightRegular p.toLaurent := by
  apply isRightRegular_of_non_zero_divisor
  intro q hq
  obtain ⟨n, q', hn⟩ := exists_T_pow q
  have hz : (q' * p).toLaurent = 0 := by
    rw [map_mul, hn, mul_assoc, T_mul, ← mul_assoc, hq, zero_mul]
  have hcoef := congrArg
    (fun r : Polynomial R ↦ r.coeff (q'.natDegree + p.natDegree))
    (Polynomial.toLaurent_eq_zero.mp hz)
  rw [Polynomial.coeff_mul_degree_add_degree, Polynomial.coeff_zero] at hcoef
  have hq' : q' = 0 := Polynomial.leadingCoeff_eq_zero.mp
    (hp.mul_right_eq_zero_iff.mp hcoef)
  apply (isUnit_T (R := R) n).isRegular.right.mul_right_eq_zero_iff.mp
  rw [← hn, hq', map_zero]

/-- A polynomial over any ring with regular leading coefficient is regular after inclusion
into the Laurent polynomial ring. -/
theorem isRegular_toLaurent_of_isRegular_leadingCoeff [Ring R] {p : Polynomial R}
    (hp : IsRegular p.leadingCoeff) : IsRegular p.toLaurent :=
  ⟨isLeftRegular_toLaurent_of_isLeftRegular_leadingCoeff hp.left,
    isRightRegular_toLaurent_of_isRightRegular_leadingCoeff hp.right⟩

/-- A Laurent polynomial over any ring with left-regular highest coefficient is left-regular. -/
theorem isLeftRegular_of_isLeftRegular_leadingCoeff [Ring R] {p : LaurentPolynomial R}
    (hp : IsLeftRegular (p.leadingCoeff ((↑) : ℤ → WithBot ℤ))) : IsLeftRegular p := by
  induction p using induction_on_mul_T with
  | mul_T p n =>
    rw [leadingCoeff_mul_T, leadingCoeff_toLaurent] at hp
    exact (isLeftRegular_toLaurent_of_isLeftRegular_leadingCoeff hp).mul
      (isUnit_T _).isRegular.left

/-- A Laurent polynomial over any ring with right-regular highest coefficient is right-regular. -/
theorem isRightRegular_of_isRightRegular_leadingCoeff [Ring R] {p : LaurentPolynomial R}
    (hp : IsRightRegular (p.leadingCoeff ((↑) : ℤ → WithBot ℤ))) : IsRightRegular p := by
  induction p using induction_on_mul_T with
  | mul_T p n =>
    rw [leadingCoeff_mul_T, leadingCoeff_toLaurent] at hp
    exact (isRightRegular_toLaurent_of_isRightRegular_leadingCoeff hp).mul
      (isUnit_T _).isRegular.right

/-- A Laurent polynomial over any ring with regular highest coefficient is regular. -/
theorem isRegular_of_isRegular_leadingCoeff [Ring R] {p : LaurentPolynomial R}
    (hp : IsRegular (p.leadingCoeff ((↑) : ℤ → WithBot ℤ))) : IsRegular p :=
  ⟨isLeftRegular_of_isLeftRegular_leadingCoeff hp.left,
    isRightRegular_of_isRightRegular_leadingCoeff hp.right⟩

/-- A Laurent polynomial over a semiring with unit highest coefficient maps to a regular
element under every coefficient homomorphism into a ring, including a zero ring. -/
theorem isRegular_mapRingHom_of_isUnit_leadingCoeff [Semiring R] [Ring S] (φ : R →+* S)
    {p : LaurentPolynomial R}
    (hp : IsUnit (p.leadingCoeff ((↑) : ℤ → WithBot ℤ))) :
    IsRegular (mapRingHom ℤ φ p) :=
  isRegular_of_isRegular_leadingCoeff (isUnit_leadingCoeff_mapRingHom φ hp).isRegular

end LaurentPolynomial
