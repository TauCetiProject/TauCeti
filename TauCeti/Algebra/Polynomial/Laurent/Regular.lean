/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Coeff
import TauCeti.Algebra.MonoidAlgebra.Degree
import Mathlib.Algebra.Ring.Regular

/-!
# Laurent polynomials with regular highest coefficients

A Laurent polynomial with left-regular, right-regular or two-sided regular highest coefficient
has the same regularity. Highest coefficients use
`AddMonoidAlgebra.leadingCoeff ((↑) : ℤ → WithBot ℤ)`. Coefficient rings may be noncommutative
or nonreduced. A Laurent polynomial over a semiring with unit highest coefficient maps to a
regular element under every coefficient homomorphism into a ring, including quotient rings.
These cancellation results supply separated principal-ideal intersections modulo coefficients.
-/

public section

namespace LaurentPolynomial

open AddMonoidAlgebra

variable {R S : Type*}

/-- A Laurent polynomial over any ring with left-regular highest coefficient is left-regular. -/
theorem isLeftRegular_of_isLeftRegular_leadingCoeff [Ring R] {p : LaurentPolynomial R}
    (hp : IsLeftRegular (p.leadingCoeff ((↑) : ℤ → WithBot ℤ))) : IsLeftRegular p := by
  apply isLeftRegular_of_non_zero_divisor
  intro q hq
  by_contra hq0
  have hne := hp.mul_left_eq_zero_iff.not.mpr ((leadingCoeff_eq_zero q).not.mpr hq0)
  apply hne
  rw [← leadingCoeff_mul' hne, hq]
  simp

/-- A Laurent polynomial over any ring with right-regular highest coefficient is right-regular. -/
theorem isRightRegular_of_isRightRegular_leadingCoeff [Ring R] {p : LaurentPolynomial R}
    (hp : IsRightRegular (p.leadingCoeff ((↑) : ℤ → WithBot ℤ))) : IsRightRegular p := by
  apply isRightRegular_of_non_zero_divisor
  intro q hq
  by_contra hq0
  have hne := hp.mul_right_eq_zero_iff.not.mpr ((leadingCoeff_eq_zero q).not.mpr hq0)
  apply hne
  rw [← leadingCoeff_mul' hne, hq]
  simp

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
