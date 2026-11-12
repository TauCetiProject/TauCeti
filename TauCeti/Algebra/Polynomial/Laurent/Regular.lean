/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Coeff
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Laurent polynomials with unit highest coefficient are regular

Multiplication by a monomial shifts the highest exponent without changing its coefficient.
Mathlib's polynomial theorem for a unit leading coefficient gives a non-zero-divisor, whose
regularity is preserved by localization. The coefficient ring can have zero divisors, and the
result survives
any coefficient homomorphism, including a quotient map.
-/

public section

namespace LaurentPolynomial

open AddMonoidAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A polynomial with unit leading coefficient remains regular in the Laurent polynomial
ring by preservation of non-zero-divisors under localization. -/
theorem isRegular_toLaurent_of_isUnit_leadingCoeff {p : Polynomial R}
    (hp : IsUnit p.leadingCoeff) : IsRegular p.toLaurent := by
  rw [← algebraMap_eq_toLaurent, isRegular_iff_mem_nonZeroDivisors]
  apply IsLocalization.nonZeroDivisors_le_comap
    (Submonoid.powers (Polynomial.X : Polynomial R)) (LaurentPolynomial R)
  rw [mem_nonZeroDivisors_iff_left]
  exact fun q hq ↦ (Polynomial.isUnit_leadingCoeff_mul_right_eq_zero_iff hp).1 hq

/-- Unit highest coefficient implies regularity for a Laurent polynomial over any
commutative ring, without a domain hypothesis. -/
theorem isRegular_of_isUnit_leadingCoeff {p : LaurentPolynomial R}
    (hp : IsUnit (p.leadingCoeff ((↑) : ℤ → WithBot ℤ))) : IsRegular p := by
  induction p using induction_on_mul_T with
  | mul_T p n =>
    rw [leadingCoeff_toLaurent_mul_T] at hp
    exact (isRegular_toLaurent_of_isUnit_leadingCoeff hp).mul (isUnit_T _).isRegular

/-- A Laurent polynomial with unit highest coefficient stays regular after any coefficient
homomorphism, including maps to a zero ring or a ring with zero divisors. -/
theorem isRegular_mapRingHom_of_isUnit_leadingCoeff (φ : R →+* S)
    {p : LaurentPolynomial R}
    (hp : IsUnit (p.leadingCoeff ((↑) : ℤ → WithBot ℤ))) :
    IsRegular (mapRingHom ℤ φ p) := by
  cases subsingleton_or_nontrivial S
  · exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ _ _ ↦ Subsingleton.elim _ _⟩
  apply isRegular_of_isUnit_leadingCoeff
  rw [leadingCoeff_mapRingHom_of_ne_zero WithBot.coe_injective φ (hp.map φ).ne_zero]
  exact hp.map φ

end LaurentPolynomial
