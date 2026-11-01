/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Integral elements modulo products and powers of ideals

A monic relation modulo a two-sided ideal `I` gives a monic relation modulo every power `I^n`:
raise the original polynomial to the `n`-th power. This works in noncommutative algebras because
polynomials in a single element with central coefficients can be evaluated multiplicatively.
Likewise, in a commutative algebra, monic relations modulo two ideals `I` and `J` multiply to a
monic relation modulo `I * J`. These allow finiteness arguments using integral generators to
survive passage to smaller ideals.
-/

public section

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Integrality of an element modulo a two-sided ideal implies integrality modulo every power
of that ideal. No commutativity of the ambient algebra is needed. -/
theorem isIntegral_quotient_pow_of_isIntegral_quotient {I : Ideal A} [I.IsTwoSided]
    (x : A) (hx : IsIntegral R (Ideal.Quotient.mk I x)) (n : ℕ) :
    IsIntegral R (Ideal.Quotient.mk (I ^ n) x) := by
  obtain ⟨p, hp, hpx⟩ := hx
  have hmem : Polynomial.aeval x p ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← Ideal.Quotient.mkₐ_eq_mk R I, ← Polynomial.aeval_algHom_apply]
    exact hpx
  refine ⟨p ^ n, hp.pow n, ?_⟩
  rw [← Polynomial.aeval_def, ← Ideal.Quotient.mkₐ_eq_mk R (I ^ n),
    Polynomial.aeval_algHom_apply, map_pow, map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hmem n)

/-- Integrality of an element modulo two ideals of a commutative algebra implies integrality
modulo their product: the product of the two monic relations is a monic relation. -/
theorem isIntegral_quotient_mul_of_isIntegral_quotient {B : Type*} [CommRing B] [Algebra R B]
    {I J : Ideal B} (x : B) (hI : IsIntegral R (Ideal.Quotient.mk I x))
    (hJ : IsIntegral R (Ideal.Quotient.mk J x)) :
    IsIntegral R (Ideal.Quotient.mk (I * J) x) := by
  have hmem {L : Ideal B} (hx : IsIntegral R (Ideal.Quotient.mk L x)) :
      ∃ p : Polynomial R, p.Monic ∧ Polynomial.aeval x p ∈ L := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p, hp, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    rw [← Ideal.Quotient.mkₐ_eq_mk R L, ← Polynomial.aeval_algHom_apply]
    exact hpx
  obtain ⟨p, hp, hpI⟩ := hmem hI
  obtain ⟨q, hq, hqJ⟩ := hmem hJ
  refine ⟨p * q, hp.mul hq, ?_⟩
  rw [← Polynomial.aeval_def, ← Ideal.Quotient.mkₐ_eq_mk R (I * J),
    Polynomial.aeval_algHom_apply, map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_mul hpI hqJ)

end TauCeti
