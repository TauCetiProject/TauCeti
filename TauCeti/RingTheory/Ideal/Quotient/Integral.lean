/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.IntegralClosure.Quotient

/-!
# Integral elements modulo products and powers of ideals

A monic relation modulo a two-sided ideal `I` gives a monic relation modulo every power `I^n`:
raise the original polynomial to the `n`-th power. This works in noncommutative algebras because
polynomials in a single element with central coefficients can be evaluated multiplicatively.
Likewise, monic relations modulo two two-sided ideals `I` and `J` multiply to a monic relation
modulo `I * J`. These allow finiteness arguments using integral generators to
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
  obtain ⟨p, hp, hpI⟩ := (isIntegral_quotient_iff x I).1 hx
  refine (isIntegral_quotient_iff x (I ^ n)).2 ⟨p ^ n, hp.pow n, ?_⟩
  rw [map_pow]
  exact Ideal.pow_mem_pow hpI n

/-- Integrality of an element modulo two two-sided ideals implies integrality modulo their
product: the product of the two monic relations is a monic relation. No commutativity of the
ambient algebra is needed. -/
theorem isIntegral_quotient_mul_of_isIntegral_quotient {I J : Ideal A} [I.IsTwoSided]
    [J.IsTwoSided] (x : A) (hI : IsIntegral R (Ideal.Quotient.mk I x))
    (hJ : IsIntegral R (Ideal.Quotient.mk J x)) :
    IsIntegral R (Ideal.Quotient.mk (I * J) x) := by
  obtain ⟨p, hp, hpI⟩ := (isIntegral_quotient_iff x I).1 hI
  obtain ⟨q, hq, hqJ⟩ := (isIntegral_quotient_iff x J).1 hJ
  refine (isIntegral_quotient_iff x (I * J)).2 ⟨p * q, hp.mul hq, ?_⟩
  rw [map_mul]
  exact Ideal.mul_mem_mul hpI hqJ

end TauCeti
