/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.Units

/-!
# Reflection of polynomial units under coefficient maps

An injective coefficient map that reflects units continues to reflect units after passage to
polynomials, when its target has no zero divisors.
-/

public section

namespace Polynomial

/-- Mapping coefficients along an injective homomorphism `f` into a semiring without zero divisors
reflects units of the polynomial ring when `f` itself reflects units: a polynomial whose image is a
unit has degree zero, and its constant coefficient is sent to a unit. -/
theorem isLocalHom_mapRingHom {R S : Type*} [Semiring R] [Semiring S] [NoZeroDivisors S]
    {f : R →+* S} [IsLocalHom f] (hf : Function.Injective f) : IsLocalHom (mapRingHom f) where
  map_nonunit p hp := by
    have hdeg : p.natDegree = 0 := by
      rw [← natDegree_map_eq_of_injective hf]
      exact natDegree_eq_zero_of_isUnit hp
    rw [eq_C_of_natDegree_eq_zero hdeg] at hp ⊢
    rw [coe_mapRingHom, map_C, isUnit_C] at hp
    exact (isUnit_of_map_unit f _ hp).map C

end Polynomial
