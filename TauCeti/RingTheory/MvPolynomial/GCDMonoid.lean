/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Coefficient rings of multivariate polynomial GCD monoids

A nontrivial coefficient ring is a domain as soon as the multivariate polynomial ring over it is a
normalized GCD monoid, because the constant polynomials embed the coefficient ring.
-/

public section

namespace MvPolynomial

/-- A nontrivial coefficient ring is a domain as soon as the polynomial ring over it is a
normalized GCD monoid. -/
theorem isDomain_of_normalizedGCDMonoid {σ R : Type*} [CommRing R] [Nontrivial R]
    [NormalizedGCDMonoid (MvPolynomial σ R)] : IsDomain R := by
  have : NoZeroDivisors R :=
    (C_injective σ R).noZeroDivisors C (map_zero _) (map_mul C)
  exact NoZeroDivisors.to_isDomain R

end MvPolynomial
