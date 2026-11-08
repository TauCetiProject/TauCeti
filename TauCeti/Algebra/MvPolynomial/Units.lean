/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Units of multivariate polynomials under a change of coefficients

Over a field `k`, the units of `k[X_σ]` are the nonzero constants. Mapping the coefficients along a
ring homomorphism `f : k →+* L` into any nontrivial commutative ring therefore reflects units: if
`map f p` is a unit of `L[X_σ]`, then its constant coefficient is a unit and its other coefficients
are nilpotent, and since `f` is injective and reflects units, the same holds for `p`. In other words
`map f` is a local homomorphism, so irreducibility of `map f p` implies irreducibility of `p`
(`Irreducible.of_map`). This is how absolute irreducibility, over an algebraic closure, gives
irreducibility over every intermediate field.

## Main results

* `MvPolynomial.isLocalHom_map`: `map f` reflects units for a ring homomorphism `f` out of a field
  into a nontrivial commutative ring. It is an instance, so `Irreducible.of_map` applies to `map f`
  directly.
* `MvPolynomial.isUnit_iff_totalDegree_eq_zero`: a nonzero polynomial over a field is a unit
  exactly when its total degree is zero.
-/

public section

namespace MvPolynomial

variable {σ k L : Type*} [Field k] [CommRing L]

/-- Over a field, a nonzero polynomial is a unit exactly when its total degree is zero, that is,
when it is a nonzero constant. -/
theorem isUnit_iff_totalDegree_eq_zero {p : MvPolynomial σ k} (hp : p ≠ 0) :
    IsUnit p ↔ p.totalDegree = 0 := by
  rw [isUnit_iff_totalDegree_of_isReduced, isUnit_iff_ne_zero, and_iff_right_iff_imp,
    totalDegree_eq_zero_iff_eq_C]
  exact fun h h0 ↦ hp (by rw [h, h0, C_0])

/-- **Changing the coefficients along a homomorphism out of a field reflects units**: a polynomial
is a unit exactly when its constant coefficient is a unit and its other coefficients are nilpotent,
and `f` is injective and reflects units. -/
instance isLocalHom_map [Nontrivial L] (f : k →+* L) : IsLocalHom (map (σ := σ) f) where
  map_nonunit p hp := by
    simp only [isUnit_iff, coeff_map] at hp
    exact isUnit_iff.mpr ⟨isUnit_of_map_unit f _ hp.1,
      fun i hi ↦ (IsNilpotent.map_iff f.injective).mp (hp.2 i hi)⟩

end MvPolynomial
