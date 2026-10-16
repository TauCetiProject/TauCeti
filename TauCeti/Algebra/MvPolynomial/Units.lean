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
homomorphism of fields `f : k →+* L` therefore reflects units: if `map f p` is a unit of `L[X_σ]`,
then `p` is a nonzero constant. In other words `map f` is a local homomorphism, so irreducibility of
`map f p` implies irreducibility of `p` (`Irreducible.of_map`). This is how absolute irreducibility,
over an algebraic closure, gives irreducibility over every intermediate field.

## Main results

* `MvPolynomial.isLocalHom_map`: `map f` reflects units for a homomorphism of fields `f`. It is an
  instance, so `Irreducible.of_map` applies to `map f` directly.
-/

public section

namespace MvPolynomial

variable {σ k L : Type*} [Field k] [Field L]

/-- **Changing the coefficients along a homomorphism of fields reflects units**: units of `k[X_σ]`
and `L[X_σ]` are the nonzero constants. -/
instance isLocalHom_map (f : k →+* L) : IsLocalHom (map (σ := σ) f) where
  map_nonunit p hp := by
    rw [isUnit_iff_totalDegree_of_isReduced] at hp ⊢
    refine ⟨isUnit_iff_ne_zero.mpr fun h0 ↦ ?_, ?_⟩
    · simp [coeff_map, h0] at hp
    · simpa only [totalDegree, support_map_of_injective p f.injective] using hp.2

end MvPolynomial
