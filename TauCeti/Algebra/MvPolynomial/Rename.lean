/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Ring.CompTypeclasses

/-!
# Renaming variables along an equivalence as a ring-homomorphism inverse pair

Renaming the variables of a multivariable polynomial along an equivalence `e : σ ≃ τ` and along
its inverse `e.symm` are mutually inverse ring homomorphisms. Mathlib's
`RingHomInvPair.of_ringEquiv` is deliberately not an instance, so this file registers the
`RingHomInvPair` instance for this pair. It lets semilinear equivalences over
`MvPolynomial.rename e`, such as `M ≃ₛₗ[rename e] N`, be stated and inverted without local
instances.

## Main definitions

* `TauCeti.renameRingHomInvPair`: renaming along `e` and along `e.symm` form a
  `RingHomInvPair`.
-/

public section

namespace TauCeti

open MvPolynomial

variable {σ τ : Type*} (R : Type*) [CommSemiring R]

/-- Renaming variables along an equivalence and along its inverse are inverse ring
homomorphisms. -/
noncomputable instance renameRingHomInvPair (e : σ ≃ τ) :
    RingHomInvPair
      ((rename ⇑e : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) :
        MvPolynomial σ R →+* MvPolynomial τ R)
      ((rename ⇑e.symm : MvPolynomial τ R →ₐ[R] MvPolynomial σ R) :
        MvPolynomial τ R →+* MvPolynomial σ R) :=
  RingHomInvPair.of_ringEquiv (renameEquiv R e).toRingEquiv

end TauCeti
