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

Renaming the variables of a multivariable polynomial along an equivalence `e : σ ≃ τ` is a
ring equivalence. Mathlib's `RingHomInvPair.of_ringEquiv` and
`RingHomInvPair.of_ringEquiv_symm` are deliberately not instances, so this file registers them
for `MvPolynomial.renameEquiv`. This lets semilinear equivalences over variable renaming be used
and inverted without requiring downstream local instances.

## Main definitions

* `TauCeti.renameRingHomInvPair`: variable renaming and its inverse form a `RingHomInvPair`.
* `TauCeti.renameRingHomInvPairSymm`: the same inverse pair in the reverse direction.
-/

public section

namespace TauCeti

variable {σ τ : Type*} (R : Type*) [CommSemiring R]

/-- A polynomial variable-renaming ring equivalence and its inverse form a
`RingHomInvPair`. -/
noncomputable instance renameRingHomInvPair (e : σ ≃ τ) :
    RingHomInvPair
      ((MvPolynomial.renameEquiv R e).toRingEquiv :
        MvPolynomial σ R →+* MvPolynomial τ R)
      ((MvPolynomial.renameEquiv R e).toRingEquiv.symm :
        MvPolynomial τ R →+* MvPolynomial σ R) :=
  RingHomInvPair.of_ringEquiv (MvPolynomial.renameEquiv R e).toRingEquiv

/-- The inverse polynomial variable-renaming ring equivalence and the forward equivalence form a
`RingHomInvPair`. -/
noncomputable instance renameRingHomInvPairSymm (e : σ ≃ τ) :
    RingHomInvPair
      ((MvPolynomial.renameEquiv R e).toRingEquiv.symm :
        MvPolynomial τ R →+* MvPolynomial σ R)
      ((MvPolynomial.renameEquiv R e).toRingEquiv :
        MvPolynomial σ R →+* MvPolynomial τ R) :=
  RingHomInvPair.of_ringEquiv_symm (MvPolynomial.renameEquiv R e).toRingEquiv

end TauCeti
