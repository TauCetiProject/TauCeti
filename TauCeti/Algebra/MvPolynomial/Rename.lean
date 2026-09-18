/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Ring.CompTypeclasses

/-!
# Renaming variables: inverse pairs and killing a complement

Renaming the variables of a multivariable polynomial along an equivalence `e : σ ≃ τ` is a
ring equivalence. Mathlib's `RingHomInvPair.of_ringEquiv` and
`RingHomInvPair.of_ringEquiv_symm` are deliberately not instances, so this file registers them
for `MvPolynomial.renameEquiv`. This lets semilinear equivalences over variable renaming be used
and inverted without requiring downstream local instances.

For an injective map of variables `f : σ → τ`, Mathlib's `MvPolynomial.killCompl` is the left
inverse of `rename f` sending the variables outside the range of `f` to zero. This file records its
values on single variables, as Mathlib already does for `MvPowerSeries.killCompl`.

## Main definitions

* `TauCeti.renameRingHomInvPair`: variable renaming and its inverse form a `RingHomInvPair`.
* `TauCeti.renameRingHomInvPairSymm`: the same inverse pair in the reverse direction.

## Main results

* `MvPolynomial.killCompl_X`: `killCompl` sends the variable `X (f i)` to `X i`.
* `MvPolynomial.killCompl_X_eq_zero`: `killCompl` kills the variables outside the range of `f`.
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

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R] {f : σ → τ} (hf : Function.Injective f)

/-- Killing the complement of the range of an injective `f` sends the variable `X (f i)` to
`X i`. -/
@[simp]
theorem killCompl_X (i : σ) : killCompl (R := R) hf (X (f i)) = X i := by
  rw [← rename_X, killCompl_rename_app]

/-- Killing the complement of the range of `f` sends every variable outside that range to
zero. -/
theorem killCompl_X_eq_zero {t : τ} (h : t ∉ Set.range f) : killCompl (R := R) hf (X t) = 0 := by
  simp [killCompl, h]

end MvPolynomial
