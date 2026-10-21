/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Global sections of the isomorphism of an affine scheme with its spectrum

For an affine scheme `X`, Mathlib's `AlgebraicGeometry.Scheme.isoSpec` is the isomorphism
`X ≅ Spec Γ(X, ⊤)`. This file computes the map of global sections of its inverse: it is the
inverse of Mathlib's `AlgebraicGeometry.Scheme.ΓSpecIso`. It is the scheme-level companion of
Mathlib's `AlgebraicGeometry.IsAffineOpen.isoSpec_inv_appTop` for an affine open.

## Main results

* `AlgebraicGeometry.Scheme.isoSpec_inv_appTop`: the global sections of `X.isoSpec.inv` are
  `(Scheme.ΓSpecIso Γ(X, ⊤)).inv`.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The global sections of the inverse of `X ≅ Spec Γ(X, ⊤)`, for an affine scheme `X`. -/
theorem Scheme.isoSpec_inv_appTop (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
  have h : X.isoSpec.inv.appTop ≫ X.isoSpec.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  rw [← Iso.comp_hom_eq_id]
  simpa [Scheme.isoSpec] using h

end AlgebraicGeometry
