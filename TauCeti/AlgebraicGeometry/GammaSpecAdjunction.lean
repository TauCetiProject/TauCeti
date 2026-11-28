/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Global sections of the Γ–Spec comparison

`AlgebraicGeometry.LocallyRingedSpace.Γ_map_toΓSpec_comp` recovers the ring map inducing a
morphism from a locally ringed space to an affine spectrum. It uses Mathlib's naturality of
`toSpecΓ` and the Γ–Spec left triangle.
-/

public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

/-- Pulling back global sections along the morphism to `Spec R` induced by `f` recovers `f`
under the canonical identification of the global sections of `Spec R` with `R`. -/
@[reassoc (attr := simp)]
theorem Γ_map_toΓSpec_comp (X : LocallyRingedSpace.{u}) {R : CommRingCat.{u}}
    (f : R ⟶ Γ.obj (op X)) :
    toSpecΓ R ≫ Γ.map (X.toΓSpec ≫ Spec.locallyRingedSpaceMap f).op = f := by
  have hmap : Γ.map (X.toΓSpec ≫ Spec.locallyRingedSpaceMap f).op =
      Γ.map (Spec.locallyRingedSpaceMap f).op ≫ Γ.map X.toΓSpec.op := by
    rw [op_comp, Functor.map_comp]
  have htriangle : toSpecΓ (Γ.obj (op X)) ≫ Γ.map X.toΓSpec.op = 𝟙 _ :=
    X.Γ_Spec_left_triangle
  calc
    _ = toSpecΓ R ≫ Γ.map (Spec.locallyRingedSpaceMap f).op ≫ Γ.map X.toΓSpec.op :=
      congrArg (toSpecΓ R ≫ ·) hmap
    _ = f ≫ toSpecΓ (Γ.obj (op X)) ≫ Γ.map X.toΓSpec.op :=
      (Spec_Γ_naturality_assoc f _).symm
    _ = f := by rw [htriangle, Category.comp_id]

end AlgebraicGeometry.LocallyRingedSpace
