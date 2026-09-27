/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Scalar extension of module endomorphisms

Extension of scalars carries multiplication by a scalar to multiplication by its image.
This transports the curvature equations of a matrix factorization when its components are
extended along a ring map, so the resulting factorization has the image potential.
-/

public section

universe u v

namespace TauCeti.ModuleCat

open CategoryTheory
open scoped ChangeOfRings

variable {S : Type u} {T : Type v} [CommRing S] [CommRing T] {w : S}

/-- Scalar extension sends multiplication by a scalar to multiplication by its image. -/
@[simp] theorem extendScalars_map_smul_id (f : S →+* T) (M : _root_.ModuleCat.{u} S) :
    (_root_.ModuleCat.extendScalars f).map (w • 𝟙 M) = f w • 𝟙 _ := by
  let _ : Algebra S T := f.toAlgebra
  apply _root_.ModuleCat.hom_ext
  -- Expose the underlying base-changed linear map after forgetting the category wrapper.
  change (w • (LinearMap.id : M →ₗ[S] M)).baseChange T =
    (f w) • (LinearMap.id : TensorProduct S T M →ₗ[T] TensorProduct S T M)
  rw [LinearMap.baseChange_smul, LinearMap.baseChange_id]
  rfl

end TauCeti.ModuleCat
