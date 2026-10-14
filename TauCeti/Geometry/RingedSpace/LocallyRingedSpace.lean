/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic

/-!
# Epimorphisms of locally ringed spaces determined by sections

A morphism `f : X ⟶ Y` of locally ringed spaces which is surjective on points and whose maps on
sections `Γ(Y, U) ⟶ Γ(X, f⁻¹ U)` are all monomorphisms is an epimorphism. A morphism of locally
ringed spaces is determined by its underlying morphism of presheafed spaces, so this follows from
the presheafed-space criterion
`AlgebraicGeometry.PresheafedSpace.epi_of_base_surjective_of_c_app_mono`. It applies when
`𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.epi_of_base_surjective_of_c_app_mono`: a morphism of
  locally ringed spaces which is surjective on points and a monomorphism on sections over every
  open is an epimorphism.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.LocallyRingedSpace

/-- **A morphism of locally ringed spaces which is surjective on points and a monomorphism on
sections is an epimorphism.** -/
theorem epi_of_base_surjective_of_c_app_mono {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    (h₁ : Function.Surjective f.base) (h₂ : ∀ U, Mono (f.c.app U)) : Epi f := by
  apply Functor.epi_of_epi_map LocallyRingedSpace.forgetToSheafedSpace
  apply Functor.epi_of_epi_map SheafedSpace.forgetToPresheafedSpace
  exact PresheafedSpace.epi_of_base_surjective_of_c_app_mono _ h₁ h₂

end AlgebraicGeometry.LocallyRingedSpace
