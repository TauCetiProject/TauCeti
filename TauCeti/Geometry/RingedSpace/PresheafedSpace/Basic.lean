/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.Topology.Category.TopCat.EpiMono

/-!
# Morphisms of presheafed spaces determined by sections

Two morphisms `α β : X ⟶ Y` of presheafed spaces with the same underlying continuous map agree
once their maps on sections `Γ(Y, U) ⟶ Γ(X, α⁻¹ U)` and `Γ(Y, U) ⟶ Γ(X, β⁻¹ U)` agree up to the
identification `α⁻¹ U = β⁻¹ U`. This is the presheafed-space form of Mathlib's
`AlgebraicGeometry.Scheme.Hom.ext`, and is convenient when a morphism of presheafed spaces is
built by hand before its locality on stalks is known, so that it is not yet a morphism of
locally ringed spaces or of schemes.

A morphism `f : X ⟶ Y` of presheafed spaces which is surjective on points and whose maps on sections
`Γ(Y, U) ⟶ Γ(X, f⁻¹ U)` are all monomorphisms is an epimorphism: two morphisms out of `Y` which
agree after composing with `f` agree on points because `f` is surjective, and then on sections
because the maps on sections of `f` can be cancelled. This is the sectionwise analogue of
Mathlib's `AlgebraicGeometry.SheafedSpace.epi_of_base_surjective_of_stalk_mono`, and applies when
`𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism.

## Main results

* `AlgebraicGeometry.PresheafedSpace.ext_of_app`: morphisms of presheafed spaces agreeing on the
  underlying map and on sections over every open are equal.
* `AlgebraicGeometry.PresheafedSpace.epi_of_base_surjective_of_c_app_mono`: a morphism which is
  surjective on points and a monomorphism on sections over every open is an epimorphism.
-/

public section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.PresheafedSpace

universe w v u

variable {C : Type u} [Category.{v} C] {X Y : PresheafedSpace.{_, _, w} C}

/-- Two morphisms of presheafed spaces are equal if they have the same underlying continuous map
and the same maps on sections over every open subset, up to the induced identification of
preimages. -/
theorem ext_of_app {α β : X ⟶ Y} (w : α.base = β.base)
    (h : ∀ U, α.c.app (op U) ≫ X.presheaf.map (eqToHom congr((Opens.map $w.symm).obj U)).op =
      β.c.app (op U)) : α = β := by
  obtain ⟨αb, αc⟩ := α
  obtain ⟨βb, βc⟩ := β
  dsimp at w
  subst w
  congr
  exact TopCat.Presheaf.ext fun U ↦ by simpa using h U

/-- **A morphism of presheafed spaces which is surjective on points and a monomorphism on
sections is an epimorphism.** -/
theorem epi_of_base_surjective_of_c_app_mono (f : X ⟶ Y) (h₁ : Function.Surjective f.base)
    (h₂ : ∀ U, Mono (f.c.app U)) : Epi f := by
  refine ⟨fun {Z} g g' e ↦ ?_⟩
  obtain ⟨gb, gc⟩ := g
  obtain ⟨gb', gc'⟩ := g'
  obtain rfl : gb = gb' := ((TopCat.epi_iff_surjective f.base).2 h₁).left_cancellation _ _
    congr(Hom.base $e)
  congr
  ext U
  rw [← cancel_mono (f.c.app _)]
  exact congr(NatTrans.app (Hom.c $e) (op U))

end AlgebraicGeometry.PresheafedSpace
