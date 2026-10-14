/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

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
`𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism. The same criterion holds for morphisms of locally ringed
spaces, since a morphism of locally ringed spaces is determined by its underlying morphism of
presheafed spaces.

## Main results

* `AlgebraicGeometry.PresheafedSpace.ext_of_app`: morphisms of presheafed spaces agreeing on the
  underlying map and on sections over every open are equal.
* `AlgebraicGeometry.PresheafedSpace.epi_of_base_surjective_of_c_app_mono`: a morphism which is
  surjective on points and a monomorphism on sections over every open is an epimorphism.
* `AlgebraicGeometry.LocallyRingedSpace.epi_of_base_surjective_of_c_app_mono`: the same criterion
  for morphisms of locally ringed spaces.
* `TopCat.Presheaf.comp_map_comp_map_eq_self`: restricting sections to a smaller open and back
  again is the identity, since the opens of a space form a thin category.
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

namespace AlgebraicGeometry.LocallyRingedSpace

/-- **A morphism of locally ringed spaces which is surjective on points and a monomorphism on
sections is an epimorphism.** -/
theorem epi_of_base_surjective_of_c_app_mono {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    (h₁ : Function.Surjective f.base) (h₂ : ∀ U, Mono (f.c.app U)) : Epi f := by
  apply Functor.epi_of_epi_map LocallyRingedSpace.forgetToSheafedSpace
  apply Functor.epi_of_epi_map SheafedSpace.forgetToPresheafedSpace
  exact PresheafedSpace.epi_of_base_surjective_of_c_app_mono _ h₁ h₂

end AlgebraicGeometry.LocallyRingedSpace

namespace TopCat.Presheaf

universe w v u

variable {C : Type u} [Category.{v} C] {T : TopCat.{w}}

/-- Restricting sections of a presheaf to a smaller open and back again, along any two maps of
opens, is the identity: the opens of a space form a thin category. The sections are given by a
morphism `a` into `F.obj (op V)`, so that the lemma applies by `exact` even when the intermediate
open is only definitionally equal to the one in the composite. -/
theorem comp_map_comp_map_eq_self {F : T.Presheaf C} {A : C} {V V' : Opens T}
    (a : A ⟶ F.obj (op V)) (i : op V ⟶ op V') (j : op V' ⟶ op V) :
    (a ≫ F.map i) ≫ F.map j = a := by
  rw [Category.assoc, ← F.map_comp, Subsingleton.elim (i ≫ j) (𝟙 _), F.map_id, Category.comp_id]

end TopCat.Presheaf
