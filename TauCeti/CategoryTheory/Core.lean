/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Core

/-!
# Functors into the core of a category

A functor `F : D ⥤ C` sending every morphism of `D` to an isomorphism of `C` factors through the
core `Core C`, the groupoid of objects of `C` and isomorphisms between them. Mathlib's
`CategoryTheory.Core.functorToCore` is the case where `D` is a groupoid.
-/

public section

namespace CategoryTheory.Core

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- A functor sending every morphism to an isomorphism, as a functor to the core. -/
@[expose, simps obj map_iso]
noncomputable def functorToCoreOfIsIso (F : D ⥤ C)
    (hF : ∀ ⦃X Y : D⦄ (f : X ⟶ Y), IsIso (F.map f)) : D ⥤ Core C where
  obj X := .mk (F.obj X)
  map f := have := hF f; .mk (asIso (F.map f))
  map_id X := Core.hom_ext (by simp)
  map_comp f g := Core.hom_ext (by simp)

@[simp]
lemma functorToCoreOfIsIso_comp_inclusion (F : D ⥤ C)
    (hF : ∀ ⦃X Y : D⦄ (f : X ⟶ Y), IsIso (F.map f)) :
    functorToCoreOfIsIso F hF ⋙ inclusion C = F :=
  rfl

/-- The functor `functorToCoreOfIsIso (G ⋙ F)` factors through `functorToCoreOfIsIso F`. -/
lemma functorToCoreOfIsIso_comp_left (G : E ⥤ D) (F : D ⥤ C)
    (hF : ∀ ⦃X Y : D⦄ (f : X ⟶ Y), IsIso (F.map f)) :
    functorToCoreOfIsIso (G ⋙ F) (fun _ _ f ↦ hF (G.map f)) = G ⋙ functorToCoreOfIsIso F hF :=
  rfl

/-- A functor to the core is recovered from its composite with the inclusion of the core. -/
@[simp]
lemma functorToCoreOfIsIso_comp_inclusion_self (G : D ⥤ Core C) :
    functorToCoreOfIsIso (G ⋙ inclusion C) (fun _ _ f ↦ (G.map f).iso.isIso_hom) = G :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ heq_of_eq (Core.hom_ext rfl)

end CategoryTheory.Core
