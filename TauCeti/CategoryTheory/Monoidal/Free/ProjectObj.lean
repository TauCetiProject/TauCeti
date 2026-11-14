/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Free.Basic

/-!
# Transporting interpretations of tensor words along isomorphisms

Mathlib's `CategoryTheory.FreeMonoidalCategory.projectObj f` interprets a formal tensor word in
the generators `C` as an object of a monoidal category `D`, once the generators are interpreted
by `f : C → D`. This file transports such interpretations along isomorphisms: a family of
isomorphisms `e a : f a ≅ g a` extends to isomorphisms
`FreeMonoidalCategory.projectObjIso e X : projectObj f X ≅ projectObj g X` for every word `X`,
the unit word going to the identity and a tensor word to the tensor product of isomorphisms.
The extension is compatible with identities, composites and inverses of the families.

These isomorphisms are the objectwise data of morphisms between interpretations of a tensor
signature, which are families of isomorphisms of generators compatible with the generating
morphisms after extension to their source and target words.
-/

public section

universe u u' v'

namespace CategoryTheory.FreeMonoidalCategory

open MonoidalCategory

variable {C : Type u} {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {f g h : C → D}

/-- The isomorphism between the interpretations of a tensor word induced by isomorphisms
`e a : f a ≅ g a` of the interpretations of its generators. -/
@[expose] def projectObjIso (e : ∀ a, f a ≅ g a) :
    ∀ X : FreeMonoidalCategory C, projectObj f X ≅ projectObj g X
  | .of a => e a
  | .unit => Iso.refl _
  | .tensor X Y => projectObjIso e X ⊗ᵢ projectObjIso e Y

@[simp]
theorem projectObjIso_of (e : ∀ a, f a ≅ g a) (a : C) : projectObjIso e (.of a) = e a :=
  (rfl)

@[simp]
theorem projectObjIso_tensorUnit (e : ∀ a, f a ≅ g a) :
    projectObjIso e (𝟙_ (FreeMonoidalCategory C)) = Iso.refl (𝟙_ D) :=
  (rfl)

@[simp]
theorem projectObjIso_tensor (e : ∀ a, f a ≅ g a) (X Y : FreeMonoidalCategory C) :
    projectObjIso e (X ⊗ Y) = projectObjIso e X ⊗ᵢ projectObjIso e Y :=
  (rfl)

@[simp]
theorem projectObjIso_refl (X : FreeMonoidalCategory C) :
    projectObjIso (fun a ↦ Iso.refl (f a)) X = Iso.refl (projectObj f X) := by
  induction X with
  | of a => rfl
  | unit => rfl
  | tensor X Y hX hY =>
    dsimp only [projectObjIso, projectObj]
    rw [hX, hY]
    ext
    simp

@[simp]
theorem projectObjIso_trans (e : ∀ a, f a ≅ g a) (e' : ∀ a, g a ≅ h a)
    (X : FreeMonoidalCategory C) :
    projectObjIso (fun a ↦ e a ≪≫ e' a) X = projectObjIso e X ≪≫ projectObjIso e' X := by
  induction X with
  | of a => rfl
  | unit => exact (Iso.refl_trans _).symm
  | tensor X Y hX hY =>
    dsimp only [projectObjIso, projectObj]
    rw [hX, hY]
    ext
    simp

@[simp]
theorem projectObjIso_symm (e : ∀ a, f a ≅ g a) (X : FreeMonoidalCategory C) :
    projectObjIso (fun a ↦ (e a).symm) X = (projectObjIso e X).symm := by
  induction X with
  | of a => rfl
  | unit => exact (Iso.refl_symm _).symm
  | tensor X Y hX hY =>
    dsimp only [projectObjIso, projectObj]
    rw [hX, hY]
    ext
    simp

end CategoryTheory.FreeMonoidalCategory
