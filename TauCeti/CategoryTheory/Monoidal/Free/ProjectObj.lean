/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.Basic
import TauCeti.CategoryTheory.Monoidal.EqToHom

/-!
# Transporting interpretations of tensor words along isomorphisms

Mathlib's `CategoryTheory.FreeMonoidalCategory.projectObj f` interprets a formal tensor word in
the generators `C` as an object of a monoidal category `D`, once the generators are interpreted
by `f : C → D`. This file transports such interpretations along isomorphisms: a family of
isomorphisms `e a : f a ≅ g a` extends to isomorphisms
`FreeMonoidalCategory.projectObjIso e X : projectObj f X ≅ projectObj g X` for every word `X`,
the unit word going to the identity and a tensor word to the tensor product of isomorphisms.
The extension is compatible with identities, composites, inverses, object-equality transports of
the families, and word substitution (`FreeMonoidalCategory.projectObjIso_projectObj`).

These isomorphisms are the objectwise data of morphisms between interpretations of a tensor
signature, which are families of isomorphisms of generators compatible with the generating
morphisms after extension to their source and target words.
-/

public section

universe u u' u'' v'

namespace CategoryTheory.FreeMonoidalCategory

open MonoidalCategory

variable {C : Type u} {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {f g h : C → D}

/-- The isomorphism between the interpretations of a tensor word induced by isomorphisms
`e a : f a ≅ g a` of the interpretations of its generators. -/
def projectObjIso (e : ∀ a, f a ≅ g a) :
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

/-- Extending equality transports on generators to a tensor word gives the equality transport
induced by `projectObj_congr`. -/
@[simp]
theorem projectObjIso_eqToIso (h : ∀ a, f a = g a) (X : FreeMonoidalCategory C) :
    projectObjIso (fun a ↦ eqToIso (h a)) X = eqToIso (projectObj_congr h X) := by
  induction X with
  | of a => rfl
  | unit => ext; rfl
  | tensor X Y hX hY =>
    dsimp only [projectObjIso, projectObj]
    rw [hX, hY]
    exact TauCeti.eqToIso_tensorIso_eqToIso (projectObj_congr h X) (projectObj_congr h Y)

/-- Extending generator isomorphisms `e` along tensor words `h` and then over a word `X` agrees
with evaluating `projectObjIso e` on the substituted word `projectObj h X`, up to
`projectObj_projectObj`. -/
theorem projectObjIso_projectObj {C' : Type u''} {f g : C' → D} (e : ∀ b, f b ≅ g b)
    (h : C → FreeMonoidalCategory C') (X : FreeMonoidalCategory C) :
    projectObjIso (fun a ↦ projectObjIso e (h a)) X =
      eqToIso (projectObj_projectObj f h X).symm ≪≫
        projectObjIso e (projectObj h X) ≪≫
        eqToIso (projectObj_projectObj g h X) := by
  induction X with
  | of a =>
    ext
    -- Both endpoints of `projectObj_projectObj` on `.of a` are definitionally `projectObj _ (h a)`,
    -- and both `projectObjIso` applications reduce definitionally to `projectObjIso e (h a)`.
    apply eq_of_heq
    simp only [Iso.trans_hom, eqToIso.hom, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    rfl
  | unit =>
    ext
    -- Both endpoints of `projectObj_projectObj` on `.unit` are definitionally `𝟙_ D`,
    -- and both sides reduce definitionally to `𝟙 (𝟙_ D)`.
    apply eq_of_heq
    simp only [Iso.trans_hom, eqToIso.hom, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    rfl
  | tensor X Y ihX ihY =>
    ext
    apply eq_of_heq
    change (projectObjIso (fun a ↦ projectObjIso e (h a)) (X ⊗ Y)).hom ≍ _
    rw [projectObjIso_tensor, tensorIso_hom, ihX, ihY]
    -- `projectObj h (X ⊗ Y) = projectObj h X ⊗ projectObj h Y` (`projectObj_tensorObj`) and
    -- `projectObjIso e (_ ⊗ _) = projectObjIso e _ ⊗ᵢ projectObjIso e _`, and in `HEq` the outer
    -- `eqToHom` conjugations match definitionally (proof-irrelevant equalities on defeq endpoints).
    simp only [Iso.trans_hom, eqToIso.hom, ← MonoidalCategory.tensorHom_comp_tensorHom,
      TauCeti.eqToHom_tensorHom_eqToHom]
    rfl

/-- Transporting `projectObjIso e` along an equality of tensor words `w = w'` conjugates its
component by `eqToHom`. -/
theorem projectObjIso_congr_word (e : ∀ a, f a ≅ g a)
    {w w' : FreeMonoidalCategory C} (hw : w = w') :
    (projectObjIso e w).hom =
      eqToHom (congrArg (projectObj f) hw) ≫ (projectObjIso e w').hom ≫
        eqToHom (congrArg (projectObj g) hw).symm := by
  subst hw
  simp

end CategoryTheory.FreeMonoidalCategory
