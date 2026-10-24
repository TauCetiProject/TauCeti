/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import TauCeti.CategoryTheory.Monoidal.Grp.Translation

/-!
# Orbit morphisms and translations for internal actions

An action in a cartesian monoidal category gives an orbit morphism from the acting
monoid to the acted-on object for each global point. For a group object, translation
by a global group point is an automorphism. The orbit morphism intertwines left
translation on the group with translation on the acted-on object. Moving its base
point corresponds instead to right multiplication on the group.

These constructions apply in particular to group schemes acting on schemes over a
base. All identities are identities of morphisms, rather than only of global points.
They use Mathlib's `Hom.mulAction` and the existing group-object `TauCeti.leftTranslation`.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj ModObj

namespace TauCeti

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

section Monoid

variable (G : C) [MonObj G] {X Y : C} [ModObj G X] [ModObj G Y]

/-- The orbit morphism of a global point, sending `g` to `g • x`. -/
def orbitMap (x : 𝟙_ C ⟶ X) : G ⟶ X :=
  (𝟙 G) • (toUnit G ≫ x)

/-- Evaluation of the orbit morphism on an arbitrary test-object point. -/
@[reassoc (attr := simp)]
theorem comp_orbitMap {T : C} (g : T ⟶ G) (x : 𝟙_ C ⟶ X) :
    g ≫ orbitMap G x = g • (toUnit T ≫ x) := by
  simp [orbitMap, comp_smul]

/-- The orbit morphism intertwines multiplication with the action morphism. -/
@[reassoc]
theorem mul_orbitMap (x : 𝟙_ C ⟶ X) :
    μ[G] ≫ orbitMap G x = G ◁ orbitMap G x ≫ γ[G, X] := by
  calc
    μ[G] ≫ orbitMap G x = (fst G G * snd G G) ≫ orbitMap G x := by
      simp [Hom.mul_def]
    _ = fst G G • (snd G G ≫ orbitMap G x) := by
      simp [comp_orbitMap, SemigroupAction.mul_smul]
    _ = G ◁ orbitMap G x ≫ γ[G, X] := by
      rw [Hom.smul_def, ← lift_whiskerLeft, lift_fst_snd, Category.id_comp]

/-- An equivariant morphism carries an orbit morphism to the orbit morphism of the image. -/
@[reassoc]
theorem orbitMap_comp (x : 𝟙_ C ⟶ X) (f : X ⟶ Y) [IsModHom G f] :
    orbitMap G x ≫ f = orbitMap G (x ≫ f) := by
  simp [orbitMap, IsModHom.map_smul, Category.assoc]

end Monoid

variable {G X Y : C} [GrpObj G] [ModObj G X] [ModObj G Y]

/-- Translation of an acted-on object by a global group point. -/
noncomputable def translation (X : C) [ModObj G X] (g : 𝟙_ C ⟶ G) : X ≅ X where
  hom := (toUnit X ≫ g) • 𝟙 X
  inv := (toUnit X ≫ g⁻¹) • 𝟙 X
  hom_inv_id := by simp [comp_smul, ← SemigroupAction.mul_smul, ← MonObj.comp_mul]
  inv_hom_id := by simp [comp_smul, ← SemigroupAction.mul_smul, ← MonObj.comp_mul]

/-- Translation acts on points by the native test-object action. -/
@[reassoc (attr := simp)]
theorem comp_translation_hom {T : C} (x : T ⟶ X) (g : 𝟙_ C ⟶ G) :
    x ≫ (translation X g).hom = (toUnit T ≫ g) • x := by
  simp [translation, comp_smul]

/-- Inverse translation acts by the inverse group point. -/
@[reassoc (attr := simp)]
theorem comp_translation_inv {T : C} (x : T ⟶ X) (g : 𝟙_ C ⟶ G) :
    x ≫ (translation X g).inv = (toUnit T ≫ g⁻¹) • x := by
  simp [translation, comp_smul]

/-- Translation by the identity is the identity isomorphism. -/
@[simp]
theorem translation_one : translation X (1 : 𝟙_ C ⟶ G) = Iso.refl X := by
  apply Iso.ext
  simp [translation, MonObj.comp_one]

/-- Translation by a product composes translations in action order. -/
@[simp]
theorem translation_mul (g h : 𝟙_ C ⟶ G) :
    translation X (g * h) = translation X h ≪≫ translation X g := by
  apply Iso.ext
  simp [translation, comp_smul, MonObj.comp_mul, SemigroupAction.mul_smul]

/-- Translation by the inverse point is the inverse translation isomorphism. -/
@[simp]
theorem translation_inv (g : 𝟙_ C ⟶ G) :
    translation X g⁻¹ = (translation X g).symm := by
  apply Iso.ext
  rfl

/-- Equivariant morphisms intertwine translations. -/
@[reassoc]
theorem translation_hom_comp (g : 𝟙_ C ⟶ G) (f : X ⟶ Y) [IsModHom G f] :
    (translation X g).hom ≫ f = f ≫ (translation Y g).hom := by
  simp [translation, IsModHom.map_smul, comp_smul]

/-- The orbit morphism intertwines left translation with the action on its target. -/
@[reassoc]
theorem leftTranslation_hom_orbitMap (g : 𝟙_ C ⟶ G) (x : 𝟙_ C ⟶ X) :
    (TauCeti.leftTranslation g).hom ≫ orbitMap G x =
      orbitMap G x ≫ (translation X g).hom := by
  simp [TauCeti.leftTranslation_hom, comp_smul, SemigroupAction.mul_smul, orbitMap]

/-- Moving the base point of an orbit morphism amounts to right multiplication on the group.
The order of multiplication matters for a noncommutative group. -/
theorem orbitMap_smul (g : 𝟙_ C ⟶ G) (x : 𝟙_ C ⟶ X) :
    orbitMap G (g • x) = (TauCeti.rightTranslation g).hom ≫ orbitMap G x := by
  simp [orbitMap, TauCeti.rightTranslation_hom, comp_smul, SemigroupAction.mul_smul]

end TauCeti
