/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import TauCeti.CategoryTheory.Monoidal.Grp.Translation
public import TauCeti.CategoryTheory.Monoidal.Mod.Basic

/-!
# Orbit morphisms and translations for internal actions

An action in a cartesian monoidal category gives an orbit morphism from the acting
monoid to the acted-on object for each global point. For a group object, translation
by a global group point is an automorphism. The orbit morphism intertwines left
translation on the group with translation on the acted-on object. Moving its base
point corresponds instead to right multiplication on the group.

A morphism is equivariant exactly when it commutes with the action on points with values in
every object (`TauCeti.isModHom_iff_map_smul`). A point `x : Z ⟶ X` of a pseudo-torsor, an
action for which `(g, x) ↦ (g • x, x)` is an isomorphism, trivialises it over `Z`
(`TauCeti.isIso_lift_smul_snd_of_isIso_leftSMul`).

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

variable {G} in
/-- A morphism is equivariant if and only if it commutes with the action on points with values
in every object. -/
theorem isModHom_iff_map_smul (f : X ⟶ Y) :
    IsModHom G f ↔ ∀ (T : C) (g : T ⟶ G) (x : T ⟶ X), (g • x) ≫ f = g • (x ≫ f) := by
  refine ⟨fun _ T g x ↦ IsModHom.map_smul f g x, fun hf ↦ ⟨?_⟩⟩
  have := hf (G ⊗ X) (fst G X) (snd G X)
  simp only [Hom.smul_def, ← lift_whiskerLeft, lift_fst_snd, Category.id_comp] at this
  exact this

variable {G} in
/-- A point `x : Z ⟶ X` of a pseudo-torsor trivialises it over `Z`: when
`(g, x) ↦ (g • x, x)` is an isomorphism `G ⊗ X ≅ X ⊗ X`, the morphism `(g, z) ↦ (g • x z, z)`
is an isomorphism `G ⊗ Z ≅ X ⊗ Z`. -/
theorem isIso_lift_smul_snd_of_isIso_leftSMul [IsIso (ModObj.leftSMul G X)] {Z : C}
    (x : Z ⟶ X) : IsIso (lift (fst G Z • (snd G Z ≫ x)) (snd G Z)) := by
  have H := (ModObj.isIso_leftSMul_iff (M := G) (X := X)).1 ‹_›
  have key {T : C} (g : T ⟶ G) (z : T ⟶ Z) :
      lift g z ≫ lift (fst G Z • (snd G Z ≫ x)) (snd G Z) = lift (g • (z ≫ x)) z := by
    simp [comp_smul]
  rw [isIso_iff_yoneda_map_bijective]
  refine fun T ↦ ⟨fun t t' htt ↦ ?_, fun y ↦ ?_⟩
  · dsimp only at htt
    rw [← lift_comp_fst_snd t, ← lift_comp_fst_snd t', key, key] at htt
    have h₂ : t ≫ snd G Z = t' ≫ snd G Z := by simpa using congrArg (· ≫ snd X Z) htt
    have h₁ : (t ≫ fst G Z) • (t ≫ snd G Z ≫ x) = (t' ≫ fst G Z) • (t' ≫ snd G Z ≫ x) := by
      simpa using congrArg (· ≫ fst X Z) htt
    refine CartesianMonoidalCategory.hom_ext _ _
      ((H T (t ≫ snd G Z ≫ x) _).unique rfl ?_).symm h₂
    rw [h₁, reassoc_of% h₂]
  · obtain ⟨g, hg, -⟩ := H T (y ≫ snd X Z ≫ x) (y ≫ fst X Z)
    refine ⟨lift g (y ≫ snd X Z), ?_⟩
    dsimp only
    rw [key, Category.assoc, hg, lift_comp_fst_snd]

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

namespace CategoryTheory.Functor

open scoped Obj

variable {C D : Type*} [Category C] [Category D]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] (G X : C) [MonObj G] [ModObj G X]

/-- A monoidal functor between cartesian categories preserves orbit morphisms, with
the base point transported by its unit comparison. -/
theorem map_orbitMap (x : 𝟙_ C ⟶ X) :
    letI := F.modObjObj G X
    F.map (TauCeti.orbitMap G x) =
      TauCeti.orbitMap (F.obj G) (LaxMonoidal.ε F ≫ F.map x) := by
  let := F.modObjObj G X
  simp only [TauCeti.orbitMap, Hom.smul_def, modObjObj_smul]
  rw [Monoidal.toUnit_ε_assoc, ← F.map_comp, ← F.map_id G,
    Monoidal.lift_μ_assoc, ← F.map_comp]

end CategoryTheory.Functor
