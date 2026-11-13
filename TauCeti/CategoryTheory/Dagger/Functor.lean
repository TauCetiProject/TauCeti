/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Dagger.Basic
public import Mathlib.CategoryTheory.NatIso

/-!
# Dagger-preserving functors and natural transformations

Preserving a chosen dagger is a property of a native functor. Natural transformations between
dagger-preserving functors admit a pointwise dagger, and pointwise unitary transformations
give natural isomorphisms. These constructions require no additive or analytic structure.
-/

public section

open CategoryTheory TauCeti

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]
variable {D : Type u₂} [Category.{v₂} D] [DaggerCategory D]
variable {E : Type u₃} [Category.{v₃} E] [DaggerCategory E]

/-- A functor preserves the chosen daggers if it commutes with taking daggers. -/
class PreservesDagger (F : C ⥤ D) : Prop where
  /-- Mapping an arrow commutes with taking its dagger. -/
  map_dagger : ∀ {X Y : C} (f : X ⟶ Y), F.map (dagger f) = dagger (F.map f)

/-- Mapping an arrow by a dagger-preserving functor commutes with its dagger. -/
@[simp, grind _=_] theorem map_dagger (F : C ⥤ D) [F.PreservesDagger] {X Y : C} (f : X ⟶ Y) :
    F.map (dagger f) = dagger (F.map f) := PreservesDagger.map_dagger f

/-- Identity functors preserve daggers. -/
instance : (𝟭 C).PreservesDagger where
  map_dagger _ := (rfl)

/-- Composites of dagger-preserving functors preserve daggers. -/
instance (F : C ⥤ D) (G : D ⥤ E) [F.PreservesDagger] [G.PreservesDagger] :
    (F ⋙ G).PreservesDagger where
  map_dagger f := by simp

/-- Dagger-preserving functors take unitary arrows to unitary arrows. -/
theorem map_isUnitary (F : C ⥤ D) [F.PreservesDagger] {X Y : C} {f : X ⟶ Y}
    (hf : IsUnitary f) : IsUnitary (F.map f) := by
  rw [isUnitary_iff] at hf ⊢
  constructor
  · simpa only [Functor.map_comp, map_dagger, Functor.map_id] using
      congrArg F.map hf.1
  · simpa only [Functor.map_comp, map_dagger, Functor.map_id] using
      congrArg F.map hf.2

/-- Faithful dagger-preserving functors detect unitary arrows. -/
@[simp] theorem map_isUnitary_iff (F : C ⥤ D) [F.PreservesDagger] [F.Faithful]
    {X Y : C} (f : X ⟶ Y) : IsUnitary (F.map f) ↔ IsUnitary f := by
  simp only [isUnitary_iff, ← map_dagger, ← Functor.map_comp, ← Functor.map_id,
    F.map_injective.eq_iff]

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]
variable {D : Type u₂} [Category.{v₂} D] [DaggerCategory D]
variable {F G H : C ⥤ D} [F.PreservesDagger] [G.PreservesDagger]

/-- The pointwise dagger of a natural transformation between dagger-preserving functors.
For `α : F ⟶ G`, this gives `G ⟶ F` with components `dagger (α.app X)`. -/
def dagger (α : F ⟶ G) : G ⟶ F where
  app X := TauCeti.dagger (α.app X)
  naturality X Y f := by
    simpa using (congrArg TauCeti.dagger (α.naturality (TauCeti.dagger f))).symm

/-- The dagger of a natural transformation acts componentwise. -/
@[simp, grind =] theorem dagger_app (α : F ⟶ G) (X : C) :
    α.dagger.app X = TauCeti.dagger (α.app X) := (rfl)

/-- Taking the pointwise dagger twice recovers the natural transformation. -/
@[simp, grind =] theorem dagger_dagger (α : F ⟶ G) : α.dagger.dagger = α := by
  ext X
  simp

/-- The pointwise dagger fixes identity natural transformations. -/
@[simp, grind =] theorem dagger_id (F : C ⥤ D) [F.PreservesDagger] :
    (𝟙 F : F ⟶ F).dagger = 𝟙 F := by
  ext X
  simp

/-- Taking the pointwise dagger reverses an equality natural transformation. -/
@[simp, grind =] theorem dagger_eqToHom (h : F = G) :
    (eqToHom h : F ⟶ G).dagger = eqToHom h.symm := by
  cases h
  simp

/-- Taking pointwise daggers reverses vertical composition. -/
@[simp, grind =] theorem dagger_comp [H.PreservesDagger] (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).dagger = β.dagger ≫ α.dagger := by
  ext X
  simp

/-- A natural transformation with unitary components is a natural isomorphism. -/
def unitaryIso (α : F ⟶ G) (hα : ∀ X, IsUnitary (α.app X)) : F ≅ G :=
  NatIso.ofComponents (fun X => (hα X).toIso) (by simp)

omit [DaggerCategory C] [F.PreservesDagger] [G.PreservesDagger] in
/-- The forward natural transformation of the pointwise unitary isomorphism. -/
@[simp, grind =] theorem unitaryIso_hom (α : F ⟶ G) (hα : ∀ X, IsUnitary (α.app X)) :
    (α.unitaryIso hα).hom = α := by
  ext X
  simp [unitaryIso]

/-- The inverse of the pointwise unitary isomorphism is the pointwise dagger. -/
@[simp, grind =] theorem unitaryIso_inv (α : F ⟶ G) (hα : ∀ X, IsUnitary (α.app X)) :
    (α.unitaryIso hα).inv = α.dagger := by
  ext X
  simp [unitaryIso]

omit [DaggerCategory C] [F.PreservesDagger] [G.PreservesDagger] in
/-- The inverse of the pointwise unitary isomorphism acts by the component's dagger. -/
@[simp, grind =] theorem unitaryIso_inv_app (α : F ⟶ G)
    (hα : ∀ X, IsUnitary (α.app X)) (X : C) :
    (α.unitaryIso hα).inv.app X = TauCeti.dagger (α.app X) := by
  simp [unitaryIso]

end CategoryTheory.NatTrans

namespace CategoryTheory.Iso

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]
variable {D : Type u₂} [Category.{v₂} D] [DaggerCategory D]
variable {F G : C ⥤ D} [F.PreservesDagger] [G.PreservesDagger]

/-- A natural isomorphism has pointwise dagger as inverse exactly when its components are
unitary. This characterizes unitary natural isomorphisms using native natural isomorphisms. -/
theorem inv_eq_dagger_iff (e : F ≅ G) :
    e.inv = e.hom.dagger ↔ ∀ X, IsUnitary (e.hom.app X) := by
  constructor
  · intro h X
    apply (e.app X).isUnitary_hom_iff.mpr
    exact (congrArg (fun α : G ⟶ F => α.app X) h).symm
  · intro h
    ext X
    exact ((e.app X).isUnitary_hom_iff.mp (h X)).symm

end CategoryTheory.Iso
