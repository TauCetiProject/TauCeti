/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-!
# Right derived functors along localizations with a right adjoint

Let `adj : L ⊣ R` be an adjunction between `L : C ⥤ D` and `R : D ⥤ C`. For every functor
`F : C ⥤ H`, the composite `R ⋙ F`, together with the transformation `F ⟶ L ⋙ R ⋙ F` induced
by the unit of `adj`, is a left Kan extension of `F` along `L`
(`CategoryTheory.Adjunction.isLeftKanExtension_whiskerRightUnit`).
Hence, whenever `L` is a localization functor (for instance a reflective localization, where `R`
is fully faithful), `R ⋙ F` is a right derived functor of `F`
(`CategoryTheory.Adjunction.isRightDerivedFunctor_whiskerRightUnit`).

This is how right derived functors are computed from functorial fibrant replacements, for
instance from K-injective replacements in the unbounded derived category: `R` sends an object to
its replacement, and the unit is the replacement map.
-/

public section

open CategoryTheory Functor Limits

namespace CategoryTheory.Adjunction

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (F : C ⥤ H)

/-- The natural transformation `F ⟶ L ⋙ R ⋙ F` induced by the unit of an adjunction `L ⊣ R`. -/
def whiskerRightUnit : F ⟶ L ⋙ R ⋙ F :=
  F.leftUnitor.inv ≫ whiskerRight adj.unit F ≫ (associator L R F).hom

@[simp]
lemma whiskerRightUnit_app (X : C) : (adj.whiskerRightUnit F).app X = F.map (adj.unit.app X) := by
  simp [whiskerRightUnit]

/-- For an adjunction `L ⊣ R`, the functor `R ⋙ F` is a left Kan extension of `F` along `L`, with
unit induced by the unit of the adjunction. -/
lemma isLeftKanExtension_whiskerRightUnit :
    (R ⋙ F).IsLeftKanExtension (adj.whiskerRightUnit F) where
  nonempty_isUniversal := ⟨IsInitial.ofUniqueHom
    (fun G ↦ StructuredArrow.homMk
      (whiskerLeft R G.hom ≫ (associator R L G.right).inv ≫
        whiskerRight adj.counit G.right ≫ G.right.leftUnitor.hom) (by
        ext X
        have := G.hom.naturality (adj.unit.app X)
        dsimp at this ⊢
        simp only [whiskerRightUnit_app, Category.id_comp, Category.comp_id]
        rw [reassoc_of% this, ← G.right.map_comp, left_triangle_components, G.right.map_id,
          Category.comp_id]))
    (fun G γ ↦ by
      ext Y
      have h₁ := congr_app (StructuredArrow.w γ) (R.obj Y)
      have h₂ := γ.right.naturality (adj.counit.app Y)
      dsimp at h₁ h₂ ⊢
      simp only [whiskerRightUnit_app, Category.id_comp, Category.comp_id] at h₁ ⊢
      rw [← h₁, Category.assoc, ← h₂, ← F.map_comp_assoc, right_triangle_components]
      simp)⟩

/-- If `L` is a localization functor for `W` and `L ⊣ R`, then `R ⋙ F` is a right derived
functor of `F` with respect to `W`. -/
lemma isRightDerivedFunctor_whiskerRightUnit (W : MorphismProperty C) [L.IsLocalization W] :
    (R ⋙ F).IsRightDerivedFunctor (adj.whiskerRightUnit F) W where
  isLeftKanExtension := adj.isLeftKanExtension_whiskerRightUnit F

end CategoryTheory.Adjunction
