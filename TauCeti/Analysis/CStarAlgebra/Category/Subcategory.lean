/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Category.Basic

/-!
# Induced categories and full subcategories of C*-categories

An induced category `CategoryTheory.InducedCategory C F` and a full subcategory
`CategoryTheory.ObjectProperty.FullSubcategory P` of a C*-category `C` inherit Hom norms and
the `TauCeti.CStarCategory` structure from the ambient category.

## Main declarations

* `CategoryTheory.InducedCategory.instNorm` and
  `CategoryTheory.ObjectProperty.instNormFullSubcategory`: inherit Hom norms from the ambient
  category.
* `CategoryTheory.InducedCategory.instCStarCategory`: `CStarCategory` inheritance for induced
  categories.
* `CategoryTheory.ObjectProperty.instCStarCategoryFullSubcategory`: `CStarCategory` inheritance
  for full subcategories.
-/

public section

noncomputable section

open CategoryTheory TauCeti

universe w v u

namespace CategoryTheory.InducedCategory

variable {C : Type u} [Category.{v} C] {D : Type w}

/-- Morphisms in an induced category inherit the norm of their underlying ambient morphism. -/
instance instNorm [∀ X Y : C, Norm (X ⟶ Y)] {F : D → C}
    (X Y : InducedCategory C F) : Norm (X ⟶ Y) where
  norm f := ‖f.hom‖

/-- The norm of a morphism in an induced category is the norm of its underlying arrow. -/
theorem norm_def [∀ X Y : C, Norm (X ⟶ Y)] {F : D → C}
    {X Y : InducedCategory C F} (f : X ⟶ Y) : ‖f‖ = ‖f.hom‖ := (rfl)

/-- Bundling an arrow in an induced category preserves its norm. -/
@[simp] theorem norm_homMk [∀ X Y : C, Norm (X ⟶ Y)] {F : D → C}
    {X Y : InducedCategory C F} (f : F X ⟶ F Y) :
    ‖homMk (F := F) f‖ = ‖f‖ := (rfl)

section CStarCategory

variable [Preadditive C] [Linear ℂ C] [DaggerCategory C] [DaggerPreadditive C]
  [DaggerLinear ℂ C] [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]

/-- The normed space axioms on Hom spaces of an induced category, transported from `C`. -/
theorem normedSpaceCore (F : D → C) (X Y : InducedCategory C F) :
    NormedSpace.Core ℂ (X ⟶ Y) where
  norm_nonneg f := CStarCategory.norm_nonneg f.hom
  norm_smul c f := (CStarCategory.normedSpaceCore (F X) (F Y)).norm_smul c f.hom
  norm_triangle f g := (CStarCategory.normedSpaceCore (F X) (F Y)).norm_triangle f.hom g.hom
  norm_eq_zero_iff f := by
    rw [norm_def, CStarCategory.norm_eq_zero]
    exact ⟨fun h => hom_ext h, fun h => congrArg Hom.hom h⟩

/-- A category induced along a map on objects inherits the ambient C*-category structure. -/
instance instCStarCategory (F : D → C) : CStarCategory (InducedCategory C F) where
  normedSpaceCore := normedSpaceCore F
  completeSpace X Y := by
    let := NormedAddCommGroup.ofCore (normedSpaceCore F X Y)
    let := CStarCategory.normedAddCommGroup (F X) (F Y)
    have : CompleteSpace (F X ⟶ F Y) := CStarCategory.completeSpace (F X) (F Y)
    let e : (X ⟶ Y) ≃ᵢ (F X ⟶ F Y) :=
      { toEquiv := homEquiv
        isometry_toFun := Isometry.of_dist_eq fun f g => by
          rw [dist_eq_norm, dist_eq_norm]; rfl }
    exact e.completeSpace
  norm_comp_le f g := CStarCategory.norm_comp_le f.hom g.hom
  norm_mul_self_le f := CStarCategory.norm_mul_self_le f.hom
  exists_self_comp_dagger_eq f := by
    obtain ⟨g, hg⟩ := CStarCategory.exists_self_comp_dagger_eq f.hom
    exact ⟨homMk g, hom_ext hg⟩

end CStarCategory

end CategoryTheory.InducedCategory

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- Morphisms in a full subcategory inherit the norm of their underlying ambient morphism. -/
instance instNormFullSubcategory [∀ X Y : C, Norm (X ⟶ Y)] {P : ObjectProperty C}
    (X Y : P.FullSubcategory) : Norm (X ⟶ Y) :=
  InducedCategory.instNorm (F := FullSubcategory.obj) X Y

/-- The norm of a morphism in a full subcategory is the norm of its underlying arrow. -/
theorem norm_def [∀ X Y : C, Norm (X ⟶ Y)] {P : ObjectProperty C}
    {X Y : P.FullSubcategory} (f : X ⟶ Y) : ‖f‖ = ‖f.hom‖ := (rfl)

/-- Bundling an arrow in a full subcategory preserves its norm. -/
@[simp] theorem norm_homMk [∀ X Y : C, Norm (X ⟶ Y)] {P : ObjectProperty C}
    {X Y : P.FullSubcategory} (f : X.obj ⟶ Y.obj) :
    ‖(homMk f : X ⟶ Y)‖ = ‖f‖ := (rfl)

/-- Any full subcategory of a C*-category inherits a C*-category structure. -/
instance instCStarCategoryFullSubcategory (P : ObjectProperty C)
    [Preadditive C] [Linear ℂ C] [DaggerCategory C] [DaggerPreadditive C]
    [DaggerLinear ℂ C] [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C] :
    CStarCategory P.FullSubcategory :=
  InducedCategory.instCStarCategory FullSubcategory.obj

end CategoryTheory.ObjectProperty
