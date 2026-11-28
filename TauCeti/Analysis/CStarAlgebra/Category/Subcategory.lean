/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Category.Basic
import TauCeti.Analysis.Normed.Module.Basic

/-!
# Induced categories and full subcategories of C*-categories

An induced category `CategoryTheory.InducedCategory C F` and a full subcategory
`CategoryTheory.ObjectProperty.FullSubcategory P` of a C*-category `C` inherit Hom norms and
the `TauCeti.CStarCategory` structure from the ambient category.

## Main declarations

* `CategoryTheory.InducedCategory.normedSpaceCoreOf`: transports `NormedSpace.Core` along
  `CategoryTheory.InducedCategory.homLinearEquiv`.
* `CategoryTheory.InducedCategory.homLinearIsometryEquiv` and
  `CategoryTheory.ObjectProperty.homLinearIsometryEquiv`: normed upgrades of
  `CategoryTheory.InducedCategory.homLinearEquiv` for induced and full subcategories of
  C*-categories.
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

/-- Transport `NormedSpace.Core` from ambient Hom spaces `F X ⟶ F Y` to `X ⟶ Y` along
`CategoryTheory.InducedCategory.homLinearEquiv`. -/
theorem normedSpaceCoreOf {𝕜 : Type*} [NormedField 𝕜]
    [Preadditive C] [Linear 𝕜 C] [∀ X Y : C, Norm (X ⟶ Y)]
    (F : D → C) {X Y : InducedCategory C F}
    (hcore : NormedSpace.Core 𝕜 (F X ⟶ F Y)) :
    NormedSpace.Core 𝕜 (X ⟶ Y) :=
  hcore.induced
    (homLinearEquiv (R := 𝕜) (F := F) (X := X) (Y := Y)).toLinearMap
    homLinearEquiv.injective fun _ => rfl

section CStarCategory

variable [Preadditive C] [Linear ℂ C] [DaggerCategory C] [DaggerPreadditive C]
  [DaggerLinear ℂ C] [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]

/-- The normed space axioms on Hom spaces of an induced category, transported from `C`. -/
theorem normedSpaceCore (F : D → C) (X Y : InducedCategory C F) :
    NormedSpace.Core ℂ (X ⟶ Y) :=
  normedSpaceCoreOf F (CStarCategory.normedSpaceCore (F X) (F Y))

/-- The normed upgrade of `CategoryTheory.InducedCategory.homLinearEquiv` for an induced
category of a C*-category. -/
def homLinearIsometryEquiv {F : D → C} (X Y : InducedCategory C F) :
    letI := NormedAddCommGroup.ofCore (normedSpaceCore F X Y)
    letI := CStarCategory.normedAddCommGroup (F X) (F Y)
    (X ⟶ Y) ≃ₗᵢ[ℂ] (F X ⟶ F Y) :=
  letI := NormedAddCommGroup.ofCore (normedSpaceCore F X Y)
  letI := NormedSpace.ofCore (normedSpaceCore F X Y)
  letI := CStarCategory.normedAddCommGroup (F X) (F Y)
  letI := CStarCategory.normedSpace (F X) (F Y)
  { toLinearEquiv := homLinearEquiv
    norm_map' _ := rfl }

/-- Forward evaluation of `CategoryTheory.InducedCategory.homLinearIsometryEquiv`. -/
@[simp] theorem homLinearIsometryEquiv_apply {F : D → C} {X Y : InducedCategory C F}
    (f : X ⟶ Y) :
    letI := NormedAddCommGroup.ofCore (normedSpaceCore F X Y)
    letI := CStarCategory.normedAddCommGroup (F X) (F Y)
    homLinearIsometryEquiv X Y f = f.hom := (rfl)

/-- Inverse evaluation of `CategoryTheory.InducedCategory.homLinearIsometryEquiv`. -/
@[simp] theorem homLinearIsometryEquiv_symm_apply {F : D → C} {X Y : InducedCategory C F}
    (g : F X ⟶ F Y) :
    letI := NormedAddCommGroup.ofCore (normedSpaceCore F X Y)
    letI := CStarCategory.normedAddCommGroup (F X) (F Y)
    (homLinearIsometryEquiv X Y).symm g = homMk g := (rfl)

/-- Forgetting the norm from `CategoryTheory.InducedCategory.homLinearIsometryEquiv` recovers
`CategoryTheory.InducedCategory.homLinearEquiv`. -/
@[simp] theorem homLinearIsometryEquiv_toLinearEquiv {F : D → C}
    (X Y : InducedCategory C F) :
    letI := NormedAddCommGroup.ofCore (normedSpaceCore F X Y)
    letI := CStarCategory.normedAddCommGroup (F X) (F Y)
    (homLinearIsometryEquiv X Y).toLinearEquiv =
      (homLinearEquiv : (X ⟶ Y) ≃ₗ[ℂ] (F X ⟶ F Y)) := (rfl)

/-- A category induced along a map on objects inherits the ambient C*-category structure. -/
instance instCStarCategory (F : D → C) : CStarCategory (InducedCategory C F) where
  normedSpaceCore := normedSpaceCore F
  completeSpace X Y := by
    let := NormedAddCommGroup.ofCore (normedSpaceCore F X Y)
    let := CStarCategory.normedAddCommGroup (F X) (F Y)
    have : CompleteSpace (F X ⟶ F Y) := CStarCategory.completeSpace (F X) (F Y)
    exact (homLinearIsometryEquiv X Y).toIsometryEquiv.completeSpace
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

section CStarCategory

variable [Preadditive C] [Linear ℂ C] [DaggerCategory C] [DaggerPreadditive C]
  [DaggerLinear ℂ C] [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]

/-- Any full subcategory of a C*-category inherits a C*-category structure. -/
instance instCStarCategoryFullSubcategory (P : ObjectProperty C) :
    CStarCategory P.FullSubcategory :=
  InducedCategory.instCStarCategory FullSubcategory.obj

/-- The normed upgrade of `CategoryTheory.InducedCategory.homLinearEquiv` for a full
subcategory of a C*-category. -/
def homLinearIsometryEquiv {P : ObjectProperty C} (X Y : P.FullSubcategory) :
    letI := CStarCategory.normedAddCommGroup X Y
    letI := CStarCategory.normedAddCommGroup X.obj Y.obj
    (X ⟶ Y) ≃ₗᵢ[ℂ] (X.obj ⟶ Y.obj) :=
  InducedCategory.homLinearIsometryEquiv (F := FullSubcategory.obj) X Y

/-- Forward evaluation of `CategoryTheory.ObjectProperty.homLinearIsometryEquiv`. -/
@[simp] theorem homLinearIsometryEquiv_apply {P : ObjectProperty C} {X Y : P.FullSubcategory}
    (f : X ⟶ Y) :
    letI := CStarCategory.normedAddCommGroup X Y
    letI := CStarCategory.normedAddCommGroup X.obj Y.obj
    homLinearIsometryEquiv X Y f = f.hom := (rfl)

/-- Inverse evaluation of `CategoryTheory.ObjectProperty.homLinearIsometryEquiv`. -/
@[simp] theorem homLinearIsometryEquiv_symm_apply {P : ObjectProperty C} {X Y : P.FullSubcategory}
    (g : X.obj ⟶ Y.obj) :
    letI := CStarCategory.normedAddCommGroup X Y
    letI := CStarCategory.normedAddCommGroup X.obj Y.obj
    (homLinearIsometryEquiv X Y).symm g = homMk g := (rfl)

/-- Forgetting the norm from `CategoryTheory.ObjectProperty.homLinearIsometryEquiv` recovers
`CategoryTheory.InducedCategory.homLinearEquiv`. -/
@[simp] theorem homLinearIsometryEquiv_toLinearEquiv {P : ObjectProperty C}
    (X Y : P.FullSubcategory) :
    letI := CStarCategory.normedAddCommGroup X Y
    letI := CStarCategory.normedAddCommGroup X.obj Y.obj
    (homLinearIsometryEquiv X Y).toLinearEquiv =
      (InducedCategory.homLinearEquiv : (X ⟶ Y) ≃ₗ[ℂ] (X.obj ⟶ Y.obj)) := (rfl)

end CStarCategory

end CategoryTheory.ObjectProperty
