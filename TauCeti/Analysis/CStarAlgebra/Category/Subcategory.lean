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

* `CategoryTheory.InducedCategory.instNorm` and
  `CategoryTheory.ObjectProperty.instNormFullSubcategory`: inherit Hom norms from the ambient
  category.
* `CategoryTheory.InducedCategory.homLinearIsometryEquiv` and
  `CategoryTheory.ObjectProperty.homLinearIsometryEquiv`: normed upgrades of
  `CategoryTheory.InducedCategory.homLinearEquiv` for induced and full-subcategory Hom spaces
  whose norms agree with their underlying arrows.
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

/-- The normed upgrade of `CategoryTheory.InducedCategory.homLinearEquiv`, when the induced and
ambient Hom spaces carry compatible linear and normed structures along `f ↦ f.hom`. -/
def homLinearIsometryEquiv {R : Type*} [Semiring R] {F : D → C} (X Y : InducedCategory C F)
    [SeminormedAddCommGroup (X ⟶ Y)] [Module R (X ⟶ Y)]
    [SeminormedAddCommGroup (F X ⟶ F Y)] [Module R (F X ⟶ F Y)]
    (hadd : ∀ f g : X ⟶ Y, (f + g).hom = f.hom + g.hom := by intros; rfl)
    (hsmul : ∀ (r : R) (f : X ⟶ Y), (r • f).hom = r • f.hom := by intros; rfl)
    (hnorm : ∀ f : X ⟶ Y, ‖f.hom‖ = ‖f‖ := by intros; rfl) :
    (X ⟶ Y) ≃ₗᵢ[R] (F X ⟶ F Y) where
  toFun f := f.hom
  invFun g := homMk g
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := hadd
  map_smul' := hsmul
  norm_map' := hnorm

/-- Forward evaluation of `CategoryTheory.InducedCategory.homLinearIsometryEquiv`. -/
@[simp] theorem homLinearIsometryEquiv_apply {R : Type*} [Semiring R]
    {F : D → C} {X Y : InducedCategory C F}
    [SeminormedAddCommGroup (X ⟶ Y)] [Module R (X ⟶ Y)]
    [SeminormedAddCommGroup (F X ⟶ F Y)] [Module R (F X ⟶ F Y)]
    (hadd : ∀ f g : X ⟶ Y, (f + g).hom = f.hom + g.hom)
    (hsmul : ∀ (r : R) (f : X ⟶ Y), (r • f).hom = r • f.hom)
    (hnorm : ∀ f : X ⟶ Y, ‖f.hom‖ = ‖f‖) (f : X ⟶ Y) :
    homLinearIsometryEquiv X Y hadd hsmul hnorm f = f.hom := (rfl)

/-- Inverse evaluation of `CategoryTheory.InducedCategory.homLinearIsometryEquiv`. -/
@[simp] theorem homLinearIsometryEquiv_symm_apply {R : Type*} [Semiring R]
    {F : D → C} {X Y : InducedCategory C F}
    [SeminormedAddCommGroup (X ⟶ Y)] [Module R (X ⟶ Y)]
    [SeminormedAddCommGroup (F X ⟶ F Y)] [Module R (F X ⟶ F Y)]
    (hadd : ∀ f g : X ⟶ Y, (f + g).hom = f.hom + g.hom)
    (hsmul : ∀ (r : R) (f : X ⟶ Y), (r • f).hom = r • f.hom)
    (hnorm : ∀ f : X ⟶ Y, ‖f.hom‖ = ‖f‖) (g : F X ⟶ F Y) :
    (homLinearIsometryEquiv X Y hadd hsmul hnorm).symm g = homMk g := (rfl)

section CStarCategory

variable [Preadditive C] [Linear ℂ C] [DaggerCategory C] [DaggerPreadditive C]
  [DaggerLinear ℂ C] [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]

/-- The normed space axioms on Hom spaces of an induced category, transported from `C`. -/
theorem normedSpaceCore (F : D → C) (X Y : InducedCategory C F) :
    NormedSpace.Core ℂ (X ⟶ Y) :=
  (CStarCategory.normedSpaceCore (F X) (F Y)).induced
    (homLinearEquiv (R := ℂ) (F := F) (X := X) (Y := Y)).toLinearMap
    homLinearEquiv.injective fun _ => rfl

/-- A category induced along a map on objects inherits the ambient C*-category structure. -/
instance instCStarCategory (F : D → C) : CStarCategory (InducedCategory C F) where
  normedSpaceCore := normedSpaceCore F
  completeSpace X Y := by
    let := NormedAddCommGroup.ofCore (normedSpaceCore F X Y)
    let := CStarCategory.normedAddCommGroup (F X) (F Y)
    have : CompleteSpace (F X ⟶ F Y) := CStarCategory.completeSpace (F X) (F Y)
    exact (homLinearIsometryEquiv (R := ℂ) X Y).toIsometryEquiv.completeSpace
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

/-- The normed upgrade of `CategoryTheory.InducedCategory.homLinearEquiv` for a full
subcategory `P.FullSubcategory`. -/
def homLinearIsometryEquiv {R : Type*} [Semiring R] {P : ObjectProperty C}
    (X Y : P.FullSubcategory)
    [hX : SeminormedAddCommGroup (X ⟶ Y)] [hM : Module R (X ⟶ Y)]
    [SeminormedAddCommGroup (X.obj ⟶ Y.obj)] [Module R (X.obj ⟶ Y.obj)]
    (hadd : ∀ f g : X ⟶ Y, (f + g).hom = f.hom + g.hom := by intros; rfl)
    (hsmul : ∀ (r : R) (f : X ⟶ Y), (r • f).hom = r • f.hom := by intros; rfl)
    (hnorm : ∀ f : X ⟶ Y, ‖f.hom‖ = ‖f‖ := by intros; rfl) :
    (X ⟶ Y) ≃ₗᵢ[R] (X.obj ⟶ Y.obj) :=
  letI : SeminormedAddCommGroup (@Quiver.Hom (InducedCategory C FullSubcategory.obj) _ X Y) := hX
  letI : Module R (@Quiver.Hom (InducedCategory C FullSubcategory.obj) _ X Y) := hM
  InducedCategory.homLinearIsometryEquiv (F := FullSubcategory.obj) X Y hadd hsmul hnorm

/-- Forward evaluation of `CategoryTheory.ObjectProperty.homLinearIsometryEquiv`. -/
@[simp] theorem homLinearIsometryEquiv_apply {R : Type*} [Semiring R] {P : ObjectProperty C}
    {X Y : P.FullSubcategory}
    [SeminormedAddCommGroup (X ⟶ Y)] [Module R (X ⟶ Y)]
    [SeminormedAddCommGroup (X.obj ⟶ Y.obj)] [Module R (X.obj ⟶ Y.obj)]
    (hadd : ∀ f g : X ⟶ Y, (f + g).hom = f.hom + g.hom)
    (hsmul : ∀ (r : R) (f : X ⟶ Y), (r • f).hom = r • f.hom)
    (hnorm : ∀ f : X ⟶ Y, ‖f.hom‖ = ‖f‖) (f : X ⟶ Y) :
    homLinearIsometryEquiv X Y hadd hsmul hnorm f = f.hom := (rfl)

/-- Inverse evaluation of `CategoryTheory.ObjectProperty.homLinearIsometryEquiv`. -/
@[simp] theorem homLinearIsometryEquiv_symm_apply {R : Type*} [Semiring R] {P : ObjectProperty C}
    {X Y : P.FullSubcategory}
    [SeminormedAddCommGroup (X ⟶ Y)] [Module R (X ⟶ Y)]
    [SeminormedAddCommGroup (X.obj ⟶ Y.obj)] [Module R (X.obj ⟶ Y.obj)]
    (hadd : ∀ f g : X ⟶ Y, (f + g).hom = f.hom + g.hom)
    (hsmul : ∀ (r : R) (f : X ⟶ Y), (r • f).hom = r • f.hom)
    (hnorm : ∀ f : X ⟶ Y, ‖f.hom‖ = ‖f‖) (g : X.obj ⟶ Y.obj) :
    (homLinearIsometryEquiv X Y hadd hsmul hnorm).symm g = homMk g := (rfl)

/-- Any full subcategory of a C*-category inherits a C*-category structure. -/
instance instCStarCategoryFullSubcategory (P : ObjectProperty C)
    [Preadditive C] [Linear ℂ C] [DaggerCategory C] [DaggerPreadditive C]
    [DaggerLinear ℂ C] [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C] :
    CStarCategory P.FullSubcategory :=
  InducedCategory.instCStarCategory FullSubcategory.obj

end CategoryTheory.ObjectProperty
