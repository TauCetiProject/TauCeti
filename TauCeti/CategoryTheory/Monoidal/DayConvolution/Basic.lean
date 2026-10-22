/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.DayConvolution

/-!
# Whiskerings and inverse associators under a lawful Day convolution structure

For a lawful Day convolution monoidal structure on `D`, Mathlib proves that the faithful functor
`ι : D ⥤ C ⥤ V` carries tensor products of morphisms and associators to their Day convolution
counterparts. This file adds the corresponding statements for left and right whiskerings and for
inverse associators. They are used to transfer the Day convolution braiding to `C ⊛⥤ V`.

## Main statements

* `LawfulDayConvolutionMonoidalCategoryStruct.ι_map_whiskerLeft_eq_tensorHom` and
  `LawfulDayConvolutionMonoidalCategoryStruct.ι_map_whiskerRight_eq_tensorHom`: `ι` carries
  whiskerings to Day convolutions with an identity.
* `LawfulDayConvolutionMonoidalCategoryStruct.ι_map_associator_inv_eq_associator_inv`: `ι`
  carries the inverse associator to the inverse Day convolution associator.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.MonoidalCategory

open scoped ExternalProduct

noncomputable section

namespace LawfulDayConvolutionMonoidalCategoryStruct

variable (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
  [MonoidalCategory C] [MonoidalCategory V]
  (D : Type u₃) [Category.{v₃} D] [MonoidalCategoryStruct D]
  [LawfulDayConvolutionMonoidalCategoryStruct C V D]

attribute [local instance] convolution convolution₂ convolution₂'

/-- `ι` carries a left whiskering `d ◁ f` to the Day convolution of `𝟙` and `ι.map f`. -/
lemma ι_map_whiskerLeft_eq_tensorHom (d : D) {d' d'' : D} (f : d' ⟶ d'') :
    (ι C V D).map (d ◁ f) = DayConvolution.map (𝟙 ((ι C V D).obj d)) ((ι C V D).map f) := by
  apply DayConvolution.corepresentableBy ((ι C V D).obj d) ((ι C V D).obj d')
    |>.homEquiv.injective
  dsimp
  ext ⟨x, y⟩
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, tensor_obj,
    DayConvolution.corepresentableBy_homEquiv_apply_app, DayConvolution.unit_app_map_app,
    NatTrans.id_app, id_tensorHom]
  exact convolutionExtensionUnit_comp_ι_map_whiskerLeft_app V d f x y

/-- `ι` carries a right whiskering `f ▷ d''` to the Day convolution of `ι.map f` and `𝟙`. -/
lemma ι_map_whiskerRight_eq_tensorHom {d d' : D} (f : d ⟶ d') (d'' : D) :
    (ι C V D).map (f ▷ d'') = DayConvolution.map ((ι C V D).map f) (𝟙 ((ι C V D).obj d'')) := by
  apply DayConvolution.corepresentableBy ((ι C V D).obj d) ((ι C V D).obj d'')
    |>.homEquiv.injective
  dsimp
  ext ⟨x, y⟩
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, tensor_obj,
    DayConvolution.corepresentableBy_homEquiv_apply_app, DayConvolution.unit_app_map_app,
    NatTrans.id_app, tensorHom_id]
  exact convolutionExtensionUnit_comp_ι_map_whiskerRight_app C V f d'' x y

/-- `ι` carries the inverse associator to the inverse Day convolution associator. -/
lemma ι_map_associator_inv_eq_associator_inv (d d' d'' : D)
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)] :
    (ι C V D).map (α_ d d' d'').inv =
      (DayConvolution.associator ((ι C V D).obj d) ((ι C V D).obj d')
        ((ι C V D).obj d'')).inv := by
  rw [← cancel_epi ((ι C V D).map (α_ d d' d'').hom), ← Functor.map_comp, Iso.hom_inv_id,
    Functor.map_id, ι_map_associator_hom_eq_associator_hom, Iso.hom_inv_id]

end LawfulDayConvolutionMonoidalCategoryStruct

end

end CategoryTheory.MonoidalCategory
