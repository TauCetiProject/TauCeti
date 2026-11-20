/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor

/-!
# Values of the Day convolution unit

In a lawful Day convolution monoidal category `D` over `C ⥤ V`, the unit `𝟙_ D` is interpreted
as the left Kan extension of `𝟙_ V` along the inclusion of `𝟙_ C`, so its value at `d : C` is the
colimit of the constant diagram `𝟙_ V` indexed by the morphisms `𝟙_ C ⟶ d`. We compute this value
in the two extreme cases:

* when `𝟙_ C` has no endomorphism other than the identity, the structure map
  `unitUnit C V D : 𝟙_ V ⟶ ((ι C V D).obj (𝟙_ D)).obj (𝟙_ C)` is an isomorphism;
* when there is no morphism `𝟙_ C ⟶ d`, the value at `d` is an initial object.

We record both for Mathlib's Day functor category `C ⊛⥤ V`, where the structure map is
`DayFunctor.ν`. For the finite-bijection groupoid both cases apply: the unit symmetric sequence is
`𝟙_ V` in level zero and initial in every positive level.

## Main statements

* `LawfulDayConvolutionMonoidalCategoryStruct.isIso_unitUnit` and its specialisation
  `DayFunctor.isIso_ν`: the unit structure map is an isomorphism when `𝟙_ C` has only the
  identity endomorphism.
* `LawfulDayConvolutionMonoidalCategoryStruct.isInitialUnitObj` and its specialisation
  `DayFunctor.isInitialUnitObj`: the unit is initial at objects receiving no morphism from
  `𝟙_ C`.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.MonoidalCategory

open scoped ExternalProduct
open Limits

noncomputable section

namespace LawfulDayConvolutionMonoidalCategoryStruct

variable (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
  [MonoidalCategory C] [MonoidalCategory V]
  (D : Type u₃) [Category.{v₃} D] [MonoidalCategoryStruct D]
  [LawfulDayConvolutionMonoidalCategoryStruct C V D]

/-- If the only endomorphism of `𝟙_ C` is the identity, then the structure map
`unitUnit C V D : 𝟙_ V ⟶ ((ι C V D).obj (𝟙_ D)).obj (𝟙_ C)` is an isomorphism: the unit of a
lawful Day convolution takes the value `𝟙_ V` at `𝟙_ C`. -/
instance isIso_unitUnit [Subsingleton (𝟙_ C ⟶ 𝟙_ C)] : IsIso (unitUnit C V D) := by
  -- With a single endomorphism of `𝟙_ C`, the inclusion of `𝟙_ C` is fully faithful.
  have : (Functor.fromPUnit.{0} (𝟙_ C)).Full :=
    ⟨fun _ ↦ ⟨Discrete.eqToHom (Subsingleton.elim _ _), Subsingleton.elim (α := 𝟙_ C ⟶ 𝟙_ C) _ _⟩⟩
  exact (isPointwiseLeftKanExtensionUnitUnit C V D (𝟙_ C)).isIso_hom_app (X := ⟨⟨⟩⟩)

/-- If there is no morphism `𝟙_ C ⟶ d`, then the unit of a lawful Day convolution takes an
initial value at `d`. -/
def isInitialUnitObj {d : C} [IsEmpty (𝟙_ C ⟶ d)] :
    IsInitial (((ι C V D).obj (𝟙_ D)).obj d) :=
  have : IsEmpty (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) :=
    ⟨fun f ↦ IsEmpty.false (α := 𝟙_ C ⟶ d) f.hom⟩
  isColimitEquivIsInitialOfIsEmpty _ _ (isPointwiseLeftKanExtensionUnitUnit C V D d)

end LawfulDayConvolutionMonoidalCategoryStruct

namespace DayFunctor

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape
      (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape
      (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

/-- If the only endomorphism of `𝟙_ C` is the identity, then the canonical map
`ν : 𝟙_ V ⟶ (𝟙_ (C ⊛⥤ V)).functor.obj (𝟙_ C)` is an isomorphism: the Day convolution unit takes
the value `𝟙_ V` at `𝟙_ C`. -/
instance isIso_ν [Subsingleton (𝟙_ C ⟶ 𝟙_ C)] : IsIso (ν C V) :=
  LawfulDayConvolutionMonoidalCategoryStruct.isIso_unitUnit C V (C ⊛⥤ V)

/-- If there is no morphism `𝟙_ C ⟶ d`, then the Day convolution unit takes an initial value
at `d`. -/
def isInitialUnitObj {d : C} [IsEmpty (𝟙_ C ⟶ d)] :
    IsInitial ((𝟙_ (C ⊛⥤ V)).functor.obj d) :=
  LawfulDayConvolutionMonoidalCategoryStruct.isInitialUnitObj C V (C ⊛⥤ V)

end DayFunctor

end

end CategoryTheory.MonoidalCategory
