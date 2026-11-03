/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Limits and colimits under tensoring

The left unitor identifies tensoring on the left by the tensor unit with the identity functor.
Thus this functor preserves colimits, without any closedness assumption on the monoidal category.
This allows constructions that require tensoring to preserve coproducts to be used with the unit.

When tensoring with an object `U` on one side preserves a limit `c`, morphisms into the tensor
product of `U` with `c.pt` are determined by their composites with the whiskered legs of `c`;
dually for colimits.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe w w' v u

namespace TauCeti

/-- Tensoring on the left with the tensor unit preserves colimits, via
`MonoidalCategory.leftUnitorNatIso`. -/
instance preservesColimits_tensorUnitLeft (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    PreservesColimitsOfSize.{w, w'} (tensorUnitLeft C) :=
  preservesColimits_of_natIso (leftUnitorNatIso C).symm

end TauCeti

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {J : Type w} [Category.{w'} J] {F : J ⥤ C}

namespace IsLimit

variable {c : Cone F}

/-- If tensoring on the left with `U` preserves the limit `c`, two morphisms into `U ⊗ c.pt`
agree if they agree after each leg `U ◁ c.π.app j`. -/
theorem hom_ext_whiskerLeft (hc : IsLimit c) {U Z : C} [PreservesLimit F (tensorLeft U)]
    {f g : Z ⟶ U ⊗ c.pt} (h : ∀ j, f ≫ U ◁ c.π.app j = g ≫ U ◁ c.π.app j) : f = g :=
  (isLimitOfPreserves (tensorLeft U) hc).hom_ext h

/-- If tensoring on the right with `U` preserves the limit `c`, two morphisms into `c.pt ⊗ U`
agree if they agree after each leg `c.π.app j ▷ U`. -/
theorem hom_ext_whiskerRight (hc : IsLimit c) {U Z : C} [PreservesLimit F (tensorRight U)]
    {f g : Z ⟶ c.pt ⊗ U} (h : ∀ j, f ≫ c.π.app j ▷ U = g ≫ c.π.app j ▷ U) : f = g :=
  (isLimitOfPreserves (tensorRight U) hc).hom_ext h

end IsLimit

namespace IsColimit

variable {c : Cocone F}

/-- If tensoring on the left with `U` preserves the colimit `c`, two morphisms out of
`U ⊗ c.pt` agree if they agree after each leg `U ◁ c.ι.app j`. -/
theorem hom_ext_whiskerLeft (hc : IsColimit c) {U Z : C} [PreservesColimit F (tensorLeft U)]
    {f g : U ⊗ c.pt ⟶ Z} (h : ∀ j, U ◁ c.ι.app j ≫ f = U ◁ c.ι.app j ≫ g) : f = g :=
  (isColimitOfPreserves (tensorLeft U) hc).hom_ext h

/-- If tensoring on the right with `U` preserves the colimit `c`, two morphisms out of
`c.pt ⊗ U` agree if they agree after each leg `c.ι.app j ▷ U`. -/
theorem hom_ext_whiskerRight (hc : IsColimit c) {U Z : C} [PreservesColimit F (tensorRight U)]
    {f g : c.pt ⊗ U ⟶ Z} (h : ∀ j, c.ι.app j ▷ U ≫ f = c.ι.app j ▷ U ≫ g) : f = g :=
  (isColimitOfPreserves (tensorRight U) hc).hom_ext h

end IsColimit

end CategoryTheory.Limits
