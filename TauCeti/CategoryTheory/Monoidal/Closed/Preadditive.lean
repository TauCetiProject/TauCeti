/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Closed braided preadditive categories are monoidal preadditive

In a closed braided monoidal category, tensoring on either side with a fixed object is a left
adjoint, so it preserves binary coproducts. In a preadditive category, binary coproducts are
binary biproducts, and a functor preserving them is additive. Hence the tensor product of
morphisms is additive in each variable: the category is `MonoidalPreadditive`.

This applies to categories such as sheaves of modules, whose monoidal structure is constructed
abstractly (for instance by localization) rather than from a bilinear formula on morphisms.

## Main declaration

* `TauCeti.monoidalPreadditive_of_monoidalClosed`.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

/-- A closed braided monoidal category which is preadditive with binary coproducts is monoidal
preadditive: whiskering on either side is additive. -/
theorem monoidalPreadditive_of_monoidalClosed (D : Type*) [Category* D] [Preadditive D]
    [HasBinaryCoproducts D] [MonoidalCategory D] [BraidedCategory D] [MonoidalClosed D] :
    MonoidalPreadditive D := by
  let _ : HasBinaryBiproducts D := HasBinaryBiproducts.of_hasBinaryCoproducts
  have (X : D) : (tensorLeft X).Additive :=
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft X)
    Functor.additive_of_preservesBinaryBiproducts _
  have (X : D) : (tensorRight X).Additive :=
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorRight X)
    Functor.additive_of_preservesBinaryBiproducts _
  exact
    { whiskerLeft_zero := (tensorLeft _).map_zero _ _
      zero_whiskerRight := (tensorRight _).map_zero _ _
      whiskerLeft_add _ _ := (tensorLeft _).map_add
      add_whiskerRight _ _ := (tensorRight _).map_add }

end TauCeti
