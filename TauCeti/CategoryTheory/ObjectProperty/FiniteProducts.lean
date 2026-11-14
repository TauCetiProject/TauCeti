/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Inverse images of properties closed under finite products

If a property `P` of objects of `D` is closed under finite products and a functor `F : C ⥤ D`
preserves finite products, then the inverse image `P.inverseImage F` is closed under finite
products.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

/-- The inverse image of a property closed under finite products, along a functor preserving
finite products, is closed under finite products. -/
instance isClosedUnderFiniteProducts_inverseImage {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) [P.IsClosedUnderFiniteProducts] (F : C ⥤ D)
    [PreservesFiniteProducts F] : (P.inverseImage F).IsClosedUnderFiniteProducts :=
  ⟨fun _ _ ↦ inferInstance⟩

end CategoryTheory.ObjectProperty
