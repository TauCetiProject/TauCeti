/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Equivalences of preadditive categories are additive

A functor between preadditive categories that is an equivalence preserves binary products and zero
morphisms, so it is additive as soon as its source has binary products. Mathlib records this fact
only for the functor of a `MoritaEquivalence`; this file records it as an instance for every
functor that is an equivalence, in particular for both directions `e.functor` and `e.inverse` of
an equivalence `e`. It lets additive constructions such as finite biproducts be transported along
equivalences of module categories, as in the Krull-Schmidt theorem for quiver representations.

Some hypothesis on the source is needed: an equivalence between one-object preadditive categories
is an isomorphism of the multiplicative monoids of their endomorphism rings, which need not be
additive.
-/

public section

namespace CategoryTheory.Functor

open Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A functor between preadditive categories that is an equivalence is additive, provided its
source has binary products. -/
instance additive_of_isEquivalence [Preadditive C] [Preadditive D] [HasBinaryProducts C]
    (F : C ⥤ D) [F.IsEquivalence] : F.Additive :=
  F.additive_of_preserves_binary_products

end CategoryTheory.Functor
