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

The functor of an equivalence between preadditive categories preserves binary products and zero
morphisms, so it is additive as soon as the source has binary products. Mathlib records this fact
for the functor of a `MoritaEquivalence`; this file records it as an instance for every
equivalence, so that the Grothendieck-group functoriality of additive functors applies to
equivalences of module categories without further hypotheses. The inverse is then additive by
Mathlib's `CategoryTheory.Equivalence.inverse_additive`.
-/

public section

namespace CategoryTheory.Equivalence

open Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The functor of an equivalence between preadditive categories with binary products is
additive. -/
instance functor_additive [Preadditive C] [Preadditive D] [HasBinaryProducts C] (e : C ≌ D) :
    e.functor.Additive :=
  e.functor.additive_of_preserves_binary_products

end CategoryTheory.Equivalence
