/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Sums.Basic

/-!
# The inclusions into a disjoint union of categories

The inclusions `CategoryTheory.Sum.inl_ C D : C ⥤ C ⊕ D` and `CategoryTheory.Sum.inr_ C D` are
fully faithful (`CategoryTheory.Sum.fullyFaithfulInl`, `CategoryTheory.Sum.fullyFaithfulInr`).
-/

public section

namespace CategoryTheory.Sum

universe v₁ v₂ u₁ u₂

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

/-- The inclusion of the left summand is fully faithful. A morphism `inl X ⟶ inl Y` of `C ⊕ D`
is by definition an element of `ULift (X ⟶ Y)`, and its preimage is the underlying morphism. -/
def fullyFaithfulInl : (inl_ C D).FullyFaithful where
  preimage f := f.down

/-- The inclusion of the right summand is fully faithful. A morphism `inr X ⟶ inr Y` of `C ⊕ D`
is by definition an element of `ULift (X ⟶ Y)`, and its preimage is the underlying morphism. -/
def fullyFaithfulInr : (inr_ C D).FullyFaithful where
  preimage f := f.down

instance : (inl_ C D).Full := (fullyFaithfulInl C D).full

instance : (inl_ C D).Faithful := (fullyFaithfulInl C D).faithful

instance : (inr_ C D).Full := (fullyFaithfulInr C D).full

instance : (inr_ C D).Faithful := (fullyFaithfulInr C D).faithful

end CategoryTheory.Sum
