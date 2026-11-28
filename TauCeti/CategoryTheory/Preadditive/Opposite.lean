/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Additivity of the double-opposite equivalence

The forward and inverse functors of Mathlib's `CategoryTheory.opOpEquivalence` are additive.
They use Mathlib's `CategoryTheory.unop_add` and `CategoryTheory.Equivalence.inverse_additive`.
-/

public section

namespace CategoryTheory

variable (C : Type*) [Category* C] [Preadditive C]

/-- The canonical functor from the double opposite is additive. -/
instance opOpEquivalence_functor_additive : (opOpEquivalence C).functor.Additive where
  map_add {_ _ f g} := by
    have h : (unopUnop C).map (f + g) = (unopUnop C).map f + (unopUnop C).map g := by
      simp only [unopUnop_map, unop_add]
    exact h

/-- The canonical inverse functor from a category to its double opposite is additive. -/
instance opOpEquivalence_symm_functor_additive : (opOpEquivalence C).symm.functor.Additive :=
  Equivalence.inverse_additive (opOpEquivalence C)

end CategoryTheory
