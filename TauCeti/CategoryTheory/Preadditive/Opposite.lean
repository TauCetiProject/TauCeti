/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Additivity of the double-opposite equivalence

The double-opposite functors `CategoryTheory.unopUnop` and `CategoryTheory.opOp` are additive
by Mathlib's `CategoryTheory.unop_add` and `CategoryTheory.op_add`. The two directions of
`CategoryTheory.opOpEquivalence` are additive as well, using
`CategoryTheory.opOpEquivalence_functor` and `CategoryTheory.Equivalence.inverse_additive`.
-/

public section

namespace CategoryTheory

variable (C : Type*) [Category* C] [Preadditive C]

/-- The functor from the double opposite of a preadditive category is additive. -/
instance unopUnop_additive : (unopUnop C).Additive where
  map_add {_ _ _ _} := by simp only [unopUnop_map, unop_add]

/-- The functor from a preadditive category to its double opposite is additive. -/
instance opOp_additive : (opOp C).Additive where
  map_add {_ _ _ _} := by simp only [opOp_map, op_add]

/-- The forward functor of the double-opposite equivalence is additive. -/
instance opOpEquivalence_functor_additive : (opOpEquivalence C).functor.Additive := by
  rw [opOpEquivalence_functor]
  infer_instance

/-- The canonical inverse functor from a category to its double opposite is additive. -/
instance opOpEquivalence_symm_functor_additive : (opOpEquivalence C).symm.functor.Additive :=
  Equivalence.inverse_additive (opOpEquivalence C)

end CategoryTheory
