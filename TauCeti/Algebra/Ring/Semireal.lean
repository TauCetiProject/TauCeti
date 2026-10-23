/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Ring.Semireal.Defs

/-! # Square obstructions in semireal rings

Semireality excludes `-1` from the squares. The `Fact` instance supplies this obstruction
when constructing a field by adjoining a square root of `-1`.
-/

public section

namespace TauCeti

/-- In a semireal additive group with multiplication and a distinguished `1`, `-1` is not a square.
This supplies the square obstruction used by quadratic-algebra field instances. -/
instance {R : Type*} [AddGroup R] [One R] [Mul R] [IsSemireal R] :
    Fact (¬ IsSquare (-1 : R)) :=
  ⟨fun h => IsSemireal.not_isSumSq_neg_one R h.isSumSq⟩

end TauCeti
