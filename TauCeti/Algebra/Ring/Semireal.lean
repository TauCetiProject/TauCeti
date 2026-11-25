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

Ring homomorphisms send sums of squares to sums of squares (`IsSumSq.map`), so semireality pulls
back along any ring homomorphism (`IsSemireal.of_ringHom`): a subring of a semireal ring, for
instance a subfield of a real closed field, is semireal.
-/

public section

namespace TauCeti

/-- In a semireal additive group with multiplication and a distinguished `1`, `-1` is not a square.
This supplies the square obstruction used by quadratic-algebra field instances. -/
instance {R : Type*} [AddGroup R] [One R] [Mul R] [IsSemireal R] :
    Fact (¬ IsSquare (-1 : R)) :=
  ⟨fun h => IsSemireal.not_isSumSq_neg_one R h.isSumSq⟩

end TauCeti

/-- A ring homomorphism sends sums of squares to sums of squares. -/
theorem IsSumSq.map {R S F : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F)
    {s : R} (hs : IsSumSq s) : IsSumSq (f s) := by
  induction hs with
  | zero => simp
  | sq_add a _ ih => simpa using IsSumSq.sq_add (f a) ih

/-- Semireality pulls back along ring homomorphisms: if `-1` is not a sum of squares in `S`, it is
not one in `R` either. -/
theorem IsSemireal.of_ringHom {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    [IsSemireal S] [FunLike F R S] [RingHomClass F R S] (f : F) : IsSemireal R :=
  ⟨fun hs h ↦ IsSemireal.one_add_ne_zero (hs.map f) (by simpa using congrArg f h)⟩
