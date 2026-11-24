/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Pullback squares and postcomposition with a monomorphism

A pullback square `IsPullback fst snd f g` stays a pullback square after postcomposing the cospan
`f`, `g` with a monomorphism `i` (`CategoryTheory.IsPullback.comp_mono`). This is the
`IsPullback` form of Mathlib's `CategoryTheory.Limits.PullbackCone.isLimitOfCompMono`.
-/

public section

namespace CategoryTheory.IsPullback

open Limits

variable {C : Type*} [Category* C] {P X Y Z W : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
  {g : Y ⟶ Z}

/-- A pullback of `f` and `g` is also a pullback of `f ≫ i` and `g ≫ i` for a monomorphism `i`. -/
theorem comp_mono (h : IsPullback fst snd f g) (i : Z ⟶ W) [Mono i] :
    IsPullback fst snd (f ≫ i) (g ≫ i) :=
  .of_isLimit' ⟨by rw [h.w_assoc]⟩ (PullbackCone.isLimitOfCompMono f g i _ h.isLimit)

end CategoryTheory.IsPullback
