/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Base change of a fibre product

Let `X ⟶ S` and `Y ⟶ S` be two objects over `S`, and let `X' ⟶ S'` and `Y' ⟶ S'` be their base
changes along `f : S' ⟶ S`. Then the fibre product `X' ×_{S'} Y'` is the base change of
`X ×_S Y` along `f`, through the morphism `pullback.map` induced by `X' ⟶ X` and `Y' ⟶ Y`
(`CategoryTheory.IsPullback.pullback_map`). In other words, base change preserves fibre
products over the base.
-/

public section

namespace CategoryTheory.IsPullback

open Limits

variable {C : Type*} [Category* C] {S S' X Y X' Y' : C} {f : S' ⟶ S} {pX : X ⟶ S} {pY : Y ⟶ S}
  {pX' : X' ⟶ S'} {pY' : Y' ⟶ S'} {iX : X' ⟶ X} {iY : Y' ⟶ Y}

/-- **Base change preserves fibre products.** If `X' ⟶ S'` and `Y' ⟶ S'` are the base changes of
`X ⟶ S` and `Y ⟶ S` along `f : S' ⟶ S`, then `X' ×_{S'} Y'`, as an object over `S'`, is the base
change of `X ×_S Y` along `f`. -/
theorem pullback_map [HasPullback pX pY] [HasPullback pX' pY']
    (hX : IsPullback pX' iX f pX) (hY : IsPullback pY' iY f pY) :
    IsPullback (pullback.fst pX' pY' ≫ pX')
      (pullback.map pX' pY' pX pY iX iY f hX.w hY.w) f (pullback.fst pX pY ≫ pX) := by
  -- `X' ×_{S'} Y'` is the base change of `X ×_S Y ⟶ X` along `X' ⟶ X`
  have top : IsPullback (pullback.map pX' pY' pX pY iX iY f hX.w hY.w)
      (pullback.fst pX' pY') (pullback.fst pX pY) iX := by
    refine .of_right (h₁₂ := pullback.snd pX pY) ?_ (by simp)
      (IsPullback.of_hasPullback pX pY).flip
    simpa [hX.w] using (IsPullback.of_hasPullback pX' pY').flip.paste_horiz hY.flip
  exact (top.paste_vert hX.flip).flip

end CategoryTheory.IsPullback
