/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# The kernel pair over a base change that is a monomorphism

Let `f : Y ⟶ X` and `g : Z ⟶ X`. If the base change `pullback.snd f g : Y ×_X Z ⟶ Z` of `f`
along `g` is a monomorphism (for instance an isomorphism), then the part of `Y ×_X Y` over `Z`
lies in the diagonal of `f`: the base change of `Y ×_X Y ⟶ X` along `g` factors through
`pullback.diagonal f` (`CategoryTheory.Limits.pullback.fst_eq_comp_diagonal_of_mono_snd`).
-/

public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {X Y Z : C}

/-- If the base change of `f` along `g` is a monomorphism, then the base change of
`Y ×_X Y ⟶ X` along `g` factors through the diagonal of `f`. -/
theorem pullback.fst_eq_comp_diagonal_of_mono_snd (f : Y ⟶ X) (g : Z ⟶ X) [HasPullback f f]
    [HasPullback (pullback.fst f f ≫ f) g] [HasPullback f g] [Mono (pullback.snd f g)] :
    pullback.fst (pullback.fst f f ≫ f) g =
      (pullback.fst (pullback.fst f f ≫ f) g ≫ pullback.fst f f) ≫ pullback.diagonal f := by
  set k := pullback.fst (pullback.fst f f ≫ f) g
  set h := pullback.snd (pullback.fst f f ≫ f) g
  -- The two projections of `k` to `Y` agree: together with `h` they lift to `Y ×_X Z`, and
  -- the two lifts agree after the monomorphism `Y ×_X Z ⟶ Z`.
  have hl : pullback.lift (k ≫ pullback.fst f f) h
        (by rw [Category.assoc]; exact pullback.condition) =
      pullback.lift (k ≫ pullback.snd f f) h
        (by rw [Category.assoc, ← pullback.condition]; exact pullback.condition) := by
    rw [← cancel_mono (pullback.snd f g)]
    simp
  have key : k ≫ pullback.fst f f = k ≫ pullback.snd f f := by
    simpa using congrArg (· ≫ pullback.fst f g) hl
  apply pullback.hom_ext <;> simp [key]

end CategoryTheory.Limits
