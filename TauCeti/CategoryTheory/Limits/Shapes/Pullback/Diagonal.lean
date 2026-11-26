/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# The kernel pair over a base change that is an isomorphism

Let `f : Y ⟶ X` and `g : Z ⟶ X`. If the base change `pullback.snd f g : Y ×_X Z ⟶ Z` of `f`
along `g` is an isomorphism, then the part of `Y ×_X Y` over `Z` lies in the diagonal of `f`:
the base change of `Y ×_X Y ⟶ X` along `g` factors through `pullback.diagonal f`
(`CategoryTheory.Limits.pullback.fst_eq_comp_diagonal_of_isIso_snd`).
-/

public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {X Y Z : C}

/-- If the base change of `f` along `g` is an isomorphism, then the base change of
`Y ×_X Y ⟶ X` along `g` factors through the diagonal of `f`. -/
theorem pullback.fst_eq_comp_diagonal_of_isIso_snd (f : Y ⟶ X) (g : Z ⟶ X) [HasPullback f f]
    [HasPullback (pullback.fst f f ≫ f) g] [HasPullback f g] [IsIso (pullback.snd f g)] :
    pullback.fst (pullback.fst f f ≫ f) g =
      (pullback.fst (pullback.fst f f ≫ f) g ≫ pullback.fst f f) ≫ pullback.diagonal f := by
  set k := pullback.fst (pullback.fst f f ≫ f) g
  set h := pullback.snd (pullback.fst f f ≫ f) g
  -- The two projections of `k` to `Y` agree, as both are determined by `h` through the
  -- isomorphism `Y ×_X Z ⟶ Z`.
  have e : ∀ π : pullback f f ⟶ Y, π ≫ f = pullback.fst f f ≫ f →
      k ≫ π = h ≫ inv (pullback.snd f g) ≫ pullback.fst f g := by
    intro π hπ
    have hl : pullback.lift (k ≫ π) h (by rw [Category.assoc, hπ]; exact pullback.condition) =
        h ≫ inv (pullback.snd f g) := by
      rw [← cancel_mono (pullback.snd f g)]
      simp
    rw [← Category.assoc, ← hl, pullback.lift_fst]
  have key : k ≫ pullback.fst f f = k ≫ pullback.snd f f := by
    rw [e _ rfl, e _ pullback.condition.symm]
  apply pullback.hom_ext <;> simp [key]

end CategoryTheory.Limits
