/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Lifting properties and limits of towers

Let `⋯ ⟶ X 2 ⟶ X 1 ⟶ X 0` be a tower given by morphisms `p n : X (n + 1) ⟶ X n`, and let `c` be a
limit cone of the functor `Functor.ofOpSequence p : ℕᵒᵖ ⥤ C`. If a morphism `i` has the left
lifting property with respect to every `p n`, then it has the left lifting property with respect
to the projection `c.π.app (op 0) : c.pt ⟶ X 0`
(`CategoryTheory.hasLiftingProperty_π_app_zero_of_isLimit`). The proof applies Mathlib's
transfinite-composition lifting theorem in the opposite category.

This is the dual of the stability of left lifting properties under transfinite compositions. In a
model category it says that the limit of a tower of fibrations is a fibration over the bottom of
the tower; in particular a limit of a tower of fibrations between fibrant objects is fibrant.
-/

public section

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category* C] {A B : C} (i : A ⟶ B) {X : ℕ → C} (p : ∀ n, X (n + 1) ⟶ X n)

/-- **Lifting properties pass to limits of towers.** If `i` has the left lifting property with
respect to every morphism `p n : X (n + 1) ⟶ X n` of a tower, then it has the left lifting property
with respect to the projection from a limit of the tower to its bottom `X 0`. -/
theorem hasLiftingProperty_π_app_zero_of_isLimit [∀ n, HasLiftingProperty i (p n)]
    {c : Cone (Functor.ofOpSequence p)} (hc : IsLimit c) :
    HasLiftingProperty i (c.π.app (op 0)) := by
  have h := HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
    (isColimitCoconeRightOpOfCone _ hc) (p := i.op) (fun n _ ↦ by
      -- Express the opposite functor map as the opposite of a tower transition.
      change HasLiftingProperty
        (((Functor.ofOpSequence p).map (homOfLE (Nat.le_succ n)).op).op) i.op
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact (inferInstance : HasLiftingProperty i (p n)).op)
  exact h.unop

end CategoryTheory
