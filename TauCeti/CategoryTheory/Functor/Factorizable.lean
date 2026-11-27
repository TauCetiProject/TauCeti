/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Factorizable sequences

The predicate `CategoryTheory.Functor.IsFactorizable` records when a sequence has an
eventual factorization at each stage (Simson, *On pure global dimension of locally finitely
presented Grothendieck categories*, Fund. Math. 96 (1977), Definition 3.1).
-/

public section

universe v u

namespace CategoryTheory.Functor

/-- A sequence is factorizable if, from each stage, some transition factors through every
subsequent transition out of that stage. -/
@[expose]
def IsFactorizable {C : Type u} [Category.{v} C] (F : ℕ ⥤ C) : Prop :=
  ∀ i : ℕ, ∃ (j : ℕ) (hij : i ≤ j), ∀ (k : ℕ) (hjk : j ≤ k),
    ∃ t : F.obj k ⟶ F.obj j,
      F.map (homOfLE (hij.trans hjk)) ≫ t = F.map (homOfLE hij)

end CategoryTheory.Functor
