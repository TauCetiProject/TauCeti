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

variable {C : Type u} [Category.{v} C]

/-- A sequence is factorizable if, from each stage, some transition factors through every
subsequent transition out of that stage. -/
def IsFactorizable (F : ℕ ⥤ C) : Prop :=
  ∀ i : ℕ, ∃ (j : ℕ) (hij : i ≤ j), ∀ (k : ℕ) (hjk : j ≤ k),
    ∃ t : F.obj k ⟶ F.obj j,
      F.map (homOfLE (hij.trans hjk)) ≫ t = F.map (homOfLE hij)

/-- A factorization bound at each stage makes the sequence factorizable. -/
theorem IsFactorizable.of_exists_factorization {F : ℕ ⥤ C}
    (h : ∀ i : ℕ, ∃ (j : ℕ) (hij : i ≤ j), ∀ (k : ℕ) (hjk : j ≤ k),
      ∃ t : F.obj k ⟶ F.obj j,
        F.map (homOfLE (hij.trans hjk)) ≫ t = F.map (homOfLE hij)) :
    F.IsFactorizable :=
  h

/-- At any stage of a factorizable sequence, some transition factors through all later ones. -/
theorem IsFactorizable.exists_factorization {F : ℕ ⥤ C} (h : F.IsFactorizable) (i : ℕ) :
    ∃ (j : ℕ) (hij : i ≤ j), ∀ (k : ℕ) (hjk : j ≤ k),
      ∃ t : F.obj k ⟶ F.obj j,
        F.map (homOfLE (hij.trans hjk)) ≫ t = F.map (homOfLE hij) :=
  h i

end CategoryTheory.Functor
