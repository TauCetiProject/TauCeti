/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism

/-!
# Automorphisms in a category

This file contains general bookkeeping lemmas for automorphisms of objects in a category.

## Main results

* `CategoryTheory.Aut.comp_pow_hom_of_comp`: iterating an automorphism that reindexes a
  family of morphisms reindexes that family by the corresponding function iterate.
-/

public section

namespace CategoryTheory.Aut

universe v u

variable {C : Type u} [Category.{v} C] {X Y : C} {ι : Type*}

/-- Iterating an automorphism which reindexes a family of morphisms reindexes that family by the
corresponding function iterate. -/
theorem comp_pow_hom_of_comp (γ : Aut X) (F : ι → (Y ⟶ X)) (s : ι → ι)
    (h : ∀ i, F i ≫ γ.asIso.hom = F (s i)) (m : ℕ) (i : ι) :
    F i ≫ (γ ^ m).asIso.hom = F (s^[m] i) := by
  induction m generalizing i with
  | zero => simp
  | succ m ih => simp [pow_succ, reassoc_of% h, ih]

end CategoryTheory.Aut
