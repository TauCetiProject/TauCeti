/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Interval.Finset.Basic

/-!
# Natural transformations from covering relations

`CategoryTheory.NatTrans.ofCovBy` builds a natural transformation between functors on a locally
finite partial order, such as `Finset ι`, from components that commute with the maps of the
covering relations. It generalizes Mathlib's `CategoryTheory.NatTrans.ofSequence` (Joël Riou,
`Mathlib.CategoryTheory.Functor.OfSequence`) from `ℕ` and its successor maps to any locally finite
partial order, using `le_iff_reflTransGen_covBy`.
-/

public section

namespace CategoryTheory

namespace NatTrans

variable {C : Type*} [Category* C] {α : Type*} [PartialOrder α] [LocallyFiniteOrder α]
  {F G : α ⥤ C} (app : ∀ a, F.obj a ⟶ G.obj a)
  (naturality : ∀ ⦃a b : α⦄ (h : a ⋖ b),
    F.map (homOfLE h.le) ≫ app b = app a ≫ G.map (homOfLE h.le))

/-- A natural transformation between functors on a locally finite partial order, from components
that commute with the maps of the covering relations `a ⋖ b`. Since every inequality is a chain of
covering relations, this suffices for naturality. -/
def ofCovBy : F ⟶ G where
  app := app
  naturality a b f := by
    suffices H : ∀ h : a ≤ b, F.map (homOfLE h) ≫ app b = app a ≫ G.map (homOfLE h) by
      rw [← Subsingleton.elim (homOfLE (leOfHom f)) f]
      exact H (leOfHom f)
    clear f
    intro h
    induction le_iff_reflTransGen_covBy.1 h with
    | refl => simp
    | @tail b c hab hbc ih =>
      simp only [← homOfLE_comp (le_iff_reflTransGen_covBy.2 hab) hbc.le, Functor.map_comp,
        Category.assoc, naturality hbc, reassoc_of% ih]

/-- The components of `NatTrans.ofCovBy` are the given ones. -/
@[simp]
theorem ofCovBy_app (a : α) : (ofCovBy app naturality).app a = app a :=
  (rfl)

end NatTrans

end CategoryTheory
