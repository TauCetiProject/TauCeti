/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Congruence for cochain complexes constructed from differentials

`CochainComplex.of_congr` identifies complexes constructed by `CochainComplex.of` when their
objects are equal and their differentials agree heterogeneously.
-/

public section

open CategoryTheory

namespace CochainComplex

/-- Two complexes built by `CochainComplex.of` are equal when their objects are equal and their
differentials agree up to that equality. -/
theorem of_congr {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
    {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]
    {Y Y' : α → C} {δ : ∀ n, Y n ⟶ Y (n + 1)} {δ' : ∀ n, Y' n ⟶ Y' (n + 1)}
    (h : ∀ n, δ n ≫ δ (n + 1) = 0) (h' : ∀ n, δ' n ≫ δ' (n + 1) = 0) (hY : Y = Y')
    (hδ : HEq δ δ') : of Y δ h = of Y' δ' h' := by
  subst hY
  cases hδ
  rfl

end CochainComplex
