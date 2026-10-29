/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Left multiples of idempotent endomorphisms

In an `R`-linear category, the left multiples `{e ≫ g}` of an endomorphism `e : X ⟶ X` form the
`R`-submodule `LinearMap.range (Linear.leftComp R X e)` of `X ⟶ X`. For an idempotent `f` and an
endomorphism `e` with `e ≫ f = f` and `f ≫ e = f`, for instance an idempotent `f` below an
idempotent `e`, the submodule of `f` lies in the one of `e`, and strictly unless `f = e`
(`TauCeti.range_leftComp_lt_range_leftComp`). When `X ⟶ X` is an Artinian `R`-module, this bounds
how often an idempotent can be split into smaller ones, as in the existence half of the
Krull-Schmidt theorem.
-/

public section

namespace TauCeti

open CategoryTheory

variable (R : Type*) [Semiring R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]

/-- **Left multiples of a smaller idempotent form a smaller submodule.** If `f` is an idempotent
endomorphism of `X` and `e` an endomorphism of `X` with `e ≫ f = f`, `f ≫ e = f` and `f ≠ e`, then
the left multiples of `f` form a proper submodule of the left multiples of `e`. -/
theorem range_leftComp_lt_range_leftComp {X : C} {e f : X ⟶ X} (hf : f ≫ f = f) (hef : e ≫ f = f)
    (hfe : f ≫ e = f) (hne : f ≠ e) :
    LinearMap.range (Linear.leftComp R X f) < LinearMap.range (Linear.leftComp R X e) := by
  refine lt_of_le_of_ne ?_ fun h ↦ hne ?_
  · rintro _ ⟨g, rfl⟩
    exact ⟨f ≫ g, by simp [reassoc_of% hef]⟩
  · -- If `e = f ≫ g`, then `f = f ≫ e = f ≫ f ≫ g = f ≫ g = e`.
    obtain ⟨g, hg⟩ : e ∈ LinearMap.range (Linear.leftComp R X f) :=
      h ▸ ⟨𝟙 X, Category.comp_id e⟩
    simp only [Linear.leftComp_apply] at hg
    rw [← hfe, ← hg, reassoc_of% hf]

end TauCeti
