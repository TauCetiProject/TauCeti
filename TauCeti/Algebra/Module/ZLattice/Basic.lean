/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Fundamental domains of integer spans

This file records geometric properties of the standard fundamental domain associated to a basis.
Its convexity makes lattice cells preconnected, so cells crossing the boundary of a set can be
detected by their intersection with the frontier in lattice-point counting arguments.

## Main results

* `ZSpan.convex_fundamentalDomain`: the fundamental domain of a real basis is convex.
* `ZSpan.eq_of_sub_mem_fundamentalDomain`: two integer-span translates placing a point in the
  fundamental domain are equal.
-/

public section

open Module Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- The fundamental domain of a basis is convex: it is cut out by the conditions
`b.repr x i ∈ [0, 1)`, one convex condition per coordinate. -/
theorem _root_.ZSpan.convex_fundamentalDomain (β : Basis ι ℝ E) :
    Convex ℝ (ZSpan.fundamentalDomain β) := by
  intro x hx y hy a t ha ht hat
  rw [ZSpan.mem_fundamentalDomain] at hx hy ⊢
  intro i
  simpa using convex_Ico (0 : ℝ) 1 (hx i) (hy i) ha ht hat

/-- Two vectors in the integer span that translate the same point into the fundamental domain
in subtraction form are equal. -/
theorem _root_.ZSpan.eq_of_sub_mem_fundamentalDomain [Finite ι] (β : Basis ι ℝ E)
    {x w₁ w₂ : E} (hw₁ : w₁ ∈ Submodule.span ℤ (Set.range β))
    (hw₂ : w₂ ∈ Submodule.span ℤ (Set.range β))
    (h₁ : x - w₁ ∈ ZSpan.fundamentalDomain β)
    (h₂ : x - w₂ ∈ ZSpan.fundamentalDomain β) : w₁ = w₂ := by
  have hn₁ : -w₁ ∈ Submodule.span ℤ (Set.range β) := neg_mem hw₁
  have hn₂ : -w₂ ∈ Submodule.span ℤ (Set.range β) := neg_mem hw₂
  have subtype_vadd (w : E) (hw : w ∈ Submodule.span ℤ (Set.range β)) :
      (⟨w, hw⟩ : Submodule.span ℤ (Set.range β)) +ᵥ x = w + x := rfl
  have heq : (⟨-w₁, hn₁⟩ : Submodule.span ℤ (Set.range β)) = ⟨-w₂, hn₂⟩ :=
    (ZSpan.exist_unique_vadd_mem_fundamentalDomain β x).unique
      (by rw [subtype_vadd]; simpa only [sub_eq_add_neg, add_comm] using h₁)
      (by rw [subtype_vadd]; simpa only [sub_eq_add_neg, add_comm] using h₂)
  exact neg_injective (congrArg Subtype.val heq)

end TauCeti
