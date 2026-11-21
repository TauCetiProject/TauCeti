/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs

/-!
# Functions changing sign on a two-element orbit

Let `σ` be a map without fixed points on a type `α` whose elements are `a` and `σ a`. A function
`α → R` that changes sign under `σ` (`g (σ a') = -g a'`) is determined by its value at `a`, and
that value can be any element of `R`. So evaluation at `a` is a bijection from the functions
changing sign under `σ` onto `R` (`TauCeti.eval_bijective_of_mem_iff_apply_eq_neg`), stated for
any submodule of `α → R` with exactly these functions as elements.

This is the common rank-one argument behind the sign module of a fibre of a double cover
(`TauCeti.signFiberEquiv`, with `σ` the deck involution) and the orientation line of a vector
space (`Orientation.orientationLineEquiv`, with `σ` the negation of orientations).
-/

public section

namespace TauCeti

variable {R : Type*} [Ring R] {α : Type*}

/-- Let `σ` have no fixed points on a type whose elements are `a` and `σ a`. On a submodule of the
functions `α → R` whose elements are exactly the functions changing sign under `σ`, evaluation at
`a` is bijective. -/
theorem eval_bijective_of_mem_iff_apply_eq_neg {σ : α → α} (hfix : ∀ a', σ a' ≠ a') {a : α}
    (hcases : ∀ a', a' = a ∨ a' = σ a) {S : Submodule R (α → R)}
    (hS : ∀ g, g ∈ S ↔ ∀ a', g (σ a') = -g a') :
    Function.Bijective fun g : S ↦ (g : α → R) a := by
  classical
  have hσσ : σ (σ a) = a := (hcases _).resolve_right (hfix _)
  refine ⟨fun g g' hg ↦ Subtype.ext (funext fun a' ↦ ?_), fun r ↦ ?_⟩
  · rcases hcases a' with rfl | rfl
    · exact hg
    · rw [(hS g).1 g.property, (hS g').1 g'.property]
      exact congrArg Neg.neg hg
  · refine ⟨⟨fun a' ↦ if a' = a then r else -r, (hS _).2 fun a' ↦ ?_⟩, by simp⟩
    rcases hcases a' with rfl | rfl
    · simp [hfix]
    · simp [hσσ, hfix]

end TauCeti
