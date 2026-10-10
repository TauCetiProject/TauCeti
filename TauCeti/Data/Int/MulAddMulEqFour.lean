/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Positive integer solutions of `αβ + γδ = 4`

The equation `αβ + γδ = 4` has exactly eight solutions in positive integers: one of the products
is `1` and the other `3`, or both products are `2`. Every factor is then at most `3`, so the
solutions are found by a finite search.
-/

public section

namespace TauCeti.Int

/-- The positive integer solutions of `αβ + γδ = 4`: either `αβ = 1` and `γδ = 3`, or `αβ = 3` and
`γδ = 1`, or `αβ = γδ = 2`. -/
theorem cases_of_mul_add_mul_eq_four {α β γ δ : ℤ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hδ : 0 < δ) (hsum : α * β + γ * δ = 4) :
    α = 1 ∧ β = 1 ∧ (γ = 1 ∧ δ = 3 ∨ γ = 3 ∧ δ = 1) ∨
      (α = 1 ∧ β = 3 ∨ α = 3 ∧ β = 1) ∧ γ = 1 ∧ δ = 1 ∨
      (α = 1 ∧ β = 2 ∨ α = 2 ∧ β = 1) ∧ (γ = 1 ∧ δ = 2 ∨ γ = 2 ∧ δ = 1) := by
  have hα₃ : α ≤ 3 := by nlinarith
  have hβ₃ : β ≤ 3 := by nlinarith
  have hγ₃ : γ ≤ 3 := by nlinarith
  have hδ₃ : δ ≤ 3 := by nlinarith
  interval_cases α <;> interval_cases β <;> interval_cases γ <;> interval_cases δ <;> omega

end TauCeti.Int
