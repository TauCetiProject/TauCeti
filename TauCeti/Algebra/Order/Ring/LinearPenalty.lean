/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith

/-!
# Comparing two choices under two linear penalties

Suppose that the choice `(a₀, d₀)` is at least as good as `(a₁, d₁)` for the objective
`a + s * d`, and `(a₁, d₁)` is at least as good as `(a₀, d₀)` for the objective `a + t * d`, with
a smaller penalty `0 ≤ t < s`. Then `d₀ ≤ d₁` and `a₁ ≤ a₀`: lowering the penalty on `d` can only
increase `d` and decrease `a`. This is the exchange argument behind the monotonicity of minimizers
of a linearly penalized objective in the penalty, for instance of resolvent steps in the time step.

## Main results

* `TauCeti.le_and_le_of_add_mul_le_add_mul`: the comparison above.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Exchange argument for two linear penalties.** If `a₀ + s d₀ ≤ a₁ + s d₁` and
`a₁ + t d₁ ≤ a₀ + t d₀` with `0 ≤ t < s`, then `d₀ ≤ d₁` and `a₁ ≤ a₀`. -/
theorem le_and_le_of_add_mul_le_add_mul {a₀ a₁ d₀ d₁ s t : R} (ht : 0 ≤ t) (hts : t < s)
    (h₀ : a₀ + s * d₀ ≤ a₁ + s * d₁) (h₁ : a₁ + t * d₁ ≤ a₀ + t * d₀) : d₀ ≤ d₁ ∧ a₁ ≤ a₀ := by
  have hd : d₀ ≤ d₁ := by
    by_contra! h
    nlinarith [mul_pos (sub_pos.2 hts) (sub_pos.2 h)]
  exact ⟨hd, by nlinarith [mul_le_mul_of_nonneg_left hd ht]⟩

end TauCeti
