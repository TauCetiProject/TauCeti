/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Weighted ultrametric bounds on finite sums

Mathlib's `Valuation.map_sum_le` bounds the value of a finite sum by a common bound on the values
of its terms. This file records the weighted form: if every term satisfies `v (f i) * c ≤ B`, then
so does the sum. Weighted bounds of this shape arise when estimating the terms of polynomial
expressions against a varying scale, as in `TauCeti/RingTheory/Valuation/Polynomial.lean`.

## Main results

* `Valuation.map_sum_mul_le`: the ultrametric bound on a finite sum, with every term weighted by a
  common factor.
-/

public section

namespace Valuation

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

/-- The ultrametric bound on a finite sum, with every term weighted by a common factor `c`. -/
theorem map_sum_mul_le {ι : Type*} {s : Finset ι} {f : ι → R} {c B : Γ₀}
    (h : ∀ i ∈ s, v (f i) * c ≤ B) : v (∑ i ∈ s, f i) * c ≤ B := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.sum_cons]
    refine (mul_le_mul_left (v.map_add _ _) c).trans ?_
    rw [max_mul]
    exact max_le (h i (by simp)) (ih fun j hj ↦ h j (by simp [hj]))

end Valuation

end
