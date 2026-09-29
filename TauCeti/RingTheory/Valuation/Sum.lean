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

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)

/-- The ultrametric bound on a finite sum, with every term weighted by a common factor `c`. -/
theorem map_sum_mul_le {ι : Type*} {s : Finset ι} {f : ι → R} {c B : Γ₀}
    (h : ∀ i ∈ s, v (f i) * c ≤ B) : v (∑ i ∈ s, f i) * c ≤ B := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [← le_div_iff₀ (zero_lt_iff.mpr hc)]
    exact v.map_sum_le fun i hi ↦ (le_div_iff₀ (zero_lt_iff.mpr hc)).mpr (h i hi)

end Valuation

end
