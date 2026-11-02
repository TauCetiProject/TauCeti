/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Additive valuations of power series coefficients

An additive valuation `v` on the coefficient ring satisfies the ultrametric inequality
`min (v x) (v y) ≤ v (x + y)` (`AddValuation.map_add`). Since taking a coefficient is additive,
the coefficients of a sum of power series satisfy the same inequality. This is the coefficientwise
estimate behind lower bounds for the Newton polygon of a sum.

## Main results

* `PowerSeries.min_addValuation_coeff_le_addValuation_coeff_add`:
  `min (v (coeff n f)) (v (coeff n g)) ≤ v (coeff n (f + g))`.
-/

public section

namespace PowerSeries

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ₀]

/-- The ultrametric inequality for the coefficients of a sum of power series. -/
theorem min_addValuation_coeff_le_addValuation_coeff_add (v : AddValuation R Γ₀) (f g : R⟦X⟧)
    (n : ℕ) : min (v (coeff n f)) (v (coeff n g)) ≤ v (coeff n (f + g)) := by
  simpa only [map_add] using v.map_add (coeff n f) (coeff n g)

end PowerSeries
