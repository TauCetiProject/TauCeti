/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Rescaling power series

This file records general facts about Mathlib's coefficientwise rescaling
`PowerSeries.rescale` of power series.

## Main results

* `PowerSeries.rescale_C`: rescaling the variable fixes constant power series.
-/

public section

namespace PowerSeries

/-- Rescaling the power-series variable fixes constant power series. -/
@[simp]
theorem rescale_C {R : Type*} [CommSemiring R] (a b : R) :
    rescale a (C b) = C b := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h <;> simp [h]

end PowerSeries
