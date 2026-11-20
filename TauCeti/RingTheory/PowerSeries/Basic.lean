/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Basic lemmas on formal power series

This file records basic `@[simp]` lemmas on univariate formal power series `R⟦X⟧` missing from
`Mathlib.RingTheory.PowerSeries.Basic`, specializing the corresponding multivariate statements.

## Main results

* `PowerSeries.constantCoeff_map`: the constant coefficient of `PowerSeries.map f p` is
  `f (constantCoeff p)`.
-/

public section

namespace PowerSeries

variable {R S : Type*} [Semiring R] [Semiring S]

/-- The constant coefficient of `PowerSeries.map f p` is `f (constantCoeff p)`. -/
@[simp]
theorem constantCoeff_map (f : R →+* S) (p : R⟦X⟧) :
    constantCoeff (map f p) = f (constantCoeff p) :=
  MvPowerSeries.constantCoeff_map f p

end PowerSeries
