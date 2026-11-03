/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential

/-!
# Shifting the argument of a decaying real exponential

The decay profile `exp (-c (t - R))`, normalised to equal `1` at `t = R`, is the radial profile
`exp (-c t)` rescaled by the constant amplitude `exp (c R)`. This is how exponential decay
estimates past a radius `R` are converted into bounds of the form `K exp (-c t)`.

## Main declarations

* `TauCeti.exp_neg_mul_sub`: `exp (-c (t - R)) = exp (c R) exp (-c t)`.
-/

public section

namespace TauCeti

/-- Shifting the radius in an exponential: `exp (-c (t - R)) = exp (c R) exp (-c t)`. -/
theorem exp_neg_mul_sub (c t R : ℝ) :
    Real.exp (-(c * (t - R))) = Real.exp (c * R) * Real.exp (-(c * t)) := by
  rw [← Real.exp_add]
  ring_nf

end TauCeti
