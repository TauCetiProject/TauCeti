/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: the Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The supporting line of `x ↦ x * log x`

The function `x ↦ x * log x` of Mathlib's `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog` is
strictly convex on the nonnegative reals. This file records the estimate about it that the
optimisation arguments over matrices and measures use: the tangent line at a positive point `a` lies
below the graph at every nonnegative point `u`, with the slope `log a + 1` of Mathlib's
`Real.deriv_mul_log`.

## Main results

* `TauCeti.Real.mul_log_sub_mul_log_ge`: for `0 < a` and `0 ≤ u`,
  `u * log u - a * log a ≥ (u - a) * (log a + 1)`.

The estimate is stated for `u = 0` as well, where the convention `0 * log 0 = 0` of Mathlib makes
its left side `-a * log a`, so that it applies at the boundary of the domain without a case split.
It is
proved from `Real.self_sub_one_le_mul_log` after the change of variables `u = a * v`, which puts the
claim in the form `-v * log v ≤ 1 - v` that Mathlib records.

## Roadmap role

This is the estimate used by the entropy-minimiser step of the diagonal-scaling target
`exists-sinkhorn-scaling` of `TauCetiRoadmap/OptimalTransport`, Layer 13:
`Matrix.pos_of_relEntropy_minOn` in `TauCeti/Data/Matrix/Scaling.lean` bounds the loss of each cell
that gives up mass, and the gain of the cell that receives it, by this supporting line.
-/

public section

namespace TauCeti.Real

/-- The supporting line of the convex function `u ↦ u * log u` at a positive point `a` lies below
the graph at every nonnegative `u`: with the slope `log a + 1` of `Real.deriv_mul_log`,
`u * log u - a * log a ≥ (u - a) * (log a + 1)`. -/
theorem mul_log_sub_mul_log_ge (a u : ℝ) (ha : 0 < a) (hu : 0 ≤ u) :
    u * Real.log u - a * Real.log a ≥ (u - a) * (Real.log a + 1) := by
  rcases lt_or_eq_of_le hu with hu' | hu0
  · have key : u * Real.log u - a * Real.log a - (u - a) * (Real.log a + 1)
        = a * ((u / a) * Real.log (u / a) - (u / a - 1)) := by
      rw [Real.log_div (x := u) (y := a) hu'.ne' ha.ne']
      field_simp
      ring
    have h1 : 0 ≤ (u / a) * Real.log (u / a) - (u / a - 1) :=
      sub_nonneg.mpr (Real.self_sub_one_le_mul_log (le_of_lt (div_pos hu' ha)))
    have h2 := mul_nonneg (le_of_lt ha) h1
    linarith
  · subst hu0
    simp only [Real.log_zero, zero_mul]
    linarith

end TauCeti.Real
