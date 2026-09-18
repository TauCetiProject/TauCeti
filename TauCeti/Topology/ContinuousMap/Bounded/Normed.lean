/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Norm bounds for bounded continuous functions

This file records norm estimates for operations on bounded continuous functions.
-/

public section

open scoped NNReal BoundedContinuousFunction

namespace TauCeti

variable {T X Y : Type*} [TopologicalSpace T] [NormedAddCommGroup X] [NormedAddCommGroup Y]
  {N : X → Y} {ε : ℝ≥0}

/-- Postcomposition by an `ε`-Lipschitz map `N` has norm at most
`‖N 0‖ + ε * ‖f‖`. -/
theorem norm_boundedContinuousFunction_comp_le (hN : LipschitzWith ε N) (f : T →ᵇ X) :
    ‖f.comp N hN‖ ≤ ‖N 0‖ + ε * ‖f‖ := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun t ↦ ?_
  have h := hN.dist_le_mul (f t) 0
  rw [dist_eq_norm, dist_zero_right] at h
  have ht := f.norm_coe_le_norm t
  have := norm_sub_norm_le (N (f t)) (N 0)
  simpa only [BoundedContinuousFunction.comp_apply] using
    (show ‖N (f t)‖ ≤ ‖N 0‖ + ε * ‖f‖ by
    nlinarith [ε.coe_nonneg])

end TauCeti
