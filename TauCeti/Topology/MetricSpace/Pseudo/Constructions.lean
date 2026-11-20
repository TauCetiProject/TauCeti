/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Distances on `ℝ≥0`

On `ℝ≥0`, the distance from `a` to `b ≥ a` is `b - a` (`NNReal.dist_eq_sub_of_le`), next to
Mathlib's `NNReal.dist_eq`.
-/

public section

/-- On `ℝ≥0`, the distance from `a` to `b ≥ a` is `b - a`. -/
theorem NNReal.dist_eq_sub_of_le {a b : NNReal} (h : a ≤ b) : dist a b = (b : ℝ) - a := by
  rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h))]
