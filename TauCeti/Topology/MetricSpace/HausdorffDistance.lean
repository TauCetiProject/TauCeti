/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Distances to sets

For a nonempty set in a pseudometric space, the extended distance `Metric.infEDist x S` equals
`ENNReal.ofReal t` for some `t ≥ 0` exactly when the real distance `Metric.infDist x S` equals `t`
(`Metric.infEDist_eq_ofReal_iff`).
-/

public section

namespace Metric

/-- For a nonempty set in a pseudometric space, the extended distance to it equals a nonnegative
real number exactly when the real distance does. -/
theorem infEDist_eq_ofReal_iff {X : Type*} [PseudoMetricSpace X] {x : X} {S : Set X}
    {t : ℝ} (hS : S.Nonempty) (ht : 0 ≤ t) :
    infEDist x S = ENNReal.ofReal t ↔ infDist x S = t := by
  constructor
  · intro h
    rw [infDist, h, ENNReal.toReal_ofReal ht]
  · intro h
    rw [← h, infDist, ENNReal.ofReal_toReal (infEDist_ne_top hS)]

end Metric
