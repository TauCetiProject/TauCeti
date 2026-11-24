/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Closed balls form a basis of an ultrametric space

In an ultrametric space every closed ball of positive radius is open, so the closed balls of
positive radius form a basis of the topology.

## Main results

* `IsUltrametricDist.isTopologicalBasis_closedBall`: the closed balls of positive radius form a
  basis of the topology.
-/

public section

open Set Metric

namespace IsUltrametricDist

variable {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X]

/-- In an ultrametric space, the closed balls of positive radius form a basis of the topology. -/
theorem isTopologicalBasis_closedBall :
    TopologicalSpace.IsTopologicalBasis {s : Set X | ∃ x, ∃ r > 0, s = closedBall x r} :=
  TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    (by rintro _ ⟨x, r, hr, rfl⟩; exact isOpen_closedBall _ hr.ne') fun x u hx hu ↦ by
      obtain ⟨ε, hε, hεu⟩ := Metric.isOpen_iff.1 hu x hx
      exact ⟨closedBall x (ε / 2), ⟨x, ε / 2, half_pos hε, rfl⟩,
        mem_closedBall_self (by positivity), (closedBall_subset_ball (half_lt_self hε)).trans hεu⟩

end IsUltrametricDist
