/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Completion
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Topology.UniformSpace.Completion

/-!
# Complete balls below the distance to the ideal boundary

In a pseudometric space, a closed ball is complete if its radius is strictly below the extended
distance from its center to the complement of the space's image in its completion. The ambient
closed ball then lies in the image and is complete, and completeness pulls back along the
uniform inducing map into the completion.

For a complete space the ideal boundary is empty, by `TauCeti.range_coe_completion_eq_univ`;
`simp` therefore reduces its extended distance to `⊤`.

## References

* Riccardo Brasca, *ColdingMinicozziTheory*,
  [extended-distance formulation](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/cec8d447).
-/

public section

open Metric Set

namespace TauCeti

/-- A closed ball whose radius is less than the extended distance, in the completion, from its
center to the points of the completion outside the space, is complete. When the space is
complete this set is empty, its extended distance is `⊤`, and every closed ball is complete. -/
theorem isComplete_closedBall_of_ofReal_lt_infEDist_compl_range_coe {X : Type*}
    [PseudoMetricSpace X] {p : X} {R : ℝ}
    (hR : ENNReal.ofReal R < infEDist (p : UniformSpace.Completion X)
      (range ((↑) : X → UniformSpace.Completion X))ᶜ) :
    IsComplete (closedBall p R) := by
  rcases lt_or_ge R 0 with hR0 | hR0
  · rw [closedBall_eq_empty.2 hR0]
    exact isCompact_empty.isComplete
  have hsub : closedBall (p : UniformSpace.Completion X) R ⊆
      range ((↑) : X → UniformSpace.Completion X) := by
    rw [← disjoint_compl_right_iff_subset, ← closedEBall_ofReal hR0]
    exact disjoint_closedEBall_of_lt_infEDist hR
  rw [← isComplete_image_iff (UniformSpace.Completion.isUniformInducing_coe X),
    ← UniformSpace.Completion.coe_isometry.preimage_closedBall p R,
    image_preimage_eq_of_subset hsub]
  exact isClosed_closedBall.isComplete

end TauCeti
