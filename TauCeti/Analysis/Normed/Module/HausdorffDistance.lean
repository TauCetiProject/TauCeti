/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Topology.Frontier

/-!
# Distances to frontiers in real seminormed spaces

In a real seminormed space, straight line segments are connected and decrease distances to their
endpoints: any segment from a point `x ∈ s` to a point `y ∈ sᶜ` must cross `frontier s` at a point
no farther from `x` than `y`. Consequently, from any point `x ∈ closure s`, the extended and
ordinary distances from `x` to `frontier s` agree with the distances from `x` to `sᶜ`.

This lets distance-to-complement estimates on open sets (for example, preservation of the distance
to `Ωᶜ` under taking holomorphic hulls) transfer directly to distances to the topological boundary
`frontier Ω`.

## Main declarations

* `Metric.infEDist_frontier_of_mem_closure`: for `x ∈ closure s` in a real seminormed space,
  `infEDist x (frontier s) = infEDist x sᶜ`.
* `Metric.infDist_frontier_of_mem_closure`: ordinary-distance form of
  `Metric.infEDist_frontier_of_mem_closure`.
-/

public section

open Metric Set

namespace Metric

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- From any point `x ∈ closure s` in a real seminormed space, the extended distance to
`frontier s` equals the extended distance to `sᶜ`. -/
theorem infEDist_frontier_of_mem_closure {s : Set E} {x : E} (hx : x ∈ closure s) :
    infEDist x (frontier s) = infEDist x sᶜ := by
  -- The segment from `x ∈ s` to any `y ∈ sᶜ` meets `frontier s` no farther from `x` than `y`.
  have hfr_compl : frontier s ⊆ closure sᶜ := by
    rw [frontier_eq_closure_inter_closure]
    exact inter_subset_right
  refine le_antisymm ?_ ?_
  · rw [closure_eq_self_union_frontier] at hx
    rcases hx with hxs | hxf
    · refine le_infEDist.mpr fun y hy ↦ ?_
      obtain ⟨z, hzseg, hzf⟩ := (convex_segment x y).isPreconnected.inter_frontier_nonempty
        ⟨x, left_mem_segment ℝ x y, hxs⟩ ⟨y, right_mem_segment ℝ x y, hy⟩
      refine (infEDist_le_edist_of_mem hzf).trans ?_
      rw [edist_dist, edist_dist]
      exact ENNReal.ofReal_le_ofReal <| by
        simpa [dist_comm] using mem_closedBall.mp (segment_subset_closedBall_left x y hzseg)
    · simp [infEDist_zero_of_mem hxf]
  · rw [← infEDist_closure]
    exact infEDist_anti hfr_compl

/-- From any point `x ∈ closure s` in a real seminormed space, the ordinary distance to
`frontier s` equals the ordinary distance to `sᶜ`. -/
theorem infDist_frontier_of_mem_closure {s : Set E} {x : E} (hx : x ∈ closure s) :
    infDist x (frontier s) = infDist x sᶜ :=
  congrArg ENNReal.toReal (infEDist_frontier_of_mem_closure hx)

end Metric
