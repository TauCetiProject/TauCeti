/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Cover

/-!
# Covers in seminormed groups

## Main results

* `Metric.IsCover.exists_norm_sub_le`: every point of a set covered by `N` at radius `ε` lies
  within `ε` of some point of `N`, stated with the norm of the difference.
-/

public section

open Metric

/-- A point of a set covered by `N` at radius `ε` is within `ε` of some point of `N`. -/
theorem Metric.IsCover.exists_norm_sub_le {E : Type*} [SeminormedAddCommGroup E]
    {ε : NNReal} {s N : Set E} (h : IsCover ε s N) {x : E} (hx : x ∈ s) :
    ∃ u ∈ N, ‖x - u‖ ≤ ε := by
  obtain ⟨u, hu, hxu⟩ : ∃ u : E, u ∈ N ∧ x ∈ closedBall u ε := by
    simpa only [Set.mem_iUnion, exists_prop] using h.subset_iUnion_closedBall hx
  exact ⟨u, hu, by simpa only [mem_closedBall, dist_eq_norm] using hxu⟩
