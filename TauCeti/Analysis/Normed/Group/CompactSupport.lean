/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Compactly supported maps on normed groups vanish near infinity

The topological support of a compactly supported map on a seminormed group lies inside some ball
around the origin (`HasCompactSupport.exists_pos_le_norm_notMem_tsupport`). This strengthens
Mathlib's `HasCompactSupport.exists_pos_le_norm`, which only gives vanishing of the map itself,
so that it also applies to derivatives of the map.
-/

public section

open Metric

/-- A compactly supported map has topological support inside some open ball of positive radius
around the origin. -/
theorem HasCompactSupport.exists_pos_le_norm_notMem_tsupport {X Y : Type*}
    [SeminormedAddGroup X] [Zero Y] {g : X → Y} (hg : HasCompactSupport g) :
    ∃ R > 0, ∀ x, R ≤ ‖x‖ → x ∉ tsupport g := by
  obtain ⟨R, hR⟩ := hg.isCompact.isBounded.subset_ball 0
  refine ⟨max R 1, by positivity, fun x hx h ↦ ?_⟩
  have := mem_ball_zero_iff.1 (hR h)
  linarith [le_max_left R 1]
