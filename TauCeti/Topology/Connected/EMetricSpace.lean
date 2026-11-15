/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.EMetricSpace.Defs

/-!
# Preconnected subsets of extended pseudometric spaces

This file establishes that points in a preconnected subset of an extended pseudometric space are at
finite distance.

The declaration and proof generalize
[Mathlib pull request #41839](https://github.com/leanprover-community/mathlib4/pull/41839),
available under Apache 2.0, from extended metric spaces to extended pseudometric spaces.
-/

public section

open scoped ENNReal

namespace IsPreconnected

/-- In a preconnected subset of an extended pseudometric space, any two points are at finite
distance. This is Mathlib's `IsPreconnected.edist_ne_top` with `EMetricSpace` weakened to
`PseudoEMetricSpace`. -/
theorem edist_ne_top' {X : Type*} [PseudoEMetricSpace X] {s : Set X}
    (hs : IsPreconnected s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) : edist x y ≠ ∞ := by
  rw [edist_comm, ← lt_top_iff_ne_top, ← Metric.mem_eball]
  exact hs.subset_isClopen Metric.isClopen_eball_top ⟨x, hx, by simp⟩ hy

end IsPreconnected
