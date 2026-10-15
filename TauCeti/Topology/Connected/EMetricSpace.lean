/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.EMetricSpace.Defs

/-!
# Preconnected subsets of extended metric spaces

This file establishes that points in a preconnected subset of an extended metric space are at
finite distance.

The declaration and proof follow
[Mathlib pull request #41839](https://github.com/leanprover-community/mathlib4/pull/41839),
available under Apache 2.0.
-/

public section

open Set
open scoped ENNReal

namespace TauCeti

/-- Two points in a preconnected subset of an extended metric space are at finite distance. -/
theorem _root_.IsPreconnected.edist_ne_top {X : Type*} [PseudoEMetricSpace X] {s : Set X}
    (hs : IsPreconnected s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) : edist x y ≠ ∞ := by
  have hsub : s ⊆ Metric.eball x ∞ := hs.subset_isClopen
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩ ⟨x, hx, by simp⟩
  have hy' := hsub hy
  rw [Metric.mem_eball] at hy'
  simpa only [edist_comm] using hy'.ne

end TauCeti
