/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen

/-!
# Continuous maps from preconnected spaces into disjoint unions

Each summand `Y j` of a disjoint union `Σ j, Y j` is clopen, so a continuous map out of a
preconnected space lands in a single summand.  This needs no nonemptiness assumption, unlike
`Continuous.exists_lift_sigma`, which lifts a map out of a connected space.

## Main declarations

* `Continuous.fst_apply_eq_fst_apply`: a continuous map from a preconnected space into
  `Σ j, Y j` sends all points into the same summand.
-/

public section

open Set

variable {α κ : Type*} {Y : κ → Type*} [TopologicalSpace α] [∀ j, TopologicalSpace (Y j)]

/-- A continuous map from a preconnected space into a disjoint union lands in a single summand:
any two points have images in the same summand. -/
theorem Continuous.fst_apply_eq_fst_apply [PreconnectedSpace α] {f : α → Σ j, Y j}
    (hf : Continuous f) (a b : α) : (f a).1 = (f b).1 := by
  obtain ⟨c, hc⟩ := (isPreconnected_range hf).subset_isClopen
    (isClopen_range_sigmaMk (i := (f a).1)) ⟨f a, mem_range_self a, ⟨_, rfl⟩⟩ (mem_range_self b)
  rw [← hc]
