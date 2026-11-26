/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Pointwise
public import Mathlib.Topology.Algebra.Star

/-!
# Pointwise star of open sets

The pointwise star `star s` of a set is its preimage under `star` (`Set.star_preimage`), so a
continuous star operation maps open sets to open sets, `IsOpen.star`.
-/

public section

open scoped Pointwise

variable {α : Type*} [TopologicalSpace α] [Star α] [ContinuousStar α] {s : Set α}

/-- Under a continuous star operation, the pointwise star of an open set is open. -/
theorem IsOpen.star (hs : IsOpen s) : IsOpen (star s) := by
  rw [← Set.star_preimage]
  exact hs.preimage continuous_star
