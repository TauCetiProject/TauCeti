/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path

/-!
# Properties along extended paths

Pointwise properties can be transferred between a path on `unitInterval` and its constant
endpoint extension on all of `ℝ`. This lets statements about the extended curve use properties
established on the original path. For the corresponding range equality, see `Path.extend_range`.
-/

public section

open Set

/-- A property holds everywhere along an extended path exactly when it holds along the path. -/
theorem Path.forall_extend_iff {E : Type*} [TopologicalSpace E] {p q : E} (γ : Path p q)
    {P : E → Prop} : (∀ t : ℝ, P (γ.extend t)) ↔ ∀ t, P (γ t) := by
  rw [← Set.forall_mem_range, γ.extend_range, Set.forall_mem_range]
