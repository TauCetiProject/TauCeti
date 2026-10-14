/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path

/-!
# Properties along extended paths

Universal properties of a path and of its constant endpoint extension are equivalent.
The proof uses Mathlib's `Path.extend_range`, which also gives membership in the path range.
-/

public section

open Set

/-- A property holds everywhere along an extended path exactly when it holds along the path. -/
theorem Path.forall_extend_iff {E : Type*} [TopologicalSpace E] {p q : E} (γ : Path p q)
    {P : E → Prop} : (∀ t : ℝ, P (γ.extend t)) ↔ ∀ t, P (γ t) := by
  rw [← Set.forall_mem_range, γ.extend_range, Set.forall_mem_range]
