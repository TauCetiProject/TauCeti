/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path

/-!
# Properties along extended paths

A pointwise property of a path also holds along its constant endpoint extension.
-/

public section

open Set

/-- A property holding along a path still holds along its constant endpoint extension. -/
theorem Path.forall_extend {E : Type*} [TopologicalSpace E] {p q : E} (γ : Path p q)
    {P : E → Prop} (h : ∀ t, P (γ t)) (t : ℝ) : P (γ.extend t) := by
  obtain ⟨u, hu⟩ := (γ.extend_range ▸ mem_range_self t : γ.extend t ∈ range γ)
  simpa only [← hu] using h u
