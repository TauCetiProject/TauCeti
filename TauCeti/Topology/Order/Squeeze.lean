/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Basic

/-!
# Convergence from eventual bounds with a separate parameter

If a function eventually lies between bounds for each sufficiently late parameter, and both
bounds tend to the same limit as the parameter varies, the function tends to that limit.
-/

public section

open Filter Topology

/-- Squeeze a function between eventual bounds depending on a separate parameter.
The bounds need only hold for eventually every parameter in a nontrivial filter. -/
theorem Filter.Tendsto.squeeze_of_eventually_bounds {α β γ : Type*} [LinearOrder γ]
    [TopologicalSpace γ] [OrderTopology γ] {f : Filter α} {g : Filter β} [g.NeBot]
    {u : α → γ} {l h : β → γ} {c : γ} (hl : Tendsto l g (𝓝 c)) (hh : Tendsto h g (𝓝 c))
    (H : ∀ᶠ ε in g, ∀ᶠ x in f, l ε ≤ u x ∧ u x ≤ h ε) : Tendsto u f (𝓝 c) := by
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · obtain ⟨ε, hε, hbound⟩ := ((hl.eventually (lt_mem_nhds ha)).and H).exists
    exact hbound.mono fun x hx ↦ hε.trans_le hx.1
  · obtain ⟨ε, hε, hbound⟩ := ((hh.eventually (gt_mem_nhds ha)).and H).exists
    exact hbound.mono fun x hx ↦ hx.2.trans_lt hε
