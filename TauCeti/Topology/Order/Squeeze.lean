/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Basic

/-!
# Convergence from eventual bounds with a separate parameter

`Filter.Tendsto.squeeze_of_eventually_eventually_le` handles two-stage squeeze arguments:
the threshold for the function may depend on a separate parameter controlling the bounds.
The parameter filter must be nontrivial, and the target filters must admit convergence of
closed intervals (`TendstoIxxClass Icc`). In particular, this applies to a common neighborhood
filter in a preordered space with the order topology.
-/

public section

open Filter Set

/-- Squeeze a function between eventual bounds depending on a separate parameter.
The bounds need only hold for eventually every parameter in a nontrivial filter. -/
theorem Filter.Tendsto.squeeze_of_eventually_eventually_le {α β γ : Type*} [Preorder γ]
    {f : Filter α} {g : Filter β} [g.NeBot] {l₁ l₂ : Filter γ}
    [TendstoIxxClass Icc l₁ l₂] {u : α → γ} {l h : β → γ}
    (hl : Tendsto l g l₁) (hh : Tendsto h g l₁)
    (H : ∀ᶠ ε in g, ∀ᶠ x in f, l ε ≤ u x ∧ u x ≤ h ε) : Tendsto u f l₂ := by
  intro s hs
  obtain ⟨ε, hsub, hbound⟩ := ((tendsto_smallSets_iff.1 (hl.Icc hh) s hs).and H).exists
  exact hbound.mono fun x hx ↦ hsub hx
