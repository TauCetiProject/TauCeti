/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Log.MaxDiv
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# Clipped logarithmic envelopes for functions vanishing at infinity

For `f : C₀(α, E)`, `δ > 0`, and `[R1Space α]`, the clipped logarithmic envelope
`TauCeti.logMaxDiv f δ` has compact support
(`ZeroAtInftyContinuousMap.hasCompactSupport_logMaxDiv`).
-/

public section

open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {α E : Type*} [TopologicalSpace α] [SeminormedAddCommGroup E]

/-- For `δ > 0` and `[R1Space α]`, `TauCeti.logMaxDiv f δ` has compact support for `f : C₀(α, E)`
because `‖f x‖ < δ` outside a compact set. -/
theorem hasCompactSupport_logMaxDiv [R1Space α] (f : C₀(α, E)) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (TauCeti.logMaxDiv f δ) := by
  obtain ⟨K, hK, hKlt⟩ := f.exists_isCompact_norm_lt hδ
  exact HasCompactSupport.of_support_subset_isCompact hK fun x hx ↦
    by_contra fun hxK ↦ hx ((TauCeti.logMaxDiv_eq_zero_iff f hδ x).2 (hKlt x hxK).le)

end ZeroAtInftyContinuousMap
