/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousOn

/-!
# Injective maps and punctured neighbourhoods

An injective map continuous at `x` sends the punctured neighbourhoods of `x` into the punctured
neighbourhoods of `f x` (`ContinuousAt.tendsto_nhdsNE`). For the inclusion of a subspace, such as
`Subtype.val` or `Set.inclusion`, this pulls back statements holding on a punctured neighbourhood
in the ambient space to the subspace (`TauCeti.tendsto_subtype_val_nhdsNE`).
-/

public section

open Filter Function Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β} {x : α}

/-- An injective map continuous at `x` sends punctured neighbourhoods of `x` to punctured
neighbourhoods of `f x`. -/
theorem ContinuousAt.tendsto_nhdsNE (hf : ContinuousAt f x) (hinj : Injective f) :
    Tendsto f (𝓝[≠] x) (𝓝[≠] (f x)) :=
  hf.continuousWithinAt.tendsto_nhdsWithin fun _ hy hxy ↦ hy (hinj hxy)

namespace TauCeti

/-- The inclusion of a subtype sends punctured neighbourhoods of `x` to punctured neighbourhoods
of `↑x`. -/
theorem tendsto_subtype_val_nhdsNE {p : α → Prop} (x : Subtype p) :
    Tendsto (Subtype.val : Subtype p → α) (𝓝[≠] x) (𝓝[≠] (x : α)) :=
  continuous_subtype_val.continuousAt.tendsto_nhdsNE Subtype.val_injective

end TauCeti
