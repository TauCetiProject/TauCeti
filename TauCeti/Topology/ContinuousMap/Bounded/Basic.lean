/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Postcomposition of bounded continuous functions by a uniformly continuous map

Mathlib proves that postcomposition `f ↦ G ∘ f` by a Lipschitz map `G` is Lipschitz, hence
uniformly continuous, for the sup metric on bounded continuous functions
(`BoundedContinuousFunction.lipschitz_comp`). This file records the uniformly continuous analogue:
if a bounded continuous function `g` is uniformly continuous on a set `s`, then `f ↦ g ∘ f` is
uniformly continuous on the bounded continuous functions taking values in `s`. No Lipschitz bound
is needed, only a common modulus of continuity.

It is used for the derivative `t ↦ G' (f t)` of a superposition operator `f ↦ G ∘ f`, where
`G'` is typically only continuous.

## Main declarations

* `BoundedContinuousFunction.uniformContinuousOn_compContinuous_left`: postcomposition by a map
  uniformly continuous on `s` is uniformly continuous on the functions with values in `s`.
-/

public section

open Set

namespace BoundedContinuousFunction

variable {α β γ : Type*} [TopologicalSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]

/-- Postcomposition by a bounded continuous function `g` which is uniformly continuous on `s` is
uniformly continuous, for the sup metric, on the bounded continuous functions with values
in `s`. -/
theorem uniformContinuousOn_compContinuous_left (g : β →ᵇ γ) {s : Set β}
    (hg : UniformContinuousOn g s) :
    UniformContinuousOn (fun f : α →ᵇ β ↦ g.compContinuous f.toContinuousMap)
      {f | ∀ t, f t ∈ s} := by
  rw [Metric.uniformContinuousOn_iff_le] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hg ε hε
  exact ⟨δ, hδ, fun f hf f' hf' hff' ↦ (dist_le hε.le).2 fun t ↦
    h _ (hf t) _ (hf' t) ((dist_coe_le_dist t).trans hff')⟩

end BoundedContinuousFunction
