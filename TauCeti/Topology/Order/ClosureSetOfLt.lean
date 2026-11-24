/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.OrderClosed

/-!
# The closure of a set cut out locally by a strict inequality

If, inside an open set `U`, a set `Ω` is the strict sublevel set `{z | f z < g z}` of two functions
continuous on `U`, then inside `U` the closure of `Ω` lies in the non-strict sublevel set
`{z | f z ≤ g z}` (`TauCeti.inter_closure_subset_setOf_le`). This is the local form of Mathlib's
`closure_lt_subset_le`, as used for a domain described near a boundary point by a defining
inequality.
-/

public section

open Set

namespace TauCeti

variable {X α : Type*} [TopologicalSpace X] [TopologicalSpace α] [Preorder α]
  [OrderClosedTopology α] {U Ω : Set X} {f g : X → α}

/-- If `Ω` agrees with `{z | f z < g z}` on an open set `U` where `f` and `g` are continuous, then
the points of `U` in the closure of `Ω` satisfy `f z ≤ g z`. -/
theorem inter_closure_subset_setOf_le (hU : IsOpen U) (hf : ContinuousOn f U)
    (hg : ContinuousOn g U) (hΩ : U ∩ Ω = U ∩ {z | f z < g z}) :
    U ∩ closure Ω ⊆ {z | f z ≤ g z} := fun y hy => by
  have hcl : y ∈ closure (U ∩ {z | f z < g z}) := hΩ ▸ hU.inter_closure hy
  exact ((hf y hy.1).mono inter_subset_left).closure_le hcl
    ((hg y hy.1).mono inter_subset_left) fun z hz => le_of_lt hz.2

end TauCeti
