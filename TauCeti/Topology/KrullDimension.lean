/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.KrullDimension

/-!
# Closed points of a topological space of dimension at most one

On a T₀ topological space the specialization order is a partial order, so the codimension
`Order.coheight x` of a point is defined: it is the supremum of the lengths of the chains of
proper specializations of `x`. This file records that on a space all of whose points have
codimension at most one, a point of codimension exactly one is closed, since a proper
specialization of such a point would have codimension at least two.

## Main declarations

* `TauCeti.isClosed_singleton_of_coheight_eq_one`: on a T₀ space all of whose points have
  codimension at most one for the specialization order, a point of codimension one is closed.
-/

public section

open Order Topology

namespace TauCeti

attribute [local instance] specializationOrder in
/-- On a T₀ topological space all of whose points have codimension at most one for the
specialization order, a point of codimension one is closed. -/
theorem isClosed_singleton_of_coheight_eq_one {α : Type*} [TopologicalSpace α] [T0Space α]
    (hdim : ∀ y : α, coheight y ≤ 1) {x : α} (hx : coheight x = 1) :
    IsClosed ({x} : Set α) := by
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun y hy ↦ ?_) subset_closure
  -- `y ∈ closure {x}` says `x ⤳ y`, which is exactly `y ≤ x` in the specialization order; a
  -- strict such `y` would be a proper specialization of `x`, hence of codimension at least two.
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  rcases eq_or_ne y x with rfl | hne
  · exact Set.mem_singleton _
  refine absurd (hdim y) (not_le.mpr ?_)
  simpa [hx] using Order.coheight_strictAnti (lt_of_le_of_ne hyx hne) (by simp [hx])

end TauCeti
