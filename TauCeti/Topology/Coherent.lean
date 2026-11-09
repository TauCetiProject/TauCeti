/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Coherent

/-!
# Closed sets in a coherent topology

If `X` carries the topology coherent with a family `S` of subsets, a set is closed as soon as it
meets every member of `S` in a closed subset of `X`. This restates
`Topology.IsCoherentWith.isClosed_iff` with intersections in place of preimages in the subtypes.

## Main declarations

* `Topology.IsCoherentWith.isClosed_of_forall_isClosed_inter`: a set meeting every member of `S`
  in a closed set is closed.
-/

public section

open Set

/-- If `X` carries the topology coherent with a family `S` of subsets, then a set which meets every
member of `S` in a closed set is closed. -/
theorem Topology.IsCoherentWith.isClosed_of_forall_isClosed_inter {X : Type*} [TopologicalSpace X]
    {S : Set (Set X)} (hS : IsCoherentWith S) {t : Set X} (ht : ∀ s ∈ S, IsClosed (t ∩ s)) :
    IsClosed t := by
  refine hS.isClosed_iff.2 fun s hs ↦ ?_
  have := (ht s hs).preimage (continuous_subtype_val (p := (· ∈ s)))
  rwa [preimage_inter, Subtype.coe_preimage_self, inter_univ] at this
