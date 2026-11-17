/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace
public import TauCeti.Topology.FilledHull
import TauCeti.Topology.ConnectedComponents

/-!
# Bounded complementary components in the one-point compactification

For a closed set in a proper locally connected metric space, the closure of a bounded
complementary component in the one-point compactification adds only points of the closed set.
Consequently a path avoiding the closed set cannot leave such a component, even through infinity.

## Main results

* `TauCeti.closure_image_coe_connectedComponentIn_subset` describes that closure.
* `TauCeti.connectedComponentIn_compl_image_coe` identifies the connected component in the
  complement of `(↑) '' K` of any point in `filledHull K \ K` with the image of its component in
  `Kᶜ`.
* `TauCeti.not_joinedIn_compl_image_coe` separates the component from every other point by paths.
-/

public section

namespace TauCeti

open Bornology Set
open scoped OnePoint

variable {E : Type*} [MetricSpace E] [ProperSpace E] [LocallyConnectedSpace E]

/-- In the one-point compactification, the closure of a bounded component of the complement
of a closed set `K` adds only points of `K`. -/
theorem closure_image_coe_connectedComponentIn_subset {K : Set E} (hK : IsClosed K)
    {x : E} (hx : x ∈ filledHull K) :
    closure (((↑) : E → OnePoint E) '' connectedComponentIn Kᶜ x) ⊆
      (↑) '' (connectedComponentIn Kᶜ x ∪ K) := by
  have hD : IsCompact (closure (connectedComponentIn Kᶜ x)) :=
    (mem_filledHull_iff.mp hx).isCompact_closure
  refine (closure_minimal (image_mono subset_closure)
    (hD.image OnePoint.continuous_coe).isClosed).trans (image_mono fun y hy => ?_)
  by_contra hyD
  rw [mem_union, not_or] at hyD
  exact frontier_connectedComponentIn_subset_compl hK.isOpen_compl x
    ⟨hy, by rw [hK.isOpen_compl.connectedComponentIn.interior_eq]; exact hyD.1⟩ hyD.2

/-- In the one-point compactification, the connected component in `(((↑) : E → OnePoint E) '' K)ᶜ`
of a point in a bounded complementary component of a closed set `K` is the image of its component in
`Kᶜ`. -/
theorem connectedComponentIn_compl_image_coe {K : Set E} (hK : IsClosed K) {x : E}
    (hx : x ∈ filledHull K \ K) :
    connectedComponentIn (((↑) : E → OnePoint E) '' K)ᶜ (x : OnePoint E) =
      ((↑) : E → OnePoint E) '' connectedComponentIn Kᶜ x := by
  have hxS : (x : OnePoint E) ∈ (((↑) : E → OnePoint E) '' K)ᶜ :=
    fun ⟨_, hy, hyx⟩ ↦ hx.2 (OnePoint.coe_injective hyx ▸ hy)
  refine Subset.antisymm ?_
    ((isPreconnected_connectedComponentIn.image _
      OnePoint.continuous_coe.continuousOn).subset_connectedComponentIn
      (mem_image_of_mem _ (mem_connectedComponentIn hx.2))
      (image_subset_iff.2 fun y hy ⟨z, hz, hzy⟩ ↦
        connectedComponentIn_subset _ _ hy (OnePoint.coe_injective hzy ▸ hz)))
  have hU : IsOpen (((↑) : E → OnePoint E) '' connectedComponentIn Kᶜ x) :=
    OnePoint.isOpenEmbedding_coe.isOpenMap _ hK.isOpen_compl.connectedComponentIn
  refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hU
    ⟨(x : OnePoint E), mem_connectedComponentIn hxS,
      mem_image_of_mem _ (mem_connectedComponentIn hx.2)⟩ ?_
  rintro w ⟨hcl, hwS⟩
  obtain ⟨y, hy | hy, rfl⟩ := closure_image_coe_connectedComponentIn_subset hK hx.1 hcl
  · exact ⟨y, hy, rfl⟩
  · exact (connectedComponentIn_subset _ _ hwS (mem_image_of_mem _ hy)).elim

/-- A point of the one-point compactification outside the image of a bounded complementary
component of a closed set `K` cannot be joined to it by a path avoiding the image of `K`. -/
theorem not_joinedIn_compl_image_coe {K : Set E} (hK : IsClosed K) {x : E}
    (hx : x ∈ filledHull K \ K) {w : OnePoint E}
    (hw : w ∉ ((↑) : E → OnePoint E) '' connectedComponentIn Kᶜ x) :
    ¬ JoinedIn (((↑) : E → OnePoint E) '' K)ᶜ (x : OnePoint E) w := fun h ↦
  hw <| connectedComponentIn_compl_image_coe hK hx ▸
    (isConnected_range h.somePath.continuous).isPreconnected.subset_connectedComponentIn
      ⟨0, by simp⟩ (range_subset_iff.2 h.somePath_mem) ⟨1, by simp⟩

end TauCeti
