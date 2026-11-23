/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.Basis
public import TauCeti.Combinatorics.Graph.Serre.Cycle.SpanningTree
public import TauCeti.Combinatorics.Graph.Serre.Parallel
import TauCeti.Combinatorics.Graph.Serre.Cycle.Coefficients
import TauCeti.Combinatorics.Graph.Serre.Cycle.Coordinates

/-!
# Cycle modules of roses, of the segment and of parallel edges

This file computes the incidence kernel, the cycle rank, the number of components and the
spanning forests of three families of small graphs. The incidence kernels are computed over an
arbitrary ring, the cycle ranks over any ring with the strong rank condition, such as the
integers and `ZMod 2`.

Every dart of a rose is a loop. Its incidence boundary is therefore zero, every chain is a
cycle, the cycle rank is the number of petals, and the only spanning forest is empty. The
integral unit cycle on a petal reduces modulo two to the binary unit cycle, in finitely
supported and in finite-function coordinates.

The positive dart of the segment is a spanning forest of itself. The segment therefore has
no nonzero cycle and a single component.

For the graph `SerreGraph.parallelGraph α` of parallel edges indexed by `α`, any single dart is a
spanning forest of every set of darts containing it, and the fundamental cycle of another dart in
the same direction traverses that dart forward and the forest dart backward. Two distinct darts
never form a spanning forest, since they join the same two vertices. When `α` has `n` elements,
`0 < n`, the cycle modules relative to any orientation have rank `n - 1`, and every spanning tree
leaves `n - 1` positive darts outside it.

## References

* R. Diestel, *Graph Theory*, §1.9 (cycle spaces and fundamental cycle bases).
* A. Hatcher, *Algebraic Topology*, §2.2 (incidence boundaries and coefficients).
-/

public section

namespace TauCeti.SerreGraph

section Rose

variable (α : Type*) (O : Set (rose α).E) (R : Type*) [Ring R]

/-- The incidence boundary of a rose is zero: every column is that of a loop. -/
@[simp] theorem incidenceBoundary_rose : (rose α).incidenceBoundary O R = 0 :=
  incidenceBoundary_eq_zero R fun _ _ => rfl

/-- The simple support of a rose has no edges. -/
@[simp] theorem supportGraph_rose : (rose α).supportGraph O = ⊥ :=
  ((rose α).supportGraph_eq_bot_iff O).mpr fun _ _ => rfl

/-- A rose has one component, whichever darts are chosen. -/
theorem card_connectedComponent_supportGraph_rose :
    Nat.card ((rose α).supportGraph O).ConnectedComponent = 1 := by
  rw [card_connectedComponent_supportGraph_of_forall_src_eq_tgt fun _ _ => rfl,
    Nat.card_unique]

variable {α O} in
/-- The only spanning forest of a rose is the empty one: it cannot contain a petal. -/
theorem isSpanningForest_rose_iff {F : Set (rose α).E} : (rose α).IsSpanningForest O F ↔ F = ∅ :=
  ⟨fun hF => hF.eq_empty fun _ _ => rfl, fun h => h ▸ isSpanningForest_empty_iff.mpr
    fun _ _ => rfl⟩

/-- The cycle rank of a rose is its number of petals, over any coefficient ring with the strong
rank condition. The one-petal rose has integral rank and binary dimension one. -/
theorem finrank_ker_incidenceBoundary_rose [StrongRankCondition R] :
    Module.finrank R ((rose α).incidenceBoundary {e | e.2 = true} R).ker = Nat.card α := by
  rw [finrank_ker_incidenceBoundary_of_forall_src_eq_tgt fun _ _ => rfl]
  exact Nat.card_congr
    ⟨fun e => e.val.1, fun a => ⟨(a, true), rfl⟩, fun ⟨⟨_, _⟩, h⟩ => by cases h; rfl,
      fun _ => rfl⟩

/- The integral unit cycle on a petal reduces modulo two to the binary unit cycle, in finitely
supported coordinates (`cycleLatticeModTwoEquiv_one_tmul_single`) and in finite-function
coordinates. -/
example [Finite O] [DecidableEq α] (e : O) :
    ((rose α).cycleSpaceFinsuppEquiv O ((rose α).cycleLatticeModTwoEquiv O
      (1 ⊗ₜ[ℤ] ⟨Finsupp.single e 1, (single_mem_cycleLattice_iff e).mpr rfl⟩))).val =
        Pi.single e 1 := by
  simp

end Rose

section Segment

variable (b : segment.E)

/-- Either dart of the segment is a spanning forest of itself. -/
theorem isSpanningForest_segment : segment.IsSpanningForest {b} {b} :=
  isSpanningForest_singleton rfl (Bool.not_ne_self b).symm
    fun f hf _ => by rw [Set.mem_singleton_iff.mp hf]

/-- The segment has no nonzero cycle, over any coefficient ring. -/
theorem ker_incidenceBoundary_segment (R : Type*) [Ring R] :
    (segment.incidenceBoundary {b} R).ker = ⊥ :=
  (isSpanningForest_segment b).ker_incidenceBoundary_eq_bot

/-- The segment has one component. -/
theorem card_connectedComponent_supportGraph_segment :
    Nat.card (segment.supportGraph {b}).ConnectedComponent = 1 := by
  have : Finite segment.V := Finite.of_equiv _ segmentVEquiv.symm
  have h := (isSpanningForest_segment b).card_add_card_connectedComponent
  have hV : Nat.card segment.V = 2 :=
    (Nat.card_congr segmentVEquiv).trans (by rw [Nat.card_eq_fintype_card, Fintype.card_bool])
  rw [Nat.card_coe_set_eq, Set.ncard_singleton, hV] at h
  omega

end Segment

section Parallel

variable {α : Type*}

/-- Any single dart of a graph of parallel edges is a spanning forest of every set of darts
containing it: all darts join the two vertices. -/
theorem isSpanningForest_parallelGraph_singleton {O : Set (parallelGraph α).E}
    {e : (parallelGraph α).E} (he : e ∈ O) : (parallelGraph α).IsSpanningForest O {e} :=
  isSpanningForest_singleton he (fun h => Bool.not_ne_self _ h.symm) fun f _ _ => by
    simp only [← edgeEnds_edge, parallelGraph_edgeEnds]

/-- Two distinct darts of a graph of parallel edges never form a spanning forest: they join the
same two vertices. -/
theorem not_isSpanningForest_parallelGraph_pair {O : Set (parallelGraph α).E}
    {e f : (parallelGraph α).E} (hef : e ≠ f) : ¬(parallelGraph α).IsSpanningForest O {e, f} :=
  fun h => hef <| h.endpoints_injOn (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl) <| by
    simp only [← edgeEnds_edge, parallelGraph_edgeEnds]

/-- Relative to the single dart `e`, the fundamental cycle of another dart of a graph of parallel
edges in the same direction traverses it forward and `e` backward. -/
theorem cycleBasis_parallelGraph_singleton (R : Type*) [Ring R] {O : Set (parallelGraph α).E}
    {e : (parallelGraph α).E} (he : e ∈ O) (f : ↥(O \ {e})) (hf : f.val.2 = e.2) :
    ((isSpanningForest_parallelGraph_singleton he).cycleBasis R f).val =
      Finsupp.single ⟨f.val, f.property.1⟩ 1 - Finsupp.single ⟨e, he⟩ 1 :=
  (isSpanningForest_parallelGraph_singleton he).cycleBasis_of_parallel f rfl hf
    (congrArg (!·) hf)

/-- Relative to any orientation, the cycle modules of `n` parallel edges, `0 < n`, have rank
`n - 1` over any coefficient ring with the strong rank condition. -/
theorem finrank_ker_incidenceBoundary_parallelGraph_add_one (R : Type*) [Ring R]
    [StrongRankCondition R] [Finite α] [Nonempty α] {O : Set (parallelGraph α).E}
    (hO : (parallelGraph α).IsOrientation O) :
    Module.finrank R ((parallelGraph α).incidenceBoundary O R).ker + 1 = Nat.card α := by
  obtain ⟨a⟩ := ‹Nonempty α›
  obtain ⟨e, he⟩ : ∃ e, e ∈ O := (hO.mem_or_rev_mem (a, false)).elim (⟨_, ·⟩) (⟨_, ·⟩)
  rw [finrank_ker_incidenceBoundary_add_one he (fun h => Bool.not_ne_self _ h.symm)
      fun f _ _ => by simp only [← edgeEnds_edge, parallelGraph_edgeEnds],
    Nat.card_eq_of_bijective _ hO.bijective_toGeomEdge,
    Nat.card_congr (parallelGraphGeomEdgeEquiv α)]

/-- Every spanning tree of `n` parallel edges leaves `n - 1` positive darts outside it, for any
orientation: these darts index the fundamental cycle basis, and the free basis of the reduced path
group. -/
theorem card_diff_darts_parallelGraph_add_one [Finite α] (T : (parallelGraph α).SpanningTree)
    {O : Set (parallelGraph α).E} (hO : (parallelGraph α).IsOrientation O) :
    Nat.card ↥(O \ T.darts) + 1 = Nat.card α := by
  have h := T.card_diff_add_card hO
  have hV : Nat.card (parallelGraph α).V = 2 := Nat.card_eq_fintype_card.trans rfl
  rw [hV, Nat.card_eq_of_bijective _ hO.bijective_toGeomEdge,
    Nat.card_congr (parallelGraphGeomEdgeEquiv α)] at h
  omega

end Parallel

end TauCeti.SerreGraph
