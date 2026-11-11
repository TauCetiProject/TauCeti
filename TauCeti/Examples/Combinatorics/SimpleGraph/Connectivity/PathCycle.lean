/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.OfSimpleGraph
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Block
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.CommonCycle

/-!
# Connectivity of a path and a cycle

The four-vertex path and cycle illustrate the structural difference between bridges and blocks.
Every edge of the path is a bridge, and its blocks are its three individual edges. Consequently
the path is connected but is neither two-edge- nor two-vertex-connected. The cycle has no bridge,
has the whole vertex set as its unique block, and is both two-edge- and two-vertex-connected.

The examples also verify the same bridge statements after regarding the simple graphs as
edge-labelled multigraphs with `Graph.ofSimpleGraph`.
-/

public section

open Set
open scoped Graph

namespace TauCeti.PathCycleExamples

open SimpleGraph

/-! ## The four-vertex path -/

/-- Every actual edge of the four-vertex path is a bridge. -/
theorem path_isBridge_of_mem {e : Sym2 (Fin 4)} (he : e ∈ (pathGraph 4).edgeSet) :
    (pathGraph 4).IsBridge e :=
  isAcyclic_iff_forall_isBridge.mp (isAcyclic_pathGraph 4) he

/-- Every actual edge remains a bridge in the edge-labelled multigraph associated to the path. -/
theorem pathGraph_isBridge_of_mem {e : Sym2 (Fin 4)}
    (he : e ∈ (Graph.ofSimpleGraph (pathGraph 4)).edgeSet) :
    (Graph.ofSimpleGraph (pathGraph 4)).IsBridge e := by
  rw [Graph.isBridge_ofSimpleGraph_iff]
  exact ⟨he, path_isBridge_of_mem he⟩

/-- The four-vertex path is connected at threshold one. -/
theorem path_isEdgeConnected_one : (pathGraph 4).IsEdgeConnected 1 := by
  rw [isEdgeConnected_one]
  exact preconnected_pathGraph 4

/-- The four-vertex path is not two-edge-connected. -/
theorem path_not_isEdgeConnected_two : ¬(pathGraph 4).IsEdgeConnected 2 := by
  rw [isEdgeConnected_two_iff_forall_not_isBridge]
  push Not
  exact ⟨s(1, 2), path_isBridge_of_mem (by simp [pathGraph_adj])⟩

/-- The four-vertex path is vertex-connected at threshold one. -/
theorem path_isVertexConnected_one : (pathGraph 4).IsVertexConnected 1 := by
  rw [isVertexConnected_one]
  exact ⟨connected_pathGraph.mpr (by decide), inferInstance⟩

/-- No vertex of the four-vertex path is isolated. -/
theorem path_not_isIsolated (v : Fin 4) : ¬(pathGraph 4).IsIsolated v :=
  (preconnected_pathGraph 4).not_isIsolated v

/-- The four-vertex path is not two-vertex-connected. -/
theorem path_not_isVertexConnected_two : ¬(pathGraph 4).IsVertexConnected 2 := by
  exact fun h ↦ path_not_isEdgeConnected_two h.isEdgeConnected

/-- The first edge of the four-vertex path is a block. -/
theorem path_isBlock_zero_one : (pathGraph 4).IsBlock ({0, 1} : Set (Fin 4)) := by
  exact (isAcyclic_pathGraph 4).isBlock_pair (by simp [pathGraph_adj])

/-- The middle edge of the four-vertex path is a block. -/
theorem path_isBlock_one_two : (pathGraph 4).IsBlock ({1, 2} : Set (Fin 4)) := by
  exact (isAcyclic_pathGraph 4).isBlock_pair (by simp [pathGraph_adj])

/-- The last edge of the four-vertex path is a block. -/
theorem path_isBlock_two_three : (pathGraph 4).IsBlock ({2, 3} : Set (Fin 4)) := by
  exact (isAcyclic_pathGraph 4).isBlock_pair (by simp [pathGraph_adj])

/-- The blocks of the four-vertex path are exactly its three edges. -/
theorem path_isBlock_iff {B : Set (Fin 4)} :
    (pathGraph 4).IsBlock B ↔ B = {0, 1} ∨ B = {1, 2} ∨ B = {2, 3} := by
  constructor
  · intro hB
    obtain ⟨a, haB⟩ := hB.nonempty
    have hB' : B.Nontrivial :=
      hB.nontrivial_of_not_isIsolated haB (path_not_isIsolated a)
    obtain ⟨v, x, hadj, hBpair⟩ :=
      (isAcyclic_pathGraph 4).exists_adj_pair_of_isBlock hB hB'
    rw [hBpair]
    have h01 : ({1, 0} : Set (Fin 4)) = {0, 1} := pair_comm _ _
    have h12 : ({2, 1} : Set (Fin 4)) = {1, 2} := pair_comm _ _
    have h23 : ({3, 2} : Set (Fin 4)) = {2, 3} := pair_comm _ _
    fin_cases v <;> fin_cases x <;> simp_all [pathGraph_adj]
  · rintro (rfl | rfl | rfl)
    · exact path_isBlock_zero_one
    · exact path_isBlock_one_two
    · exact path_isBlock_two_three

/-! ## The four-vertex cycle -/

/-- The four-vertex cycle is two-vertex-connected. -/
theorem cycle_isVertexConnected_two : (cycleGraph 4).IsVertexConnected 2 := by
  apply (isVertexConnected_two_iff_forall_exists_isCycle_mem_support
    (by simp [Nat.card_eq_fintype_card])).2
  intro u v _
  let c := cycleGraph.cycle 1
  have hu : u ∈ c.support := cycleGraph.mem_support_cycle u
  refine ⟨c.rotate u hu, cycleGraph.isCycle_cycle.rotate hu, ?_⟩
  exact (c.mem_support_rotate_iff u hu).2 (cycleGraph.mem_support_cycle v)

/-- The four-vertex cycle is two-edge-connected. -/
theorem cycle_isEdgeConnected_two : (cycleGraph 4).IsEdgeConnected 2 :=
  cycle_isVertexConnected_two.isEdgeConnected

/-- No actual edge of the four-vertex cycle is a bridge. -/
theorem cycle_not_isBridge (e : Sym2 (Fin 4)) : ¬(cycleGraph 4).IsBridge e :=
  isEdgeConnected_two_iff_forall_not_isBridge.mp cycle_isEdgeConnected_two e

/-- No actual edge is a bridge in the edge-labelled multigraph associated to the cycle. -/
theorem cycleGraph_not_isBridge (e : Sym2 (Fin 4)) :
    ¬(Graph.ofSimpleGraph (cycleGraph 4)).IsBridge e := by
  rw [Graph.isBridge_ofSimpleGraph_iff]
  exact fun h ↦ cycle_not_isBridge e h.2

/-- The whole vertex set is a block of the four-vertex cycle. -/
theorem cycle_isBlock_univ : (cycleGraph 4).IsBlock (Set.univ : Set (Fin 4)) := by
  apply (isBlock_and_three_le_encard_iff_maximal_isVertexConnected_two.mpr ?_).1
  rw [maximal_subset_iff]
  refine ⟨(SimpleGraph.induceUnivIso (cycleGraph 4)).isVertexConnected_iff.mp
    cycle_isVertexConnected_two, ?_⟩
  intro C _ hC
  exact Set.Subset.antisymm hC (Set.subset_univ C)

/-- Every block of the four-vertex cycle is its whole vertex set. -/
theorem cycle_isBlock_iff {B : Set (Fin 4)} : (cycleGraph 4).IsBlock B ↔ B = Set.univ := by
  constructor
  · intro hB
    exact hB.eq_of_subset cycle_isBlock_univ.connected cycle_isBlock_univ.not_isCutVertex
      (Set.subset_univ B)
  · rintro rfl
    exact cycle_isBlock_univ

end TauCeti.PathCycleExamples
