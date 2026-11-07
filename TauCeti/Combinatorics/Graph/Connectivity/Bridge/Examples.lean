/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.Forest
public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.OfSimpleGraph

/-!
# Examples of bridge forests

This file computes the bridge forests of two small graphs built from triangles.  Joining two
disjoint triangles by one edge and adding an isolated vertex gives a bridge forest with three
vertices, one edge, and two connected components.  Identifying one vertex of the triangles
instead gives a graph with no bridges, so its bridge forest is a single vertex.
-/

public section

open Set
open scoped Graph

namespace TauCeti

/-- Two triangles joined by one edge, together with an isolated vertex. -/
def joinedTrianglesWithIsolate : SimpleGraph (Fin 7) :=
  SimpleGraph.fromEdgeSet
    {s(0, 1), s(1, 2), s(2, 0), s(2, 3), s(3, 4), s(4, 5), s(5, 3)}

/-- Adjacency in `joinedTrianglesWithIsolate` is given by its seven listed edges. -/
@[simp]
theorem joinedTrianglesWithIsolate_adj (u v : Fin 7) :
    joinedTrianglesWithIsolate.Adj u v ↔
      s(u, v) ∈
        ({s(0, 1), s(1, 2), s(2, 0), s(2, 3), s(3, 4), s(4, 5), s(5, 3)} :
          Set (Sym2 (Fin 7))) ∧ u ≠ v := by
  simp only [joinedTrianglesWithIsolate, SimpleGraph.fromEdgeSet_adj]

private instance : DecidableRel joinedTrianglesWithIsolate.Adj := by
  intro x y
  simp only [joinedTrianglesWithIsolate, SimpleGraph.fromEdgeSet_adj]
  infer_instance

/-- The multigraph associated to `joinedTrianglesWithIsolate`. -/
abbrev joinedTrianglesWithIsolateGraph : Graph (Fin 7) (Sym2 (Fin 7)) :=
  Graph.ofSimpleGraph joinedTrianglesWithIsolate

/-- Two triangles sharing exactly their vertex `0`. -/
def trianglesSharingVertex : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {s(0, 1), s(1, 2), s(2, 0), s(0, 3), s(3, 4), s(4, 0)}

/-- Adjacency in `trianglesSharingVertex` is given by its six listed edges. -/
@[simp]
theorem trianglesSharingVertex_adj (u v : Fin 5) :
    trianglesSharingVertex.Adj u v ↔
      s(u, v) ∈
        ({s(0, 1), s(1, 2), s(2, 0), s(0, 3), s(3, 4), s(4, 0)} :
          Set (Sym2 (Fin 5))) ∧ u ≠ v := by
  simp only [trianglesSharingVertex, SimpleGraph.fromEdgeSet_adj]

private instance : DecidableRel trianglesSharingVertex.Adj := by
  intro x y
  simp only [trianglesSharingVertex, SimpleGraph.fromEdgeSet_adj]
  infer_instance

/-- The multigraph associated to `trianglesSharingVertex`. -/
abbrev trianglesSharingVertexGraph : Graph (Fin 5) (Sym2 (Fin 5)) :=
  Graph.ofSimpleGraph trianglesSharingVertex

/-- The edge joining the two triangles is the only bridge. -/
theorem joinedTrianglesWithIsolate_bridgeSet :
    joinedTrianglesWithIsolateGraph.bridgeSet = {s(2, 3)} := by
  rw [Graph.bridgeSet_ofSimpleGraph]
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    fin_cases x <;> fin_cases y <;>
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, SimpleGraph.isBridge_iff] <;> decide

/-- The joined triangles and the isolated vertex are the two components of the first example. -/
@[simp]
theorem joinedTrianglesWithIsolate_componentCount :
    joinedTrianglesWithIsolateGraph.componentCount = 2 := by
  rw [Graph.componentCount_ofSimpleGraph, Nat.card_eq_fintype_card]
  decide

/-- The bridge components are the two triangles and the isolated vertex. -/
@[simp]
theorem joinedTrianglesWithIsolate_bridgeComponent_card :
    Nat.card joinedTrianglesWithIsolateGraph.BridgeComponent = 3 := by
  have hcard : joinedTrianglesWithIsolateGraph.bridgeSet.ncard = 1 := by
    rw [joinedTrianglesWithIsolate_bridgeSet]
    simp
  rw [Graph.BridgeComponent, ← Graph.componentCount_def]
  rw [Graph.componentCount_deleteEdges_bridgeSet]
  rw [joinedTrianglesWithIsolate_componentCount, hcard]

/-- The bridge forest of the joined-triangles example has just the joining edge. -/
theorem joinedTrianglesWithIsolate_bridgeForest_edgeSet :
    E(joinedTrianglesWithIsolateGraph.bridgeForest) = {s(2, 3)} := by
  rw [Graph.edgeSet_bridgeForest, joinedTrianglesWithIsolate_bridgeSet]

/-- The isolated vertex remains a second component of the bridge forest. -/
theorem joinedTrianglesWithIsolate_bridgeForest_componentCount :
    joinedTrianglesWithIsolateGraph.bridgeForest.componentCount = 2 := by
  rw [Graph.componentCount_bridgeForest]
  exact joinedTrianglesWithIsolate_componentCount

/-- Neither triangle acquires a bridge when the triangles share a vertex. -/
theorem trianglesSharingVertex_bridgeSet :
    trianglesSharingVertexGraph.bridgeSet = ∅ := by
  rw [Graph.bridgeSet_ofSimpleGraph]
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    fin_cases x <;> fin_cases y <;>
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        SimpleGraph.isBridge_iff] <;> decide

/-- The two triangles sharing a vertex form one connected component. -/
@[simp]
theorem trianglesSharingVertex_componentCount :
    trianglesSharingVertexGraph.componentCount = 1 := by
  rw [Graph.componentCount_ofSimpleGraph, Nat.card_eq_fintype_card]
  decide

/-- With no bridge to delete, the shared-vertex example has one bridge component. -/
@[simp]
theorem trianglesSharingVertex_bridgeComponent_card :
    Nat.card trianglesSharingVertexGraph.BridgeComponent = 1 := by
  have hcard : trianglesSharingVertexGraph.bridgeSet.ncard = 0 := by
    rw [trianglesSharingVertex_bridgeSet]
    simp
  rw [Graph.BridgeComponent, ← Graph.componentCount_def]
  rw [Graph.componentCount_deleteEdges_bridgeSet]
  rw [trianglesSharingVertex_componentCount, hcard]

/-- The bridge forest of the shared-vertex example has no edges. -/
theorem trianglesSharingVertex_bridgeForest_edgeSet :
    E(trianglesSharingVertexGraph.bridgeForest) = ∅ := by
  rw [Graph.edgeSet_bridgeForest, trianglesSharingVertex_bridgeSet]

/-- The edgeless bridge forest of the shared-vertex example is a single vertex. -/
theorem trianglesSharingVertex_bridgeForest_componentCount :
    trianglesSharingVertexGraph.bridgeForest.componentCount = 1 := by
  rw [Graph.componentCount_bridgeForest]
  exact trianglesSharingVertex_componentCount

end TauCeti
