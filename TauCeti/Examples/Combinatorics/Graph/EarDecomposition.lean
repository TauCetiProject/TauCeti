/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.CutCapacity
public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Basic
public import TauCeti.Combinatorics.Graph.Orientation.StronglyConnected
import Mathlib.Tactic.FinCases

/-!
# Ears and strong orientations of two parallel edges and of a loop

Multigraph ear decompositions retain edge identities, so two parallel edges form a cycle of length
two and a loop forms a cycle of length one. This file works out both cases.

Two vertices `0` and `1` joined by two parallel edges have edge connectivity two. The two edges
form a cycle, which is a closed ear over the vertex `0`, and orienting them in opposite directions
gives a strongly connected orientation. Keeping only one of the edges leaves the same underlying
simple graph, but that edge is a bridge, the edge connectivity drops to one, and no orientation is
strongly connected.

A single loop is a cycle of length one and a closed ear over its vertex. It is not a bridge, and
it crosses no edge cut, so it contributes nothing to the capacity of any cut.
-/

public section

open Set
open scoped Graph

namespace TauCeti.Examples.MultigraphEars

open Graph

/-- A closed ear over one vertex that adds up to the whole graph gives an ear decomposition with
one closed ear, starting from that vertex. -/
private theorem exists_closed_earDecomposition_of_add_eq {α β : Type*} {G : Graph α β}
    (v : V(G)) (ear : G.Ear (noEdge {v.1} β)) (hkind : ear.kind = .closed) (hadd : ear.add = G) :
    ∃ d : G.EarDecomposition G,
      d.IsVertexStart ∧ d.length = 1 ∧ ∀ i, d.kindAt i = .closed := by
  suffices h : ∀ K (_ : K = G) (d : G.EarDecomposition K),
      d.IsVertexStart ∧ d.length = 1 ∧ (∀ i, d.kindAt i = .closed) →
        ∃ d : G.EarDecomposition G, d.IsVertexStart ∧ d.length = 1 ∧ ∀ i, d.kindAt i = .closed by
    refine h _ hadd ((EarDecomposition.vertex v).snoc ear) ⟨by simp, by simp, fun i ↦ ?_⟩
    obtain rfl : i = Fin.cast (EarDecomposition.length_snoc _ _).symm
        (Fin.last (EarDecomposition.vertex v).length) := by
      have hi := i.isLt
      simp only [EarDecomposition.length_snoc, EarDecomposition.length_vertex] at hi
      exact Fin.ext <| by
        simp only [Fin.val_cast, Fin.val_last, EarDecomposition.length_vertex]
        omega
    rw [EarDecomposition.kindAt_eq, EarDecomposition.earAt_snoc_last, hkind]
  rintro _ rfl d hd
  exact ⟨d, hd⟩

/-! ### Two parallel edges -/

/-- Two vertices `0` and `1` joined by the two parallel edges `0` and `1`. -/
abbrev parallel : Graph (Fin 2) (Fin 2) := banana 0 1 univ

/-- The edge `0` joins `0` to `1`. -/
theorem parallel_isLink_zero : parallel.IsLink 0 0 1 := by simp

/-- The edge `1` joins `1` to `0`. -/
theorem parallel_isLink_one : parallel.IsLink 1 1 0 := by simp

/-- The two parallel edges have edge connectivity two. -/
theorem edgeConnectivity_parallel : parallel.edgeConnectivity = 2 := by
  rw [edgeConnectivity_banana (by decide), encard_univ]
  simp

/-- Neither of the two parallel edges is a bridge. -/
theorem parallel_not_isBridge (e : Fin 2) : ¬ parallel.IsBridge e := by
  fin_cases e
  · exact not_isBridge_banana (f := 1) (mem_univ _) (by decide)
  · exact not_isBridge_banana (f := 0) (mem_univ _) (by decide)

/-- The closed walk from `0` to `1` along the edge `0` and back along the edge `1`. -/
def parallelCycle : parallel.Walk 0 0 :=
  .cons 0 parallel_isLink_zero (.cons 1 parallel_isLink_one .nil)

/-- The two parallel edges form a cycle of length two. -/
theorem parallelCycle_isCycle : parallelCycle.IsCycle := by
  simp [parallelCycle]

/-- The cycle through both parallel edges has length two. -/
theorem length_parallelCycle : parallelCycle.length = 2 := by
  simp [parallelCycle]

/-- The cycle through both parallel edges traces the whole graph. -/
theorem walkGraph_parallelCycle : parallel.walkGraph parallelCycle = parallel := by
  refine (Compatible.of_le (parallelCycle.walkGraph_le (by simp))).ext ?_ ?_
  · ext x
    fin_cases x <;> simp [parallelCycle]
  · ext e
    fin_cases e <;> simp [parallelCycle]

/-- The two-edge cycle is a closed ear over the vertex `0`. -/
def parallelEar : parallel.Ear (noEdge {0} (Fin 2)) :=
  .closed (noEdge_le_iff.mpr (by simp)) parallelCycle parallelCycle_isCycle
    (mem_singleton 0)
    (by simp [parallelCycle]) (by simp)

/-- The two-edge ear is closed. -/
theorem kind_parallelEar : parallelEar.kind = .closed :=
  Ear.kind_closed ..

/-- The two-edge ear traces the whole graph. -/
theorem toGraph_parallelEar : parallelEar.toGraph = parallel :=
  (Ear.toGraph_closed ..).trans walkGraph_parallelCycle

/-- Adjoining the closed ear to the vertex `0` gives the whole graph. -/
theorem add_parallelEar : parallelEar.add = parallel :=
  (Compatible.of_le parallelEar.add_le).ext
    (by rw [Ear.vertexSet_add, toGraph_parallelEar]; simp)
    (by rw [Ear.edgeSet_add, toGraph_parallelEar]; simp)

/-- Starting from the vertex `0`, the two parallel edges form one closed ear. -/
theorem exists_closed_earDecomposition_parallel :
    ∃ d : parallel.EarDecomposition parallel,
      d.IsVertexStart ∧ d.length = 1 ∧ ∀ i, d.kindAt i = .closed :=
  exists_closed_earDecomposition_of_add_eq ⟨0, by simp⟩ parallelEar kind_parallelEar
    add_parallelEar

/-- The orientation sending the edge `0` from `0` to `1` and the edge `1` back from `1` to `0`. -/
def parallelOrientation : parallel.Orientation where
  tail e := if e.1 = 0 then ⟨0, by simp⟩ else ⟨1, by simp⟩
  head e := if e.1 = 0 then ⟨1, by simp⟩ else ⟨0, by simp⟩
  isLink e := by
    obtain ⟨e, -⟩ := e
    fin_cases e <;> simp

/-- Orienting the two parallel edges in opposite directions is strongly connected. -/
theorem parallelOrientation_isStronglyConnected :
    @Quiver.IsStronglyConnected V(parallel) ⟨parallelOrientation.Hom⟩ := by
  let : Quiver V(parallel) := ⟨parallelOrientation.Hom⟩
  have forward : (⟨0, by simp⟩ : V(parallel)) ⟶ ⟨1, by simp⟩ :=
    ⟨⟨0, by simp⟩, by simp [parallelOrientation], by simp [parallelOrientation]⟩
  have backward : (⟨1, by simp⟩ : V(parallel)) ⟶ ⟨0, by simp⟩ :=
    ⟨⟨1, by simp⟩, by simp [parallelOrientation], by simp [parallelOrientation]⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  simp only [vertexSet_banana, mem_insert_iff, mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact ⟨.nil⟩
  · exact ⟨forward.toPath⟩
  · exact ⟨backward.toPath⟩
  · exact ⟨.nil⟩

/-! ### The single-edge simplification -/

/-- The vertices `0` and `1` joined by the edge `0` alone. -/
abbrev single : Graph (Fin 2) (Fin 2) := banana 0 1 {0}

/-- The underlying simple graph of the two parallel edges is the complete graph on their ends. -/
theorem toSimpleGraph_parallel : parallel.toSimpleGraph = ⊤ := by
  ext ⟨x, hx⟩ ⟨y, hy⟩
  simp only [vertexSet_banana, mem_insert_iff, mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

/-- Keeping only one of the two parallel edges leaves the same underlying simple graph. -/
theorem toSimpleGraph_single : single.toSimpleGraph = ⊤ := by
  ext ⟨x, hx⟩ ⟨y, hy⟩
  simp only [vertexSet_banana, mem_insert_iff, mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

/-- The single edge is a bridge. -/
theorem single_isBridge : single.IsBridge 0 :=
  isBridge_banana_singleton (by decide) 0

/-- The single edge has edge connectivity one. -/
theorem edgeConnectivity_single : single.edgeConnectivity = 1 := by
  rw [edgeConnectivity_banana (by decide), encard_singleton]

/-- No orientation of the single edge is strongly connected, since a strongly connected orientation
forces `2`-edge-connectivity. -/
theorem not_exists_stronglyConnected_orientation_single :
    ¬ ∃ o : single.Orientation, @Quiver.IsStronglyConnected V(single) ⟨o.Hom⟩ := fun h ↦ by
  have := (isEdgeConnected_banana_iff (k := 2) (by decide)).mp
    (isEdgeConnected_two_of_exists_stronglyConnected_orientation h)
  simp at this

/-! ### A loop -/

/-- One vertex carrying one loop. -/
abbrev loop : Graph Unit Unit := bouquet () univ

/-- The loop joins its vertex to itself. -/
theorem loop_isLink : loop.IsLink () () () := by simp

/-- The loop traversed once. -/
def loopCycle : loop.Walk () () := loop_isLink.toWalk

/-- A loop is a cycle of length one. -/
theorem loopCycle_isCycle : loopCycle.IsCycle :=
  loop_isLink.isCycle_toWalk

/-- The loop traversed once has length one. -/
theorem length_loopCycle : loopCycle.length = 1 := by
  simp [loopCycle]

/-- The loop is a closed ear over its vertex. -/
def loopEar : loop.Ear (noEdge {()} Unit) :=
  .closed (noEdge_le_iff.mpr (by simp)) loopCycle loopCycle_isCycle
    (mem_singleton ())
    (by simp [loopCycle]) (by simp)

/-- The loop ear is closed. -/
theorem kind_loopEar : loopEar.kind = .closed :=
  Ear.kind_closed ..

/-- The loop ear traces the graph of its walk. -/
theorem toGraph_loopEar : loopEar.toGraph = loop.walkGraph loopCycle :=
  Ear.toGraph_closed ..

/-- Adjoining the loop to its vertex gives the whole graph. -/
theorem add_loopEar : loopEar.add = loop :=
  (Compatible.of_le loopEar.add_le).ext
    (by ext; simp)
    (by rw [Ear.edgeSet_add, toGraph_loopEar, Walk.edgeSet_walkGraph]; ext; simp [loopCycle])

/-- Starting from its vertex, the loop forms one closed ear. -/
theorem exists_closed_earDecomposition_loop :
    ∃ d : loop.EarDecomposition loop,
      d.IsVertexStart ∧ d.length = 1 ∧ ∀ i, d.kindAt i = .closed :=
  exists_closed_earDecomposition_of_add_eq ⟨(), by simp⟩ loopEar kind_loopEar add_loopEar

/-- A loop is not a bridge. -/
theorem loop_not_isBridge : ¬ loop.IsBridge () :=
  IsLoopAt.not_isBridge (x := ()) (by simp)

/-- A loop crosses no edge cut. -/
theorem edgeCut_loop (S : Set Unit) : loop.edgeCut S = ∅ :=
  eq_empty_of_forall_notMem fun _ ↦ IsLoopAt.notMem_edgeCut (x := ()) (by simp)

/-- The edge set of `loop` is finite, so cut capacities are defined. -/
noncomputable local instance : Fintype E(loop) := Fintype.ofFinite _

/-- Whatever capacity the loop carries, every cut has capacity zero. -/
theorem edgeCutCapacity_loop {K : Type*} [AddCommMonoid K] (c : E(loop) → K)
    (S : Finset V(loop)) : loop.edgeCutCapacity c S = 0 := by
  classical
  rw [edgeCutCapacity_def]
  simp [edgeCut_loop]

end TauCeti.Examples.MultigraphEars
