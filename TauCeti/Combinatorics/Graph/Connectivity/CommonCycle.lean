/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.VertexConnectivity
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.CommonCycle

/-!
# Common-cycle characterizations of vertex connectivity for multigraphs

Vertex connectivity of a multigraph depends only on its underlying simple graph on the actual
vertices. This file characterizes two-vertex-connectivity using cycles in `G.toSimpleGraph`, as
loops and parallel edge identities play no role in these vertex-connectivity consequences.

For a connected graph on at least three actual vertices, two-vertex-connectivity is equivalent to
every vertex and edge, or every two distinct edges, of its simplification lying on a common cycle.
The vertex-only characterization applies directly because `Graph.IsVertexConnected` is defined
through simplification.

## References

* R. Diestel, *Graph Theory*, 6th ed., Sections 3.1 and 3.3.
-/

public section

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- For a connected multigraph on finitely many actual vertices, at least three of them,
two-vertex-connectivity is equivalent to every actual vertex and every edge of the simplification
lying on a common cycle. -/
theorem isVertexConnected_two_iff_forall_exists_toSimpleGraph_isCycle_mem_edges [Finite V(G)]
    (hconn : G.Connected) (hcard : 3 ≤ Nat.card V(G)) :
    G.IsVertexConnected 2 ↔
      ∀ (x : V(G)) {e : Sym2 V(G)}, e ∈ G.toSimpleGraph.edgeSet →
        ∃ c : G.toSimpleGraph.Walk x x, c.IsCycle ∧ e ∈ c.edges :=
  SimpleGraph.isVertexConnected_two_iff_forall_exists_isCycle_mem_edges
    (connected_iff_toSimpleGraph_connected.mp hconn) hcard

/-- For a connected multigraph on finitely many actual vertices, at least three of them,
two-vertex-connectivity is equivalent to every pair of distinct simplification edges lying on a
common cycle. -/
theorem isVertexConnected_two_iff_forall_exists_toSimpleGraph_isCycle_mem_edges_mem_edges
    [Finite V(G)] (hconn : G.Connected) (hcard : 3 ≤ Nat.card V(G)) :
    G.IsVertexConnected 2 ↔
      ∀ ⦃e f : Sym2 V(G)⦄, e ∈ G.toSimpleGraph.edgeSet → f ∈ G.toSimpleGraph.edgeSet → e ≠ f →
        ∃ (x : V(G)) (c : G.toSimpleGraph.Walk x x),
          c.IsCycle ∧ e ∈ c.edges ∧ f ∈ c.edges :=
  SimpleGraph.isVertexConnected_two_iff_forall_exists_isCycle_mem_edges_mem_edges
    (connected_iff_toSimpleGraph_connected.mp hconn) hcard

end Graph
