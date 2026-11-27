/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.VertexConnectivity
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.CommonCycle
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.PrescribedCycle

/-!
# Cycle and fan consequences of vertex connectivity for multigraphs

Vertex connectivity of a multigraph depends only on its underlying simple graph on the actual
vertices. This file gives the multigraph-facing forms of the common-cycle theorem, the fan lemma,
and Dirac's prescribed-vertex cycle theorem. Their witnesses are walks in `G.toSimpleGraph`, as
loops and parallel edge identities play no role in these vertex-connectivity consequences.

The common-cycle characterizations say that a connected graph on at least three actual vertices
is two-vertex-connected exactly when every two vertices, every vertex and edge, or every two
distinct edges of its simplification lie on a common cycle. The fan and prescribed-cycle results
apply at every vertex-connectivity threshold.

## References

* R. Diestel, *Graph Theory*, 6th ed., Sections 3.1 and 3.3.
* G. A. Dirac, *In abstrakten Graphen vorhandene vollst\u00e4ndige 4-Graphen und ihre
  Unterteilungen*, Math. Nachr. 22 (1960), 61--85.
-/

public section

open Finset

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

/-! ### Common cycles -/

/-- Two distinct actual vertices of a two-vertex-connected multigraph lie on a common cycle of
its simplification. -/
theorem IsVertexConnected.exists_toSimpleGraph_isCycle_mem_support [Finite V(G)]
    (hG : G.IsVertexConnected 2) {x y : V(G)} (hxy : x ≠ y) :
    ∃ c : G.toSimpleGraph.Walk x x, c.IsCycle ∧ y ∈ c.support :=
  SimpleGraph.IsVertexConnected.exists_isCycle_mem_support hG hxy

/-- On finitely many actual vertices, at least three of them, a multigraph is
two-vertex-connected exactly when every two distinct actual vertices lie on a common cycle of its
simplification. -/
theorem isVertexConnected_two_iff_forall_exists_toSimpleGraph_isCycle_mem_support [Finite V(G)]
    (hcard : 3 ≤ Nat.card V(G)) :
    G.IsVertexConnected 2 ↔
      ∀ x y : V(G), x ≠ y →
        ∃ c : G.toSimpleGraph.Walk x x, c.IsCycle ∧ y ∈ c.support :=
  SimpleGraph.isVertexConnected_two_iff_forall_exists_isCycle_mem_support hcard

/-- Every actual vertex and every edge of the simplification of a two-vertex-connected multigraph
lie on a common cycle. -/
theorem IsVertexConnected.exists_toSimpleGraph_isCycle_mem_edges [Finite V(G)]
    (hG : G.IsVertexConnected 2) (x : V(G)) {e : Sym2 V(G)}
    (he : e ∈ G.toSimpleGraph.edgeSet) :
    ∃ c : G.toSimpleGraph.Walk x x, c.IsCycle ∧ e ∈ c.edges :=
  SimpleGraph.IsVertexConnected.exists_isCycle_mem_edges hG x he

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

/-- Any two edges of the simplification of a two-vertex-connected multigraph lie on a common
cycle, which may be based at either endpoint of the first edge. -/
theorem IsVertexConnected.exists_toSimpleGraph_isCycle_mem_edges_mem_edges [Finite V(G)]
    (hG : G.IsVertexConnected 2) {x : V(G)} {e f : Sym2 V(G)}
    (he : e ∈ G.toSimpleGraph.edgeSet) (hf : f ∈ G.toSimpleGraph.edgeSet) (hx : x ∈ e) :
    ∃ c : G.toSimpleGraph.Walk x x, c.IsCycle ∧ e ∈ c.edges ∧ f ∈ c.edges :=
  SimpleGraph.IsVertexConnected.exists_isCycle_mem_edges_mem_edges hG he hf hx

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

/-! ### Fans and prescribed vertices -/

/-- In a `k`-vertex-connected multigraph on finitely many actual vertices, an actual vertex `x`
outside a set `U` of at least `k` vertices is joined to `U` by a fan of `k` paths in the
simplification. The ends are distinct, the other vertices of each path avoid `U`, and different
paths meet only at `x`. -/
theorem IsVertexConnected.exists_toSimpleGraph_fan [Finite V(G)] {k : ℕ}
    (hG : G.IsVertexConnected k) {x : V(G)} {U : Finset V(G)} (hx : x ∉ U) (hU : k ≤ #U) :
    ∃ (u : Fin k → V(G)) (P : ∀ i, G.toSimpleGraph.Walk x (u i)),
      Function.Injective u ∧ (∀ i, u i ∈ U) ∧ (∀ i, (P i).IsPath) ∧
        (∀ i, ∀ y ∈ (P i).support, y ≠ u i → y ∉ U) ∧
        Pairwise fun i j ↦ ∀ y ∈ (P i).support, y ∈ (P j).support → y = x :=
  SimpleGraph.IsVertexConnected.exists_fan hG hx hU

/-- For `2 ≤ k`, every set of at most `k` actual vertices of a `k`-vertex-connected multigraph
on finitely many actual vertices lies on a common cycle of its simplification. -/
theorem IsVertexConnected.exists_toSimpleGraph_isCycle_forall_mem_support [Finite V(G)]
    {k : ℕ} (hk : 2 ≤ k) (hG : G.IsVertexConnected k) {S : Finset V(G)} (hS : #S ≤ k) :
    ∃ (x : V(G)) (c : G.toSimpleGraph.Walk x x),
      c.IsCycle ∧ ∀ y ∈ S, y ∈ c.support :=
  SimpleGraph.IsVertexConnected.exists_isCycle_forall_mem_support hk hG hS

end Graph
