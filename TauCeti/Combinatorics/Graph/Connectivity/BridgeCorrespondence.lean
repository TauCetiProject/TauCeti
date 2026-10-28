import TauCeti.Combinatorics.Graph.Connectivity.Bridge

/-!
# Bridge correspondence for simple graphs

A bridge in a simple graph is also a bridge in its multigraph representation,
and conversely, for edges belonging to the original graph.
-/

/-- An edge of a simple graph is a bridge exactly when it is a bridge
in the corresponding multigraph. -/
theorem SimpleGraph.isBridge_iff_ofSimpleGraph {α : Type*} (H : SimpleGraph α)
    {x y : α} (h : H.Adj x y) :
    H.IsBridge s(x, y) ↔ (Graph.ofSimpleGraph H).IsBridge s(x, y) := by
  have hl : (Graph.ofSimpleGraph H).IsLink s(x, y) x y := by
    simpa [Graph.ofSimpleGraph_isLink] using h
  constructor
  · intro hb
    apply hl.isBridge_iff_forall_walk_mem_edges.mpr
    intro p
    have hm : s(x, y) ∈ p.toSimpleGraph.edges :=
      (H.isBridge_iff_forall_walk_mem_edges).mp hb p.toSimpleGraph
    simpa using hm
  · intro hb
    apply H.isBridge_iff_forall_walk_mem_edges.mpr
    intro p
    have hm : s(x, y) ∈ p.toGraph.edges :=
      hl.isBridge_iff_forall_walk_mem_edges.mp hb p.toGraph
    simpa using hm
