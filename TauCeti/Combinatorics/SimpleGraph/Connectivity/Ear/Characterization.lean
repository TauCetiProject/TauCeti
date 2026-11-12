/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.OfSimpleGraph

/-!
# Ear characterization of two-edge-connected simple graphs

A finite simple graph is `2`-edge-connected exactly when it can be built from one vertex by
repeatedly adjoining open or closed ears.  The forward direction transports the multigraph ear
characterization along `Graph.ofSimpleGraph`; the converse is the finiteness-free preservation
theorem for simple-graph ear decompositions.

## Main result

* `SimpleGraph.isEdgeConnected_two_iff_exists_isVertexStart_earDecomposition` is the ear
  characterization of finite `2`-edge-connected simple graphs.
-/

public section

universe u

namespace SimpleGraph.EarDecomposition

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

/-- An ear decomposition starts from a single vertex rather than a cycle. -/
def IsVertexStart (d : G.EarDecomposition H) : Prop :=
  ∃ v : V, d.initial = G.singletonSubgraph v

/-- Characterization of a vertex-starting simple-graph ear decomposition by its initial
subgraph. -/
theorem isVertexStart_iff (d : G.EarDecomposition H) :
    d.IsVertexStart ↔ ∃ v : V, d.initial = G.singletonSubgraph v :=
  Iff.rfl

end SimpleGraph.EarDecomposition

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- **Ear characterization of two-edge-connectivity.** A finite simple graph is
`2`-edge-connected exactly when it admits an ear decomposition built from one vertex by adjoining
open or closed ears. -/
theorem isEdgeConnected_two_iff_exists_isVertexStart_earDecomposition
    [Finite V] [Nonempty V] :
    G.IsEdgeConnected 2 ↔
      ∃ d : G.EarDecomposition ⊤, d.IsVertexStart := by
  constructor
  · intro hG
    let v : V := Classical.arbitrary V
    have hv : v ∈ (Graph.ofSimpleGraph G).vertexSet := by simp
    obtain ⟨d, hinitial⟩ :=
      ((Graph.isEdgeConnected_ofSimpleGraph_iff G 2).mpr hG).exists_earDecomposition ⟨v, hv⟩
    obtain ⟨d', _, hinitial'⟩ := d.exists_toSimpleGraph
    have hfinal :
        (Graph.ofSimpleGraph G).toSimpleGraphSubgraph d.final_le = (⊤ : G.Subgraph) := by
      ext x y
      · simp
      · simp
    let d'' := d'.copy hfinal
    refine ⟨d'', v, ?_⟩
    rw [show d'' = d'.copy hfinal from rfl,
      SimpleGraph.EarDecomposition.initial_copy, hinitial']
    have hgraph0 : d.graphAfter 0 = Graph.noEdge {v} (Sym2 V) :=
      d.initial_eq_graphAfter.symm.trans hinitial
    have hnoEdge : Graph.noEdge {v} (Sym2 V) ≤ Graph.ofSimpleGraph G :=
      hgraph0 ▸ d.graphAfter_le 0
    exact (Graph.toSimpleGraphSubgraph_congr hgraph0 (d.graphAfter_le 0) hnoEdge).trans
      (Graph.noEdge_toSimpleGraphSubgraph v hnoEdge)
  · rintro ⟨d, _⟩
    exact d.isEdgeConnected_two

end SimpleGraph
