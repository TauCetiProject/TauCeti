/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Ear.Transport

/-!
# Ear characterization of edge connectivity in simple graphs

This file derives the finite simple-graph characterization from the edge-labelled multigraph
characterization and the ear-decomposition transport API.
-/

public section

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

namespace EarDecomposition

/-- An ear decomposition starts from a single vertex rather than from a cycle. -/
def IsVertexStart (d : G.EarDecomposition H) : Prop :=
  ∃ v : V, d.initial = G.singletonSubgraph v

theorem isVertexStart_iff (d : G.EarDecomposition H) :
    d.IsVertexStart ↔ ∃ v : V, d.initial = G.singletonSubgraph v :=
  Iff.rfl

end EarDecomposition

/-- **Ear characterization of two-edge-connectivity for simple graphs.** A finite nonempty simple
graph is `2`-edge-connected exactly when it admits an ear decomposition built from one vertex by
adjoining open or closed ears. -/
theorem isEdgeConnected_two_iff_exists_isVertexStart_earDecomposition
    [Finite V] [Nonempty V] :
    G.IsEdgeConnected 2 ↔
      ∃ d : G.EarDecomposition (⊤ : G.Subgraph), d.IsVertexStart := by
  constructor
  · intro hG
    have hmulti : (Graph.ofSimpleGraph G).IsEdgeConnected 2 :=
      (Graph.isEdgeConnected_ofSimpleGraph_iff G 2).2 hG
    let v : (Graph.ofSimpleGraph G).vertexSet := ⟨Classical.arbitrary V, by simp⟩
    obtain ⟨d, hinit⟩ := hmulti.exists_earDecomposition v
    let d' := d.toSimpleGraphTop
    refine ⟨d', v.1, ?_⟩
    dsimp only [d']
    rw [Graph.EarDecomposition.initial_toSimpleGraphTop]
    have hstage : d.graphAfter 0 = Graph.noEdge {v.1} (Sym2 V) := by
      rw [← d.initial_eq_graphAfter]
      exact hinit
    exact (Graph.toSubgraphOfSimpleGraph_congr hstage
      (d.graphAfter_le 0) (Graph.noEdge_le_iff.mpr (by simp))).trans
        (Graph.toSubgraphOfSimpleGraph_noEdge_singleton v _)
  · rintro ⟨d, -⟩
    exact d.isEdgeConnected_two

end SimpleGraph
