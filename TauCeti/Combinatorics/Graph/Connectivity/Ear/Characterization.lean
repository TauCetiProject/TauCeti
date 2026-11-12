/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.EdgeConnected
public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Extension

/-!
# Ear characterization of two-edge-connected multigraphs

A finite multigraph with a nonempty vertex set is `2`-edge-connected exactly when it can be built
from one vertex by repeatedly adjoining open or closed ears.  The forward direction iterates the
single-ear extension theorem: as long as a prefix graph is proper, two-edge-connectivity supplies
an ear that strictly enlarges it.  Finiteness of the actual vertex and edge sets makes this
iteration terminate.

The construction can start with any ear decomposition of a prefix graph.  In particular, it can
start at any chosen actual vertex.  Combined with the finiteness-free converse proved in
`Ear.EdgeConnected`, this gives the full ear characterization.

The argument follows R. Diestel, *Graph Theory*, Chapter 3, with edge identities retained for
parallel edges and loops.

## Main results

* `Graph.IsEdgeConnected.exists_earDecomposition_of_earDecomposition`: extend any existing prefix
  decomposition to the whole graph.
* `Graph.IsEdgeConnected.exists_earDecomposition`: construct a decomposition starting at a chosen
  vertex.
* `Graph.isEdgeConnected_two_iff_exists_isVertexStart_earDecomposition`: the ear characterization
  of finite `2`-edge-connected multigraphs.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G H K : Graph α β}

/-- The number of actual vertices and edges of `G` not yet accounted for by the sizes of a
subgraph `H`.  It is used only as the termination measure for adjoining ears. -/
private noncomputable def remainingSize (G H : Graph α β) : ℕ :=
  V(G).ncard + E(G).ncard - (V(H).ncard + E(H).ncard)

/-- Strictly enlarging a subgraph of a graph with finite actual vertex and edge sets strictly
decreases `remainingSize`. -/
private theorem remainingSize_lt [Finite V(G)] [Finite E(G)] (hHK : H < K) (hKG : K ≤ G) :
    remainingSize G K < remainingSize G H := by
  have hVG : V(G).Finite := Set.toFinite _
  have hEG : E(G).Finite := Set.toFinite _
  have hVK : V(K).Finite := hVG.subset hKG.vertexSet_mono
  have hEK : E(K).Finite := hEG.subset hKG.edgeSet_mono
  have hsize : V(H).ncard + E(H).ncard < V(K).ncard + E(K).ncard := by
    rcases vertexSet_ssubset_or_edgeSet_ssubset_of_lt hHK with hV | hE
    · exact Nat.add_lt_add_of_lt_of_le (Set.ncard_lt_ncard hV hVK)
        (Set.ncard_le_ncard hHK.le.edgeSet_mono hEK)
    · exact Nat.add_lt_add_of_le_of_lt (Set.ncard_le_ncard hHK.le.vertexSet_mono hVK)
        (Set.ncard_lt_ncard hE hEK)
  have hbound : V(K).ncard + E(K).ncard ≤ V(G).ncard + E(G).ncard :=
    Nat.add_le_add (Set.ncard_le_ncard hKG.vertexSet_mono hVG)
      (Set.ncard_le_ncard hKG.edgeSet_mono hEG)
  simp only [remainingSize]
  omega

/-- An ear decomposition of a prefix subgraph of a finite `2`-edge-connected multigraph extends
to an ear decomposition of the whole graph with the same initial graph. -/
theorem IsEdgeConnected.exists_earDecomposition_of_earDecomposition
    [Finite V(G)] [Finite E(G)] (hG : G.IsEdgeConnected 2)
    (d₀ : G.EarDecomposition H) :
    ∃ d : G.EarDecomposition G, d.initial = d₀.initial := by
  classical
  generalize hr : remainingSize G H = r
  induction r using Nat.strong_induction_on generalizing H with
  | ind r ih =>
      by_cases hHG : H = G
      · subst H
        exact ⟨d₀, rfl⟩
      · have hlt : H < G := lt_of_le_of_ne d₀.final_le hHG
        obtain ⟨ear, hear⟩ := d₀.vertexSet_nonempty.exists_ear_of_lt hlt hG
        have hrem : remainingSize G ear.add < r :=
          (remainingSize_lt hear ear.add_le).trans_eq hr
        obtain ⟨d, hinit⟩ := ih _ hrem (d₀.snoc ear) rfl
        exact ⟨d, hinit.trans (by simp)⟩

/-- A finite `2`-edge-connected multigraph has a vertex-starting ear decomposition beginning at
any chosen actual vertex. -/
theorem IsEdgeConnected.exists_earDecomposition [Finite V(G)] [Finite E(G)]
    (hG : G.IsEdgeConnected 2) (v : V(G)) :
    ∃ d : G.EarDecomposition G, d.initial = Graph.noEdge {v.1} β := by
  obtain ⟨d, hinit⟩ :=
    hG.exists_earDecomposition_of_earDecomposition (EarDecomposition.vertex v)
  exact ⟨d, hinit.trans (by simp)⟩

/-- **Ear characterization of two-edge-connectivity.** A finite multigraph with a nonempty actual
vertex set is `2`-edge-connected exactly when it admits an ear decomposition built from one vertex
by adjoining open or closed ears. -/
theorem isEdgeConnected_two_iff_exists_isVertexStart_earDecomposition
    [Finite V(G)] [Finite E(G)] [Nonempty V(G)] :
    G.IsEdgeConnected 2 ↔ ∃ d : G.EarDecomposition G, d.IsVertexStart :=
  ⟨fun hG ↦ by
      obtain ⟨d, hinit⟩ := hG.exists_earDecomposition (Classical.arbitrary V(G))
      exact ⟨d, (EarDecomposition.isVertexStart_iff d).mpr
        ⟨Classical.arbitrary V(G), hinit⟩⟩,
    fun ⟨d, _⟩ ↦ d.isEdgeConnected_two⟩

end Graph
