/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.Coloring
public import TauCeti.Combinatorics.Graph.Matching.Regular

/-!
# Edge-colouring bipartite multigraphs

Kőnig's edge-colouring theorem says that a finite bipartite multigraph has a proper
edge-colouring by `k` colours exactly when every vertex is incident with at most `k` edges.
Parallel edges retain their identities and therefore receive different colours when they have a
common end. The cases `k = 0`, an empty graph, and isolated vertices are included.

The proof embeds the graph in a finite `k`-regular bipartite multigraph, decomposes the completion
into `k` perfect matchings, colours by the matching indices, and restricts the colouring back to
the original graph. The matching-partition and chromatic-number formulations are included as
equivalent interfaces.

## References

* D. Kőnig, *Gráfok és alkalmazásuk a determinánsok és a halmazok elméletére*, Mat.
  Természett. Ért. 34 (1916), 104--119.
* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Section 5.3.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {L R : Finset V(G)} {k : ℕ}

namespace IsBipartition

/-- **Kőnig's edge-colouring theorem.** A finite bipartite multigraph admits a proper
edge-colouring by `k` colours exactly when every actual vertex is incident with at most `k`
actual edges. -/
theorem nonempty_edgeColoring_iff_forall_incidenceCount_le [Finite E(G)]
    (hLR : G.IsBipartition L R) :
    Nonempty (G.EdgeColoring (Fin k)) ↔
      ∀ x ∈ V(G), G.incidenceCount x ≤ k := by
  constructor
  · rintro ⟨c⟩ x -
    simpa using c.incidenceCount_le_card x
  · intro hk
    obtain ⟨G', L', R', hC⟩ := hLR.exists_isRegularCompletion hk
    let _ : Finite E(G') := hC.finite_edgeSet
    let _ : G'.Loopless := hC.isBipartition.loopless
    obtain ⟨M, hM, hdisj, hcover⟩ :=
      hC.isBipartition.exists_perfectMatching_decomposition hC.isRegularOfDegree
    have hc : Nonempty (G'.EdgeColoring (Fin k)) :=
      nonempty_edgeColoring_iff_exists_matchings.mpr
        ⟨M, fun i ↦ (isPerfectMatching_def.mp (hM i)).1, hdisj, hcover⟩
    exact hc.map hC.restrictEdgeColoring

/-- A finite bipartite multigraph has its actual edge set partitioned into `k` matchings exactly
when every actual vertex is incident with at most `k` actual edges. Empty matchings are allowed. -/
theorem exists_matching_partition_iff_forall_incidenceCount_le [Finite E(G)]
    (hLR : G.IsBipartition L R) :
    (∃ M : Fin k → Set E(G), (∀ i, G.IsMatching (M i)) ∧
      (Pairwise fun i j ↦ Disjoint (M i) (M j)) ∧ ⋃ i, M i = univ) ↔
      ∀ x ∈ V(G), G.incidenceCount x ≤ k := by
  let _ : G.Loopless := hLR.loopless
  rw [← hLR.nonempty_edgeColoring_iff_forall_incidenceCount_le,
    nonempty_edgeColoring_iff_exists_matchings]

/-- For a finite bipartite multigraph, the line graph is colourable by at most `k` colours exactly
when every actual vertex is incident with at most `k` actual edges. -/
theorem chromaticNumber_lineGraph_le_iff_forall_incidenceCount_le [Finite E(G)]
    (hLR : G.IsBipartition L R) :
    G.lineGraph.chromaticNumber ≤ k ↔
      ∀ x ∈ V(G), G.incidenceCount x ≤ k := by
  rw [SimpleGraph.chromaticNumber_le_iff_colorable]
  exact hLR.nonempty_edgeColoring_iff_forall_incidenceCount_le

end IsBipartition

end Graph

namespace SimpleGraph

variable {α : Type u} {k : ℕ}

/-- Kőnig's edge-colouring theorem for a finite simple graph with a displayed covering
bipartition. Its multigraph edge-colourings by `Fin k` exist exactly when the maximum degree of
the simple graph is at most `k`. -/
theorem nonempty_edgeColoring_ofSimpleGraph_iff_maxDegree_le (H : SimpleGraph α) [Fintype α]
    [DecidableRel H.Adj] {L R : Finset ↥(Graph.ofSimpleGraph H).vertexSet}
    (hLR : (Graph.ofSimpleGraph H).IsBipartition L R) :
    Nonempty ((Graph.ofSimpleGraph H).EdgeColoring (Fin k)) ↔ H.maxDegree ≤ k := by
  rw [hLR.nonempty_edgeColoring_iff_forall_incidenceCount_le]
  constructor
  · intro h
    apply H.maxDegree_le_of_forall_degree_le
    intro x
    simpa using h x (by simp)
  · intro hk x _
    simpa using (H.degree_le_maxDegree x).trans hk

/-- **Kőnig's line-colouring theorem for simple graphs.** For a finite simple graph with a
displayed covering bipartition, the chromatic number of its line graph is its maximum degree.
The maximum degree, and hence the chromatic number, is zero on the empty vertex type. -/
theorem chromaticNumber_lineGraph_eq_maxDegree (H : SimpleGraph α) [Fintype α]
    [DecidableRel H.Adj] {L R : Finset ↥(Graph.ofSimpleGraph H).vertexSet}
    (hLR : (Graph.ofSimpleGraph H).IsBipartition L R) :
    H.lineGraph.chromaticNumber = H.maxDegree := by
  rw [← Graph.chromaticNumber_lineGraph_ofSimpleGraph]
  apply le_antisymm
  · exact (hLR.chromaticNumber_lineGraph_le_iff_forall_incidenceCount_le).2
      fun x _ ↦ by simpa using H.degree_le_maxDegree x
  · cases isEmpty_or_nonempty α with
    | inl => simp
    | inr =>
      obtain ⟨x, hx⟩ := H.exists_maximal_degree_vertex
      rw [hx, ← Graph.incidenceCount_ofSimpleGraph]
      exact Graph.incidenceCount_le_chromaticNumber_lineGraph _ x

end SimpleGraph
