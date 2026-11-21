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
common end. The cases `k = 0`, an empty graph, and isolated vertices are included. The theorem
holds for every finite palette `C` with `Nat.card C` colours, including the empty palette; it is
transported from `Fin k` by relabelling colours along an equivalence.

The proof embeds the graph in a finite `k`-regular bipartite multigraph, decomposes the completion
into `k` perfect matchings, colours by the matching indices, and restricts the colouring back to
the original graph. The matching-partition formulation, with matchings indexed by an arbitrary
finite palette, and the chromatic-number formulation are included as equivalent interfaces.
Consequently the least number of colours is the largest number of edges at a vertex, which is zero
for the empty graph; for a simple graph this is its maximum degree.
For a finite bipartite simple graph the theorem is also stated through colourings of Mathlib's
`SimpleGraph.lineGraph`.

## References

* D. Kőnig, *Gráfok és alkalmazásuk a determinánsok és a halmazok elméletére*, Mat.
  Természett. Ért. 34 (1916), 104--119.
* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Section 5.3.
-/

public section

open Set

universe u v w

namespace Graph

variable {α : Type u} {β : Type v} {C : Type w} {G : Graph α β} {L R : Finset V(G)} {k : ℕ}

namespace IsBipartition

/-- **Kőnig's edge-colouring theorem.** A finite bipartite multigraph admits a proper
edge-colouring by any finite palette `C` exactly when every actual vertex is incident with
at most `Nat.card C` actual edges. Empty palettes and parallel edges are included. -/
theorem nonempty_edgeColoring_iff_forall_incidenceCount_le [Finite E(G)] [Finite C]
    (hLR : G.IsBipartition L R) :
    Nonempty (G.EdgeColoring C) ↔
      ∀ x ∈ V(G), G.incidenceCount x ≤ Nat.card C := by
  constructor
  · rintro ⟨c⟩ x -
    simpa using c.incidenceCount_le_card x
  · intro hk
    obtain ⟨G', L', R', hC⟩ := hLR.exists_isRegularCompletion hk
    let _ : Finite E(G') := hC.finite_edgeSet
    let _ : G'.Loopless := hC.isBipartition.loopless
    obtain ⟨M, hM, hdisj, hcover⟩ :=
      hC.isBipartition.exists_perfectMatching_decomposition hC.isRegularOfDegree
    have hc : Nonempty (G'.EdgeColoring (Fin (Nat.card C))) :=
      nonempty_edgeColoring_iff_exists_matchings.mpr
        ⟨M, fun i ↦ (isPerfectMatching_def.mp (hM i)).1, hdisj, hcover⟩
    exact (hc.map hC.restrictEdgeColoring).map
      (G.lineGraph.recolorOfEquiv (Finite.equivFin C).symm)

/-- A finite bipartite multigraph has its actual edge set partitioned into a family of matchings
indexed by a finite type `C` exactly when every actual vertex is incident with at most
`Nat.card C` actual edges. Empty matchings are allowed, and `C` may be empty. -/
theorem exists_matching_partition_iff_forall_incidenceCount_le [Finite E(G)] [Finite C]
    (hLR : G.IsBipartition L R) :
    (∃ M : C → Set E(G), (∀ i, G.IsMatching (M i)) ∧
      (Pairwise fun i j ↦ Disjoint (M i) (M j)) ∧ ⋃ i, M i = univ) ↔
      ∀ x ∈ V(G), G.incidenceCount x ≤ Nat.card C := by
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
  change Nonempty (G.EdgeColoring (Fin k)) ↔ _
  simpa using (hLR.nonempty_edgeColoring_iff_forall_incidenceCount_le (C := Fin k))

/-- In a finite bipartite multigraph, the chromatic number of the line graph is the largest
incidence count over the bipartition sides `L` and `R`, which cover all actual vertices. This
supremum is zero for the empty graph, when `L = R = ∅`. -/
theorem chromaticNumber_lineGraph_eq_sup_incidenceCount [Finite E(G)]
    (hLR : G.IsBipartition L R) :
    G.lineGraph.chromaticNumber =
      (L.sup (fun x : V(G) ↦ G.incidenceCount x) ⊔ R.sup (fun x : V(G) ↦ G.incidenceCount x) :
        ℕ) := by
  refine le_antisymm (hLR.chromaticNumber_lineGraph_le_iff_forall_incidenceCount_le.2
    fun x hx ↦ ?_) ?_
  · rcases hLR.mem_or_mem ⟨x, hx⟩ with hxL | hxR
    · exact (Finset.le_sup (f := fun y : V(G) ↦ G.incidenceCount y) hxL).trans le_sup_left
    · exact (Finset.le_sup (f := fun y : V(G) ↦ G.incidenceCount y) hxR).trans le_sup_right
  · have hcast (S : Finset V(G)) :
        ((S.sup fun x : V(G) ↦ G.incidenceCount x : ℕ) : ℕ∞) =
          S.sup fun x : V(G) ↦ (G.incidenceCount x : ℕ∞) :=
      Finset.apply_sup_eq_sup_comp _ (fun _ _ ↦ Nat.mono_cast.map_max) (by simp)
    rw [Nat.mono_cast.map_max, hcast, hcast]
    exact max_le (Finset.sup_le fun x _ ↦ G.incidenceCount_le_chromaticNumber_lineGraph x)
      (Finset.sup_le fun x _ ↦ G.incidenceCount_le_chromaticNumber_lineGraph x)

end IsBipartition

end Graph

namespace SimpleGraph

variable {α : Type u} {k : ℕ}

/-- **Kőnig's line-colouring theorem.** The chromatic index of a finite bipartite simple graph
is its maximum degree. Both are zero when the vertex type is empty. -/
theorem IsBipartite.chromaticIndex_eq_maxDegree {H : SimpleGraph α} [Fintype α]
    [DecidableRel H.Adj] (hH : H.IsBipartite) :
    H.chromaticIndex = H.maxDegree := by
  obtain ⟨L, R, hLR⟩ := hH.exists_isBipartition_ofSimpleGraph
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

/-- **Kőnig's edge-colouring theorem.** A finite bipartite simple graph is edge-colourable by
`k` colours exactly when its maximum degree is at most `k`. -/
theorem IsBipartite.edgeColorable_iff_maxDegree_le {H : SimpleGraph α} [Fintype α]
    [DecidableRel H.Adj] (hH : H.IsBipartite) :
    H.EdgeColorable k ↔ H.maxDegree ≤ k := by
  rw [← chromaticIndex_le_iff_edgeColorable, hH.chromaticIndex_eq_maxDegree, Nat.cast_le]

end SimpleGraph
