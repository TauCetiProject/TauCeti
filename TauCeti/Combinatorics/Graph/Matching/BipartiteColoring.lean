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

Kőnig's edge-colouring theorem says that a finite bipartite multigraph can be properly
edge-coloured with `k` colours exactly when every vertex is incident with at most `k` edges.
Parallel edges retain their identities and therefore receive distinct colours when they share an
endpoint. The theorem includes the empty and edgeless cases, where `k = 0` is allowed.

The proof embeds the graph in a finite `k`-regular bipartite multigraph, decomposes the completion
into `k` perfect matchings, regards the matching partition as an edge-colouring, and restricts the
colouring to the original graph.

## Main results

* `Graph.IsBipartition.nonempty_edgeColoring_fin_iff`: **Kőnig's edge-colouring theorem** for
  bipartite multigraphs.
* `Graph.IsBipartition.chromaticNumber_lineGraph_eq_sup_incidenceCount`: the least number of
  colours is the maximum incidence count, with value zero when there are no actual vertices.

## References

* D. Kőnig, *Gráfok és alkalmazásuk a determinánsok és a halmazok elméletére*,
  Mat. Természettud. Értesítő 34 (1916), 104--119.
-/

public section

open Finset

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {L R : Finset V(G)} {k : ℕ}

namespace IsBipartition

/-- **Kőnig's edge-colouring theorem.** A finite bipartite multigraph has a proper
edge-colouring by `k` colours if and only if every actual vertex is incident with at most `k`
actual edges. Parallel edges are counted separately. -/
theorem nonempty_edgeColoring_fin_iff [Finite E(G)] (hLR : G.IsBipartition L R) :
    Nonempty (G.EdgeColoring (Fin k)) ↔
      ∀ x ∈ V(G), G.incidenceCount x ≤ k := by
  constructor
  · rintro ⟨c⟩ x _
    simpa using c.incidenceCount_le_card x
  · intro hk
    obtain ⟨G', L', R', hC⟩ := hLR.exists_isRegularCompletion hk
    let _ : Finite E(G') := hC.finite_edgeSet
    obtain ⟨M, hM, hdisj, hcover⟩ :=
      hC.isBipartition.exists_perfectMatching_decomposition hC.isRegularOfDegree
    let _ : G'.Loopless := hC.isBipartition.loopless
    have hc : Nonempty (G'.EdgeColoring (Fin k)) :=
      nonempty_edgeColoring_iff_exists_matchings.2
        ⟨M, fun i ↦ (isPerfectMatching_def.1 (hM i)).1, hdisj, hcover⟩
    exact hc.map hC.restrictEdgeColoring

/-- In a finite bipartite multigraph, the chromatic number of the line graph is the largest
incidence count of an actual vertex. The supremum over the empty vertex type is zero. -/
theorem chromaticNumber_lineGraph_eq_sup_incidenceCount [Finite E(G)]
    (hLR : G.IsBipartition L R) :
    G.lineGraph.chromaticNumber =
      (Finset.sup L (fun x : V(G) ↦ G.incidenceCount x) ⊔
        Finset.sup R (fun x : V(G) ↦ G.incidenceCount x) : ℕ) := by
  classical
  refine le_antisymm (α := ℕ∞) ?_ ?_
  · rw [SimpleGraph.chromaticNumber_le_iff_colorable]
    refine hLR.nonempty_edgeColoring_fin_iff.2 fun x hx ↦ ?_
    rcases hLR.mem_or_mem ⟨x, hx⟩ with hxL | hxR
    · exact (Finset.le_sup (f := fun y : V(G) ↦ G.incidenceCount y) hxL).trans le_sup_left
    · exact (Finset.le_sup (f := fun y : V(G) ↦ G.incidenceCount y) hxR).trans le_sup_right
  · have hcast (S : Finset V(G)) :
        ((Finset.sup S (fun x : V(G) ↦ G.incidenceCount x) : ℕ) : ℕ∞) =
          Finset.sup S (fun x : V(G) ↦ (G.incidenceCount x : ℕ∞)) :=
      Finset.apply_sup_eq_sup_comp (fun n : ℕ ↦ (n : ℕ∞))
        (fun x y ↦ WithTop.coe_sup x y) WithTop.coe_bot
    calc
      ((max (Finset.sup L fun x : V(G) ↦ G.incidenceCount x)
          (Finset.sup R fun x : V(G) ↦ G.incidenceCount x) : ℕ) : ℕ∞) =
          max (Finset.sup L fun x : V(G) ↦ (G.incidenceCount x : ℕ∞))
            (Finset.sup R fun x : V(G) ↦ (G.incidenceCount x : ℕ∞)) := by
              exact (WithTop.coe_sup _ _).trans (congrArg₂ max (hcast L) (hcast R))
      _ ≤ G.lineGraph.chromaticNumber := max_le
        (Finset.sup_le fun x _ ↦ G.incidenceCount_le_chromaticNumber_lineGraph x)
        (Finset.sup_le fun x _ ↦ G.incidenceCount_le_chromaticNumber_lineGraph x)

end IsBipartition

end Graph
