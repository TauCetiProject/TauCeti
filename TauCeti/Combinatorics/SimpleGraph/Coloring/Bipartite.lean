/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import TauCeti.Combinatorics.SimpleGraph.Coloring.Edge

import TauCeti.Combinatorics.Graph.Matching.EdgeColoring
import TauCeti.Combinatorics.Graph.Matching.OfSimpleGraph

/-!
# Kőnig's edge-colouring theorem and chromatic index of finite bipartite simple graphs

Kőnig's edge-colouring theorem states that a finite bipartite simple graph admits a proper
`k`-edge-colouring if and only if its maximum degree is at most `k`, so its chromatic index equals
its maximum degree (`0` on an empty vertex type). Equivalently, its edge set partitions into `k`
pairwise disjoint matching subgraphs, with empty matchings allowed.

These results are transported from the finite multigraph theorem in
`TauCeti.Combinatorics.Graph.Matching.EdgeColoring` and the matching-partition transport in
`TauCeti.Combinatorics.Graph.Matching.OfSimpleGraph` along `Graph.ofSimpleGraph`.

## Main results

* `SimpleGraph.IsBipartite.chromaticIndex_eq_maxDegree`: the chromatic index of a finite bipartite
  simple graph equals its maximum degree.
* `SimpleGraph.IsBipartite.edgeColorable_iff_maxDegree_le` and
  `SimpleGraph.IsBipartite.edgeColorable_maxDegree`: a finite bipartite simple graph is
  `k`-edge-colourable if and only if `G.maxDegree ≤ k`, and in particular is
  `G.maxDegree`-edge-colourable.
* `SimpleGraph.IsBipartite.exists_matching_partition_iff_maxDegree_le`: the edges of a finite
  bipartite simple graph partition into `k` pairwise disjoint matchings if and only if
  `G.maxDegree ≤ k`.

## References

* D. Kőnig, *Gráfok és alkalmazásuk a determinánsok és a halmazok elméletére*, Mat. Természett.
  Ért. 34 (1916), 104--119.
* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Section 5.3.
-/

public section

open Function

universe u

namespace SimpleGraph.IsBipartite

variable {V : Type u} {G : SimpleGraph V} {k : ℕ}

/-- **Kőnig's line-colouring theorem.** The chromatic index of a finite bipartite simple graph is
its maximum degree (`0` when `V` is empty). -/
theorem chromaticIndex_eq_maxDegree [Fintype V] [DecidableRel G.Adj] (hbip : G.IsBipartite) :
    G.chromaticIndex = G.maxDegree := by
  refine le_antisymm ?_ G.maxDegree_le_chromaticIndex
  obtain ⟨L, R, hLR⟩ := hbip.exists_isBipartition_ofSimpleGraph
  rw [← Graph.chromaticNumber_lineGraph_ofSimpleGraph]
  exact hLR.chromaticNumber_lineGraph_le_iff_forall_incidenceCount_le.2 fun x _ ↦
    (Graph.incidenceCount_ofSimpleGraph G x).trans_le (G.degree_le_maxDegree x)

/-- **Kőnig's edge-colouring theorem.** A finite bipartite simple graph is `k`-edge-colourable if
and only if its maximum degree is at most `k`. -/
theorem edgeColorable_iff_maxDegree_le [Fintype V] [DecidableRel G.Adj] (hbip : G.IsBipartite) :
    G.EdgeColorable k ↔ G.maxDegree ≤ k := by
  rw [← G.chromaticIndex_le_iff_edgeColorable, hbip.chromaticIndex_eq_maxDegree, Nat.cast_le]

/-- Every finite bipartite simple graph is `G.maxDegree`-edge-colourable. -/
theorem edgeColorable_maxDegree [Fintype V] [DecidableRel G.Adj] (hbip : G.IsBipartite) :
    G.EdgeColorable G.maxDegree :=
  hbip.edgeColorable_iff_maxDegree_le.2 le_rfl

/-- The edges of a finite bipartite simple graph partition into `k` pairwise disjoint matchings if
and only if its maximum degree is at most `k`. Empty matchings are allowed. -/
theorem exists_matching_partition_iff_maxDegree_le [Fintype V] [DecidableRel G.Adj]
    (hbip : G.IsBipartite) :
    (∃ M : Fin k → G.Subgraph, (∀ i, (M i).IsMatching) ∧
      Pairwise (Disjoint on fun i ↦ (M i).edgeSet) ∧ ⋃ i, (M i).edgeSet = G.edgeSet) ↔
      G.maxDegree ≤ k := by
  rw [← G.edgeColorable_iff_exists_matchings, hbip.edgeColorable_iff_maxDegree_le]

end SimpleGraph.IsBipartite
