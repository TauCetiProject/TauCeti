/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import TauCeti.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.Combinatorics.SimpleGraph.Matching.Hall

import TauCeti.Combinatorics.Graph.Matching.OfSimpleGraph
import TauCeti.Combinatorics.Graph.Matching.OrdinaryHall
import TauCeti.Combinatorics.Graph.Matching.VertexCover
import TauCeti.Data.Set.Card

/-!
# Kőnig's theorem and the Kőnig–Ore deficiency formula for simple graphs

This file establishes matching–cover duality, **Kőnig's theorem**, and the **Kőnig–Ore deficiency
formula** for `SimpleGraph`, expressed in Mathlib's canonical `SimpleGraph.Subgraph.IsMatching`,
`SimpleGraph.IsVertexCover`, and `SimpleGraph.vertexCoverNum` interfaces. Elementary matched-vertex
bijections and general Hall marriage equivalences live in
`TauCeti.Combinatorics.SimpleGraph.Matching.Hall` and are re-exported here.

In any simple graph `G`, every matching `M` has extended edge cardinality at most that of every
vertex cover, and hence at most `G.vertexCoverNum`; neither finiteness nor bipartiteness is
needed. Moreover, replacing any subset `S` of a vertex cover `C` by `⋃ x ∈ S, G.neighborSet x`
produces another vertex cover (`SimpleGraph.IsVertexCover.sdiff_union_biUnion_neighborSet`),
giving the general cover-deficiency bound

`|M| + |S| ≤ |C| + |⋃ x ∈ S, G.neighborSet x|`

on arbitrary simple graphs; specializing to `C = L` for `G.IsBipartiteWith L R` yields the
**Kőnig–Ore inequality** in `ℕ∞` with no finiteness assumptions, and in `ℕ` whenever `L` and the
neighbourhood union of `S` are finite.

When `V` is finite, transferring ordinary multigraph Kőnig and Kőnig–Ore duality across
`Graph.ofSimpleGraph G` and `SimpleGraph.matchingSubgraph` (after enlarging `R` to `Lᶜ` so that
any isolated vertices outside `L ∪ R` are covered without altering neighbourhoods of subsets of
`L`) proves equality:

* **Kőnig's theorem**: some matching `M` and some vertex cover `C` satisfy
  `M.edgeSet.ncard = C.ncard`, and some matching attains `M.edgeSet.encard = G.vertexCoverNum`;
* **the Kőnig–Ore formula**: for `G.IsBipartiteWith L R`, some matching `M` and some `S ⊆ L`
  satisfy `M.edgeSet.ncard + S.ncard = L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard`, so the
  greatest matching size is `L.ncard - sSup ((fun S ↦ S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard)
  '' {S | S ⊆ L})`.

At zero deficiency, Kőnig–Ore characterizes the existence of a matching of size `L.ncard` (or a
perfect matching on a covering bipartition `L ∪ R = Set.univ`) by Hall's neighbourhood condition on
one side.

## Main declarations

* `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_le_encard_of_isVertexCover` and
  `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_le_vertexCoverNum`: matching–cover weak duality
  for arbitrary simple graphs.
* `SimpleGraph.IsVertexCover.sdiff_union_biUnion_neighborSet`,
  `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_add_encard_le_of_isVertexCover`, and
  `SimpleGraph.Subgraph.IsMatching.ncard_edgeSet_add_ncard_le_of_isVertexCover`: cover-modification
  and general cover-deficiency inequalities on arbitrary simple graphs, specialized to
  `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_add_encard_le` and
  `SimpleGraph.Subgraph.IsMatching.ncard_edgeSet_add_ncard_le` for bipartite graphs.
* `SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_ncard_eq`,
  `SimpleGraph.IsBipartite.exists_isMatching_encard_edgeSet_eq_vertexCoverNum`, and
  `SimpleGraph.IsBipartite.iSup_encard_edgeSet_isMatching_eq_vertexCoverNum`: **Kőnig's theorem**
  for finite bipartite simple graphs.
* `SimpleGraph.IsBipartiteWith.exists_isMatching_ncard_edgeSet_add_ncard_eq` and
  `SimpleGraph.IsBipartiteWith.isGreatest_ncard_edgeSet_isMatching`: **the Kőnig–Ore deficiency
  formula** in witness and numerical forms, together with right-side versions.
* `SimpleGraph.IsBipartiteWith.exists_isMatching_ncard_edgeSet_eq_ncard_iff` and
  `SimpleGraph.IsBipartiteWith.exists_isPerfectMatching_iff_ncard_eq_and_forall_ncard_le`:
  compatibility between the extremal Kőnig–Ore formula and Hall's condition on each side.

## Implementation notes

Mathlib's `SimpleGraph.IsBipartiteWith L R` permits isolated vertices outside `L ∪ R`, whereas a
multigraph bipartition `(Graph.ofSimpleGraph G).IsBipartition L' R'` partitions the entire vertex
set `V(Graph.ofSimpleGraph G)`. Before invoking the finite multigraph Kőnig and Kőnig–Ore theorems,
`SimpleGraph.IsBipartiteWith.exists_isBipartition_ofSimpleGraph_compl` replaces `R` with `Lᶜ`,
absorbing any isolated vertices into the right class without changing the neighbourhoods of subsets
of `L`.

## References

* D. Kőnig, *Gráfok és mátrixok*, Mat. Fiz. Lapok 38 (1931).
* P. Hall, *On representatives of subsets*, J. London Math. Soc. 10 (1935).
* Ø. Ore, *Graphs and matching theorems*, Duke Math. J. 22 (1955).
* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Section 2.1.
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Section 21.1.
-/

public section

open Function Set
open scoped Graph

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Weak duality between matchings and vertex covers -/

namespace Subgraph.IsMatching

/-- **Weak duality for simple-graph matchings.** In any simple graph, the edge set of a matching
has extended cardinality at most that of any vertex cover. -/
theorem encard_edgeSet_le_encard_of_isVertexCover {M : G.Subgraph} (hM : M.IsMatching)
    {C : Set V} (hC : G.IsVertexCover C) :
    M.edgeSet.encard ≤ C.encard := by
  have hC' : (Graph.ofSimpleGraph G).IsVertexCover (Subtype.val ⁻¹' C) :=
    isVertexCover_ofSimpleGraph_preimage_iff.2 hC
  have hle := hM.toGraphEdgeSet.encard_le_encard_of_isVertexCover hC'
  have hpre : (Subtype.val ⁻¹' C : Set V(Graph.ofSimpleGraph G)).encard = C.encard := by
    rw [← Set.encard_image_val, Subtype.image_preimage_coe]
    simp
  rwa [M.encard_toGraphEdgeSet, hpre] at hle

/-- In any simple graph, the number of edges in a matching is at most the cardinality of any
finite vertex cover. -/
theorem ncard_edgeSet_le_ncard_of_isVertexCover {M : G.Subgraph} (hM : M.IsMatching)
    {C : Set V} (hC : G.IsVertexCover C) (hCf : C.Finite := by toFinite_tac) :
    M.edgeSet.ncard ≤ C.ncard :=
  Set.ncard_le_ncard_of_encard_le (hM.encard_edgeSet_le_encard_of_isVertexCover hC) hCf

/-- **Weak duality with the vertex cover number.** Every matching of `G` has extended edge
cardinality at most `G.vertexCoverNum`. -/
theorem encard_edgeSet_le_vertexCoverNum {M : G.Subgraph} (hM : M.IsMatching) :
    M.edgeSet.encard ≤ G.vertexCoverNum := by
  obtain ⟨C, hCnum, hC⟩ := G.vertexCoverNum_exists
  exact hCnum ▸ hM.encard_edgeSet_le_encard_of_isVertexCover hC

/-- When `G.vertexCoverNum` is finite, every matching has at most `G.vertexCoverNum.toNat`
edges. -/
theorem ncard_edgeSet_le_toNat_vertexCoverNum {M : G.Subgraph} (hM : M.IsMatching)
    (hG : G.vertexCoverNum ≠ ⊤ := by simp) :
    M.edgeSet.ncard ≤ G.vertexCoverNum.toNat := by
  rw [Set.ncard_def]
  exact ENat.toNat_le_toNat hM.encard_edgeSet_le_vertexCoverNum hG

end Subgraph.IsMatching

/-! ### Cover-modification and the Kőnig–Ore inequality -/

/-- Replacing any subset `S` of a vertex cover `C` by the union of the neighbourhoods of `S`
produces another vertex cover of `G`. -/
theorem IsVertexCover.sdiff_union_biUnion_neighborSet {C : Set V} (hC : G.IsVertexCover C)
    (S : Set V) :
    G.IsVertexCover ((C \ S) ∪ ⋃ x ∈ S, G.neighborSet x) := by
  intro u w hadj
  rcases hC hadj with huC | hwC
  · by_cases huS : u ∈ S
    · exact .inr <| .inr <| Set.mem_biUnion huS hadj
    · exact .inl <| .inl ⟨huC, huS⟩
  · by_cases hwS : w ∈ S
    · exact .inl <| .inr <| Set.mem_biUnion hwS hadj.symm
    · exact .inr <| .inl ⟨hwC, hwS⟩

/-- **Normalized Kőnig–Ore vertex cover.** If `G.IsBipartiteWith L R`, then for any `S : Set V`
the set `(L \ S) ∪ ⋃ x ∈ S, G.neighborSet x` is a vertex cover of `G`. -/
theorem IsBipartiteWith.isVertexCover_sdiff_union_biUnion_neighborSet {L R S : Set V}
    (h : G.IsBipartiteWith L R) :
    G.IsVertexCover ((L \ S) ∪ ⋃ x ∈ S, G.neighborSet x) :=
  h.isVertexCover_left.sdiff_union_biUnion_neighborSet S

namespace Subgraph.IsMatching

/-- **General cover-deficiency inequality** in extended cardinalities: for any simple graph `G`,
any matching `M`, any vertex cover `C` of `G`, and any `S ⊆ C`,
`M.edgeSet.encard + S.encard ≤ C.encard + (⋃ x ∈ S, G.neighborSet x).encard`. -/
theorem encard_edgeSet_add_encard_le_of_isVertexCover {M : G.Subgraph} (hM : M.IsMatching)
    {C S : Set V} (hC : G.IsVertexCover C) (hS : S ⊆ C) :
    M.edgeSet.encard + S.encard ≤ C.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
  have hcov : M.edgeSet.encard ≤ ((C \ S) ∪ ⋃ x ∈ S, G.neighborSet x).encard :=
    hM.encard_edgeSet_le_encard_of_isVertexCover (hC.sdiff_union_biUnion_neighborSet S)
  calc
    M.edgeSet.encard + S.encard ≤
        ((C \ S).encard + (⋃ x ∈ S, G.neighborSet x).encard) + S.encard :=
      add_le_add_left (hcov.trans (Set.encard_union_le _ _)) S.encard
    _ = ((C \ S).encard + S.encard) + (⋃ x ∈ S, G.neighborSet x).encard := by ac_rfl
    _ = C.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
      rw [Set.encard_sdiff_add_encard_of_subset hS]

/-- **General cover-deficiency inequality** in `Set.ncard` form: for any simple graph `G`, any
matching `M`, any finite vertex cover `C`, and any `S ⊆ C` with finite neighbourhood union,
`M.edgeSet.ncard + S.ncard ≤ C.ncard + (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem ncard_edgeSet_add_ncard_le_of_isVertexCover {M : G.Subgraph} (hM : M.IsMatching)
    {C S : Set V} (hC : G.IsVertexCover C) (hS : S ⊆ C)
    (hCf : C.Finite := by toFinite_tac)
    (hNf : (⋃ x ∈ S, G.neighborSet x).Finite := by toFinite_tac) :
    M.edgeSet.ncard + S.ncard ≤ C.ncard + (⋃ x ∈ S, G.neighborSet x).ncard := by
  have hMf : M.edgeSet.Finite := by
    rw [← Set.encard_lt_top_iff]
    exact (hM.encard_edgeSet_le_encard_of_isVertexCover hC).trans_lt hCf.encard_lt_top
  have hSf : S.Finite := hCf.subset hS
  have hle := hM.encard_edgeSet_add_encard_le_of_isVertexCover hC hS
  rw [← hMf.cast_ncard_eq, ← hSf.cast_ncard_eq, ← hCf.cast_ncard_eq, ← hNf.cast_ncard_eq] at hle
  exact_mod_cast hle

/-- **The Kőnig–Ore inequality** in extended cardinalities. For any bipartite simple graph
`G.IsBipartiteWith L R`, any matching `M`, and any `S ⊆ L`,
`M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard`, without finiteness
assumptions. -/
theorem encard_edgeSet_add_encard_le {M : G.Subgraph} (hM : M.IsMatching) {L R S : Set V}
    (h : G.IsBipartiteWith L R) (hS : S ⊆ L) :
    M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard :=
  hM.encard_edgeSet_add_encard_le_of_isVertexCover h.isVertexCover_left hS

/-- **The Kőnig–Ore inequality** for subsets of the right side `R` in extended cardinalities. -/
theorem encard_edgeSet_add_encard_right_le {M : G.Subgraph} (hM : M.IsMatching) {L R T : Set V}
    (h : G.IsBipartiteWith L R) (hT : T ⊆ R) :
    M.edgeSet.encard + T.encard ≤ R.encard + (⋃ y ∈ T, G.neighborSet y).encard :=
  hM.encard_edgeSet_add_encard_le h.symm hT

/-- **The Kőnig–Ore inequality** in `Set.ncard` form, valid whenever `L` and the neighbourhood
union of `S` are finite. -/
theorem ncard_edgeSet_add_ncard_le {M : G.Subgraph} (hM : M.IsMatching) {L R S : Set V}
    (h : G.IsBipartiteWith L R) (hS : S ⊆ L)
    (hLf : L.Finite := by toFinite_tac)
    (hNf : (⋃ x ∈ S, G.neighborSet x).Finite := by toFinite_tac) :
    M.edgeSet.ncard + S.ncard ≤ L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard :=
  hM.ncard_edgeSet_add_ncard_le_of_isVertexCover h.isVertexCover_left hS hLf hNf

/-- **The Kőnig–Ore inequality** for subsets of the right side `R` in `Set.ncard` form. -/
theorem ncard_edgeSet_add_ncard_right_le {M : G.Subgraph} (hM : M.IsMatching) {L R T : Set V}
    (h : G.IsBipartiteWith L R) (hT : T ⊆ R)
    (hRf : R.Finite := by toFinite_tac)
    (hNf : (⋃ y ∈ T, G.neighborSet y).Finite := by toFinite_tac) :
    M.edgeSet.ncard + T.ncard ≤ R.ncard + (⋃ y ∈ T, G.neighborSet y).ncard :=
  hM.ncard_edgeSet_add_ncard_le h.symm hT hRf hNf

end Subgraph.IsMatching

/-! ### Kőnig's theorem and the Kőnig–Ore formula for finite bipartite simple graphs -/

section FiniteBipartite

variable [Finite V]

/-- **Kőnig's theorem for finite bipartite simple graphs.** Every finite bipartite simple graph
has a matching `M` and a vertex cover `C` of equal cardinality. -/
theorem IsBipartite.exists_isMatching_isVertexCover_ncard_eq (h : G.IsBipartite) :
    ∃ (M : G.Subgraph) (C : Set V),
      M.IsMatching ∧ G.IsVertexCover C ∧ M.edgeSet.ncard = C.ncard := by
  obtain ⟨_, _, hLR⟩ := h.exists_isBipartiteWith
  obtain ⟨_, _, hLR', -, -⟩ := hLR.exists_isBipartition_ofSimpleGraph_compl
  obtain ⟨M₀, C₀, hM₀, hC₀, hMC₀⟩ := hLR'.exists_isMatching_isVertexCover_ncard_eq
  refine ⟨G.matchingSubgraph M₀, Subtype.val '' C₀,
    (G.matchingSubgraph_isMatching_iff M₀).2 hM₀,
    G.isVertexCover_ofSimpleGraph_image_iff.2 hC₀, ?_⟩
  rw [G.ncard_edgeSet_matchingSubgraph M₀, Set.ncard_image_val, hMC₀]

/-- **Kőnig's theorem with `vertexCoverNum`.** Every finite bipartite simple graph has a matching
whose extended edge cardinality equals `G.vertexCoverNum`. -/
theorem IsBipartite.exists_isMatching_encard_edgeSet_eq_vertexCoverNum (h : G.IsBipartite) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = G.vertexCoverNum := by
  obtain ⟨_, _, hLR⟩ := h.exists_isBipartiteWith
  obtain ⟨_, _, hLR', -, -⟩ := hLR.exists_isBipartition_ofSimpleGraph_compl
  obtain ⟨M₀, hM₀, hM₀num⟩ := hLR'.exists_isMatching_encard_eq_vertexCoverNum
  refine ⟨G.matchingSubgraph M₀, (G.matchingSubgraph_isMatching_iff M₀).2 hM₀, ?_⟩
  rw [G.encard_edgeSet_matchingSubgraph M₀, hM₀num, vertexCoverNum_toSimpleGraph_ofSimpleGraph]

/-- Every finite bipartite simple graph has a matching of size `G.vertexCoverNum.toNat`. -/
theorem IsBipartite.exists_isMatching_ncard_edgeSet_eq_toNat_vertexCoverNum (h : G.IsBipartite) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = G.vertexCoverNum.toNat := by
  obtain ⟨M, hM, hMnum⟩ := h.exists_isMatching_encard_edgeSet_eq_vertexCoverNum
  exact ⟨M, hM, by rw [Set.ncard_def, hMnum]⟩

/-- **Kőnig's min-max identity for finite bipartite simple graphs.** The supremum of the extended
edge cardinalities of all matchings of `G` equals `G.vertexCoverNum`. -/
theorem IsBipartite.iSup_encard_edgeSet_isMatching_eq_vertexCoverNum (h : G.IsBipartite) :
    (⨆ (M : G.Subgraph) (_ : M.IsMatching), M.edgeSet.encard) = G.vertexCoverNum := by
  obtain ⟨M, hM, hMnum⟩ := h.exists_isMatching_encard_edgeSet_eq_vertexCoverNum
  refine le_antisymm (iSup₂_le fun N hN ↦ hN.encard_edgeSet_le_vertexCoverNum) ?_
  exact hMnum ▸ le_iSup₂ (f := fun (N : G.Subgraph) (_ : N.IsMatching) ↦ N.edgeSet.encard) M hM

/-- **The Kőnig–Ore deficiency formula** in witness form for finite bipartite simple graphs: for
any `G.IsBipartiteWith L R` (even if isolated vertices lie outside `L ∪ R`), some matching `M` and
some `S ⊆ L` satisfy `M.edgeSet.ncard + S.ncard = L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem IsBipartiteWith.exists_isMatching_ncard_edgeSet_add_ncard_eq {L R : Set V}
    (h : G.IsBipartiteWith L R) :
    ∃ (M : G.Subgraph) (S : Set V), M.IsMatching ∧ S ⊆ L ∧
      M.edgeSet.ncard + S.ncard = L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard := by
  obtain ⟨L', R', hLR', hL', hR'⟩ := h.exists_isBipartition_ofSimpleGraph_compl
  obtain ⟨M₀, S₀, hM₀, hS₀, hMS₀⟩ := hLR'.exists_isMatching_card_add_card_eq
  let S : Set V := Subtype.val '' (S₀ : Set V(Graph.ofSimpleGraph G))
  have hSL : S ⊆ L := hL' ▸ Set.image_mono (Finset.coe_subset.2 hS₀)
  refine ⟨G.matchingSubgraph (M₀ : Set E(Graph.ofSimpleGraph G)), S,
    (G.matchingSubgraph_isMatching_iff _).2 hM₀, hSL, ?_⟩
  have hN : Subtype.val ''
      ((Graph.ofSimpleGraph G).neighborsIn S₀ R' : Set V(Graph.ofSimpleGraph G)) =
        ⋃ x ∈ S, G.neighborSet x :=
    image_neighborsIn_ofSimpleGraph_of_isBipartiteWith h.compl_right hSL hR'.symm.subset
  have hScard : S.ncard = S₀.card := Set.ncard_image_val_coe_finset S₀
  have hLcard : L.ncard = L'.card := hL' ▸ Set.ncard_image_val_coe_finset L'
  have hNcard :
      (⋃ x ∈ S, G.neighborSet x).ncard = ((Graph.ofSimpleGraph G).neighborsIn S₀ R').card :=
    hN ▸ Set.ncard_image_val_coe_finset _
  rw [G.ncard_edgeSet_matchingSubgraph, Set.ncard_coe_finset, hScard, hLcard, hNcard, hMS₀]

/-- **The Kőnig–Ore deficiency formula** for subsets of the right side `R` of a finite bipartite
simple graph. -/
theorem IsBipartiteWith.exists_isMatching_ncard_edgeSet_add_ncard_right_eq {L R : Set V}
    (h : G.IsBipartiteWith L R) :
    ∃ (M : G.Subgraph) (T : Set V), M.IsMatching ∧ T ⊆ R ∧
      M.edgeSet.ncard + T.ncard = R.ncard + (⋃ y ∈ T, G.neighborSet y).ncard :=
  h.symm.exists_isMatching_ncard_edgeSet_add_ncard_eq

/-- **The numerical Kőnig–Ore deficiency formula** for finite bipartite simple graphs: the
greatest edge cardinality of a matching of `G` is
`L.ncard - sSup ((fun S ↦ S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard) '' {S | S ⊆ L})`. -/
theorem IsBipartiteWith.isGreatest_ncard_edgeSet_isMatching {L R : Set V}
    (h : G.IsBipartiteWith L R) :
    IsGreatest {n | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = n}
      (L.ncard -
        sSup ((fun S : Set V ↦ S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard) '' {S | S ⊆ L})) := by
  set f : Set V → ℕ := fun S ↦ S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard
  set D : Set ℕ := f '' {S | S ⊆ L}
  have hDne : D.Nonempty := ⟨f ∅, ∅, Set.empty_subset L, rfl⟩
  have hDmax := hDne.isGreatest_csSup (Set.toFinite D)
  obtain ⟨T, hTL, hTf⟩ := hDmax.1
  have hub {M : G.Subgraph} (hM : M.IsMatching) : M.edgeSet.ncard ≤ L.ncard - sSup D := by
    have hML : M.edgeSet.ncard ≤ L.ncard :=
      hM.ncard_edgeSet_le_ncard_of_isVertexCover h.isVertexCover_left
    have hMT := hM.ncard_edgeSet_add_ncard_le h hTL
    have hTf' : sSup D = T.ncard - (⋃ x ∈ T, G.neighborSet x).ncard := hTf.symm
    omega
  refine ⟨?_, fun n ⟨M, hM, hMn⟩ ↦ hMn ▸ hub hM⟩
  obtain ⟨M, S, hM, hSL, hMS⟩ := h.exists_isMatching_ncard_edgeSet_add_ncard_eq
  have hSd : S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard ≤ sSup D := hDmax.2 ⟨S, hSL, rfl⟩
  have hMub := hub hM
  exact ⟨M, hM, by omega⟩

/-- **The numerical Kőnig–Ore deficiency formula** in terms of subsets of the right side `R`. -/
theorem IsBipartiteWith.isGreatest_ncard_edgeSet_isMatching_right {L R : Set V}
    (h : G.IsBipartiteWith L R) :
    IsGreatest {n | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = n}
      (R.ncard -
        sSup ((fun T : Set V ↦ T.ncard - (⋃ y ∈ T, G.neighborSet y).ncard) '' {T | T ⊆ R})) :=
  h.symm.isGreatest_ncard_edgeSet_isMatching

/-! ### Compatibility of the Kőnig–Ore formula with Hall's condition -/

/-- **Compatibility of the Kőnig–Ore formula with Hall's theorem** on finite bipartite simple
graphs: a matching of size `L.ncard` (equivalently, by
`SimpleGraph.Subgraph.IsMatching.ncard_edgeSet_eq_ncard_iff_subset_verts`, a matching saturating
`L`) exists if and only if `S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard` for every `S ⊆ L`. -/
theorem IsBipartiteWith.exists_isMatching_ncard_edgeSet_eq_ncard_iff {L R : Set V}
    (h : G.IsBipartiteWith L R) :
    (∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = L.ncard) ↔
      ∀ S ⊆ L, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  constructor
  · rintro ⟨M, hM, hML⟩ S hSL
    have hle := hM.ncard_edgeSet_add_ncard_le h hSL
    omega
  · intro hHall
    obtain ⟨M, S, hM, hSL, hMS⟩ := h.exists_isMatching_ncard_edgeSet_add_ncard_eq
    have hML : M.edgeSet.ncard ≤ L.ncard :=
      hM.ncard_edgeSet_le_ncard_of_isVertexCover h.isVertexCover_left
    have hSN := hHall S hSL
    exact ⟨M, hM, by omega⟩

/-- **Compatibility of the Kőnig–Ore formula with Hall's theorem** on the right side `R` of a
finite bipartite simple graph: a matching of size `R.ncard` exists if and only if
`T.ncard ≤ (⋃ y ∈ T, G.neighborSet y).ncard` for every `T ⊆ R`. -/
theorem IsBipartiteWith.exists_isMatching_ncard_edgeSet_eq_ncard_right_iff {L R : Set V}
    (h : G.IsBipartiteWith L R) :
    (∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = R.ncard) ↔
      ∀ T ⊆ R, T.ncard ≤ (⋃ y ∈ T, G.neighborSet y).ncard :=
  h.symm.exists_isMatching_ncard_edgeSet_eq_ncard_iff

/-- On a finite simple graph with a covering bipartition (`L ∪ R = Set.univ`), a perfect matching
exists if and only if `L.ncard = R.ncard` and Hall's condition holds for subsets of `L`. -/
theorem IsBipartiteWith.exists_isPerfectMatching_iff_ncard_eq_and_forall_ncard_le
    {L R : Set V} (h : G.IsBipartiteWith L R) (hcover : L ∪ R = Set.univ) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      L.ncard = R.ncard ∧ ∀ S ⊆ L, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  constructor
  · rintro ⟨M, hM, hspan⟩
    have hLM : L ⊆ M.verts := hspan.verts_eq_univ ▸ Set.subset_univ L
    have hRM : R ⊆ M.verts := hspan.verts_eq_univ ▸ Set.subset_univ R
    have hLcard := (hM.ncard_edgeSet_eq_ncard_iff_subset_verts h).2 hLM
    have hRcard := (hM.ncard_edgeSet_eq_ncard_iff_subset_verts h.symm).2 hRM
    exact ⟨hLcard.symm.trans hRcard,
      h.exists_isMatching_ncard_edgeSet_eq_ncard_iff.1 ⟨M, hM, hLcard⟩⟩
  · rintro ⟨hLRcard, hHall⟩
    obtain ⟨M, hM, hML⟩ := h.exists_isMatching_ncard_edgeSet_eq_ncard_iff.2 hHall
    have hLM : L ⊆ M.verts := (hM.ncard_edgeSet_eq_ncard_iff_subset_verts h).1 hML
    have hRM : R ⊆ M.verts :=
      (hM.ncard_edgeSet_eq_ncard_iff_subset_verts h.symm).1 (hML.trans hLRcard)
    refine ⟨M, hM, Subgraph.isSpanning_iff.2 ?_⟩
    exact Set.Subset.antisymm (Set.subset_univ _) (hcover ▸ Set.union_subset hLM hRM)

/-- On a finite simple graph with a covering bipartition (`L ∪ R = Set.univ`), a perfect matching
exists if and only if `L.ncard = R.ncard` and Hall's condition holds for subsets of `R`. -/
theorem IsBipartiteWith.exists_isPerfectMatching_iff_ncard_eq_and_forall_ncard_le_right
    {L R : Set V} (h : G.IsBipartiteWith L R) (hcover : L ∪ R = Set.univ) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      L.ncard = R.ncard ∧ ∀ T ⊆ R, T.ncard ≤ (⋃ y ∈ T, G.neighborSet y).ncard := by
  rw [h.symm.exists_isPerfectMatching_iff_ncard_eq_and_forall_ncard_le
    (Set.union_comm L R ▸ hcover), eq_comm]

end FiniteBipartite

end SimpleGraph
