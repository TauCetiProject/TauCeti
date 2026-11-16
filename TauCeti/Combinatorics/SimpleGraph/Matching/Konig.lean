/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hall
public import Mathlib.Combinatorics.SimpleGraph.VertexCover

import TauCeti.Combinatorics.Graph.Matching.OfSimpleGraph
import TauCeti.Combinatorics.Graph.Matching.OrdinaryHall
import TauCeti.Combinatorics.Graph.Matching.VertexCover
import TauCeti.Combinatorics.SimpleGraph.Bipartite

/-!
# Kőnig's theorem and the Kőnig–Ore deficiency formula for simple graphs

This file establishes matching–cover duality, **Kőnig's theorem**, the **Kőnig–Ore deficiency
formula**, and two-way **Hall marriage characterizations** for `SimpleGraph`, expressed in
Mathlib's canonical `SimpleGraph.Subgraph.IsMatching`, `SimpleGraph.IsVertexCover`, and
`SimpleGraph.vertexCoverNum` interfaces.

In any simple graph `G`, every matching `M` has extended edge cardinality at most that of every
vertex cover, and hence at most `G.vertexCoverNum`; neither finiteness nor bipartiteness is
needed. When `G` is bipartite with classes `L` and `R`, every edge of `M` meets `L` in a unique
vertex, giving a canonical bijection `↥(L ∩ M.verts) ≃ M.edgeSet`, while for every `S ⊆ L` the set
`(L \ S) ∪ ⋃ x ∈ S, G.neighborSet x` is a vertex cover of `G`. Combining weak duality with this
normalized cover yields the general Kőnig–Ore inequality

`|M| + |S| ≤ |L| + |⋃ x ∈ S, G.neighborSet x|`

in `ℕ∞` with no finiteness assumptions, and in `ℕ` whenever `L` and the neighbourhood union of `S`
are finite.

When `V` is finite, transferring ordinary multigraph Kőnig and Kőnig–Ore duality across
`Graph.ofSimpleGraph G` and `SimpleGraph.matchingSubgraph` (after enlarging `R` to `Lᶜ` so that
any isolated vertices outside `L ∪ R` are covered without altering neighbourhoods of subsets of
`L`) proves equality:

* **Kőnig's theorem**: some matching `M` and some vertex cover `C` satisfy
  `M.edgeSet.ncard = C.ncard`, and some matching attains `M.edgeSet.encard = G.vertexCoverNum`;
* **the Kőnig–Ore formula**: for `G.IsBipartiteWith L R`, some matching `M` and some `S ⊆ L`
  satisfy `M.edgeSet.ncard + S.ncard = L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard`, so the
  greatest matching size is `L.ncard - ⨆ S ⊆ L, (S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard)`.

At zero deficiency, Kőnig–Ore recovers the finite case of Hall's marriage theorem via
`M.edgeSet.ncard = L.ncard ↔ L ⊆ M.verts`; combining our general necessity bound with Mathlib's
locally finite sufficiency theorems `SimpleGraph.exists_isMatching_of_forall_ncard_le` and
`SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le` upgrades both to equivalences under
`[G.LocallyFinite]`.

## Main declarations

* `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_le_encard_of_isVertexCover` and
  `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_le_vertexCoverNum`: matching–cover weak duality
  for arbitrary simple graphs.
* `SimpleGraph.Subgraph.IsMatching.interVertsEquivEdgeSet`: the canonical equivalence
  `↥(L ∩ M.verts) ≃ M.edgeSet` for a matching `M` in a bipartite graph `G.IsBipartiteWith L R`.
* `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_add_encard_le` and
  `SimpleGraph.Subgraph.IsMatching.ncard_edgeSet_add_ncard_le`: the Kőnig–Ore inequality.
* `SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_ncard_eq`,
  `SimpleGraph.IsBipartite.exists_isMatching_encard_edgeSet_eq_vertexCoverNum`, and
  `SimpleGraph.IsBipartite.iSup_encard_edgeSet_isMatching_eq_vertexCoverNum`: **Kőnig's theorem**
  for finite bipartite simple graphs.
* `SimpleGraph.IsBipartiteWith.exists_isMatching_ncard_edgeSet_add_ncard_eq` and
  `SimpleGraph.IsBipartiteWith.isGreatest_ncard_edgeSet_isMatching`: **the Kőnig–Ore deficiency
  formula** in witness and numerical forms, together with right-side versions.
* `SimpleGraph.IsBipartiteWith.exists_isMatching_iff`,
  `SimpleGraph.IsBipartite.exists_isPerfectMatching_iff`, and
  `SimpleGraph.IsBipartiteWith.exists_isMatching_ncard_edgeSet_eq_ncard_iff`: two-way **Hall
  characterizations** and compatibility between the extremal and locally finite formulations.

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
    rw [← Subtype.val_injective.encard_image, Subtype.image_preimage_coe]
    simp
  rwa [M.encard_toGraphEdgeSet, hpre] at hle

/-- In any simple graph, the number of edges in a matching is at most the cardinality of any
finite vertex cover. -/
theorem ncard_edgeSet_le_ncard_of_isVertexCover {M : G.Subgraph} (hM : M.IsMatching)
    {C : Set V} (hC : G.IsVertexCover C) (hCf : C.Finite := by toFinite_tac) :
    M.edgeSet.ncard ≤ C.ncard := by
  rw [Set.ncard_def, Set.ncard_def]
  exact ENat.toNat_le_toNat (hM.encard_edgeSet_le_encard_of_isVertexCover hC) hCf.encard_lt_top.ne

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

/-! ### Bipartite covers, matched-vertex bijections, and the Kőnig–Ore inequality -/

/-- The left class of a bipartition of `G` is a vertex cover of `G`. -/
theorem IsBipartiteWith.isVertexCover_left {L R : Set V} (h : G.IsBipartiteWith L R) :
    G.IsVertexCover L :=
  fun _ _ hadj ↦ (h.mem_of_adj hadj).imp And.left And.right

/-- The right class of a bipartition of `G` is a vertex cover of `G`. -/
theorem IsBipartiteWith.isVertexCover_right {L R : Set V} (h : G.IsBipartiteWith L R) :
    G.IsVertexCover R :=
  h.symm.isVertexCover_left

/-- **Normalized Kőnig–Ore vertex cover.** If `G.IsBipartiteWith L R`, then for any `S : Set V`
the set `(L \ S) ∪ ⋃ x ∈ S, G.neighborSet x` is a vertex cover of `G`. -/
theorem IsBipartiteWith.isVertexCover_sdiff_union_biUnion_neighborSet {L R S : Set V}
    (h : G.IsBipartiteWith L R) :
    G.IsVertexCover ((L \ S) ∪ ⋃ x ∈ S, G.neighborSet x) := by
  intro u w hadj
  rcases h.mem_of_adj hadj with ⟨huL, -⟩ | ⟨-, hwL⟩
  · by_cases huS : u ∈ S
    · exact .inr <| .inr <| Set.mem_biUnion huS hadj
    · exact .inl <| .inl ⟨huL, huS⟩
  · by_cases hwS : w ∈ S
    · exact .inl <| .inr <| Set.mem_biUnion hwS hadj.symm
    · exact .inr <| .inl ⟨hwL, hwS⟩

namespace Subgraph.IsMatching

/-- In a bipartite graph `G.IsBipartiteWith L R`, sending each matched vertex of `L` to its unique
incident matching edge gives a bijection `↥(L ∩ M.verts) ≃ M.edgeSet`. -/
noncomputable def interVertsEquivEdgeSet {M : G.Subgraph} (hM : M.IsMatching) {L R : Set V}
    (h : G.IsBipartiteWith L R) :
    ↥(L ∩ M.verts) ≃ M.edgeSet :=
  Equiv.ofBijective (fun v ↦ hM.toEdge ⟨v.1, v.2.2⟩) ⟨by
    rintro ⟨u, huL, huM⟩ ⟨v, hvL, hvM⟩ huv
    dsimp only at huv
    apply Subtype.ext
    obtain ⟨w, huw, -⟩ := hM huM
    have hv_mem : v ∈ (s(u, w) : Sym2 V) := by
      have := hM.mem_coe_toEdge hvM
      rwa [← huv, hM.toEdge_eq_of_adj huw] at this
    rcases Sym2.mem_iff.mp hv_mem with rfl | rfl
    · rfl
    · exact (h.disjoint.ne_of_mem hvL (h.mem_of_mem_adj huL (M.adj_sub huw)) rfl).elim, by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u w =>
      rw [Subgraph.mem_edgeSet] at he
      rcases h.mem_of_adj (M.adj_sub he) with ⟨huL, -⟩ | ⟨-, hwL⟩
      · exact ⟨⟨u, huL, he.fst_mem⟩, hM.toEdge_eq_of_adj he⟩
      · refine ⟨⟨w, hwL, he.snd_mem⟩, ?_⟩
        exact (hM.toEdge_eq_of_adj he.symm).trans (Subtype.ext Sym2.eq_swap)⟩

@[simp]
theorem interVertsEquivEdgeSet_apply {M : G.Subgraph} (hM : M.IsMatching) {L R : Set V}
    (h : G.IsBipartiteWith L R) (v : ↥(L ∩ M.verts)) :
    hM.interVertsEquivEdgeSet h v = hM.toEdge ⟨v.1, v.2.2⟩ :=
  (rfl)

/-- In a bipartite graph `G.IsBipartiteWith L R`, the extended edge cardinality of a matching
equals the extended cardinality of the vertices of `L` that it saturates. -/
theorem encard_edgeSet_eq_encard_inter_verts {M : G.Subgraph} (hM : M.IsMatching)
    {L R : Set V} (h : G.IsBipartiteWith L R) :
    M.edgeSet.encard = (L ∩ M.verts).encard :=
  (Set.encard_congr (hM.interVertsEquivEdgeSet h)).symm

/-- In a bipartite graph `G.IsBipartiteWith L R`, the edge cardinality of a matching equals the
cardinality of the vertices of `L` that it saturates. -/
theorem ncard_edgeSet_eq_ncard_inter_verts {M : G.Subgraph} (hM : M.IsMatching)
    {L R : Set V} (h : G.IsBipartiteWith L R) :
    M.edgeSet.ncard = (L ∩ M.verts).ncard :=
  (Set.ncard_congr' (hM.interVertsEquivEdgeSet h)).symm

/-- When `L` is finite, a matching in `G.IsBipartiteWith L R` has `L.ncard` edges if and only if
it saturates every vertex of `L`. -/
theorem ncard_edgeSet_eq_ncard_iff_subset_verts {M : G.Subgraph} (hM : M.IsMatching)
    {L R : Set V} (h : G.IsBipartiteWith L R) (hLf : L.Finite := by toFinite_tac) :
    M.edgeSet.ncard = L.ncard ↔ L ⊆ M.verts := by
  rw [hM.ncard_edgeSet_eq_ncard_inter_verts h, ← Set.inter_eq_left]
  exact ⟨fun heq ↦ Set.eq_of_subset_of_ncard_le Set.inter_subset_left heq.ge hLf,
    fun heq ↦ congrArg Set.ncard heq⟩

/-- **The Kőnig–Ore inequality** in extended cardinalities. For any bipartite simple graph
`G.IsBipartiteWith L R`, any matching `M`, and any `S ⊆ L`,
`M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard`, without finiteness
assumptions. -/
theorem encard_edgeSet_add_encard_le {M : G.Subgraph} (hM : M.IsMatching) {L R S : Set V}
    (h : G.IsBipartiteWith L R) (hS : S ⊆ L) :
    M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
  have hcov : M.edgeSet.encard ≤ ((L \ S) ∪ ⋃ x ∈ S, G.neighborSet x).encard :=
    hM.encard_edgeSet_le_encard_of_isVertexCover (h.isVertexCover_sdiff_union_biUnion_neighborSet)
  calc
    M.edgeSet.encard + S.encard ≤
        ((L \ S).encard + (⋃ x ∈ S, G.neighborSet x).encard) + S.encard :=
      add_le_add_left (hcov.trans (Set.encard_union_le _ _)) S.encard
    _ = ((L \ S).encard + S.encard) + (⋃ x ∈ S, G.neighborSet x).encard := by ac_rfl
    _ = L.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
      rw [Set.encard_sdiff_add_encard_of_subset hS]

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
    M.edgeSet.ncard + S.ncard ≤ L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard := by
  have hMf : M.edgeSet.Finite := by
    rw [← Set.encard_lt_top_iff]
    exact (hM.encard_edgeSet_le_encard_of_isVertexCover h.isVertexCover_left).trans_lt
      hLf.encard_lt_top
  have hSf : S.Finite := hLf.subset hS
  have hle := hM.encard_edgeSet_add_encard_le h hS
  rw [← hMf.cast_ncard_eq, ← hSf.cast_ncard_eq, ← hLf.cast_ncard_eq, ← hNf.cast_ncard_eq] at hle
  exact_mod_cast hle

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
  rw [G.ncard_edgeSet_matchingSubgraph M₀, Set.ncard_image_of_injective C₀ Subtype.val_injective,
    hMC₀]

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
  have hScard : S.ncard = S₀.card := by
    rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
  have hLcard : L.ncard = L'.card := by
    rw [← hL', Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
  have hNcard :
      (⋃ x ∈ S, G.neighborSet x).ncard = ((Graph.ofSimpleGraph G).neighborsIn S₀ R').card := by
    rw [← hN, Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
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

end FiniteBipartite

/-! ### Hall's marriage characterizations and compatibility -/

/-- In any simple graph (without bipartiteness or finiteness assumptions), every vertex set `S`
saturated by a matching `M` has extended cardinality at most that of its neighbourhood union. -/
theorem Subgraph.IsMatching.encard_le_encard_biUnion_neighborSet {M : G.Subgraph}
    (hM : M.IsMatching) {S : Set V} (hSM : S ⊆ M.verts) :
    S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard := by
  choose partner hpartner _ using fun x : S ↦ hM (hSM x.2)
  refine Function.Embedding.encard_le
    ⟨fun x ↦ ⟨partner x, Set.mem_biUnion x.2 (M.adj_sub (hpartner x))⟩, fun x y hxy ↦ ?_⟩
  apply Subtype.ext
  have hp : partner x = partner y := congrArg Subtype.val hxy
  exact hM.eq_of_adj_right (hpartner x) (hp ▸ hpartner y)

/-- In a locally finite simple graph, every vertex set `S` saturated by a matching `M` satisfies
`S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem Subgraph.IsMatching.ncard_le_ncard_biUnion_neighborSet [G.LocallyFinite] {M : G.Subgraph}
    (hM : M.IsMatching) {S : Set V} (hSM : S ⊆ M.verts) :
    S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  obtain hSf | hSi := S.finite_or_infinite
  · have hNf : (⋃ x ∈ S, G.neighborSet x).Finite :=
      hSf.biUnion fun x _ ↦ (G.neighborSet x).toFinite
    rw [Set.ncard_def, Set.ncard_def]
    exact ENat.toNat_le_toNat (hM.encard_le_encard_biUnion_neighborSet hSM) hNf.encard_lt_top.ne
  · simp [hSi.ncard]

/-- **Hall's marriage theorem (equivalence form)** for a locally finite bipartite simple graph:
a matching saturating `L` exists if and only if every `S ⊆ L` satisfies
`S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem IsBipartiteWith.exists_isMatching_iff [G.LocallyFinite] {L R : Set V}
    (h : G.IsBipartiteWith L R) :
    (∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ S ⊆ L, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard :=
  ⟨fun ⟨_, hLM, hM⟩ _ hSL ↦ hM.ncard_le_ncard_biUnion_neighborSet (hSL.trans hLM),
    exists_isMatching_of_forall_ncard_le h⟩

/-- **Hall's marriage theorem (equivalence form)** saturating the right side `R` of a locally
finite bipartite simple graph. -/
theorem IsBipartiteWith.exists_isMatching_right_iff [G.LocallyFinite] {L R : Set V}
    (h : G.IsBipartiteWith L R) :
    (∃ M : G.Subgraph, R ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ T ⊆ R, T.ncard ≤ (⋃ y ∈ T, G.neighborSet y).ncard :=
  h.symm.exists_isMatching_iff

/-- **Hall's condition for a perfect matching (equivalence form)** in a locally finite bipartite
simple graph: a perfect matching exists if and only if every vertex set `S` satisfies
`S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem IsBipartite.exists_isPerfectMatching_iff [G.LocallyFinite] (h : G.IsBipartite) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ∀ S : Set V, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  obtain ⟨_, _, hLR⟩ := h.exists_isBipartiteWith
  exact ⟨fun ⟨_, hM, hspan⟩ S ↦ hM.ncard_le_ncard_biUnion_neighborSet
      (hspan.verts_eq_univ ▸ Set.subset_univ S),
    exists_isPerfectMatching_of_forall_ncard_le hLR⟩

/-- **Compatibility of the Kőnig–Ore formula with Hall's theorem** on finite bipartite simple
graphs: a matching of size `L.ncard` (equivalently, by
`SimpleGraph.Subgraph.IsMatching.ncard_edgeSet_eq_ncard_iff_subset_verts`, a matching saturating
`L`) exists if and only if `S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard` for every `S ⊆ L`. -/
theorem IsBipartiteWith.exists_isMatching_ncard_edgeSet_eq_ncard_iff [Finite V] {L R : Set V}
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

/-- **Hall's marriage theorem** for a finite bipartite simple graph, under propositional finiteness
`[Finite V]` alone (without requiring `[G.LocallyFinite]` data): a matching saturating `L` exists
if and only if `S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard` for every `S ⊆ L`. -/
theorem IsBipartiteWith.exists_isMatching_iff_of_finite [Finite V] {L R : Set V}
    (h : G.IsBipartiteWith L R) :
    (∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ S ⊆ L, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  rw [← h.exists_isMatching_ncard_edgeSet_eq_ncard_iff]
  refine exists_congr fun M ↦ ⟨fun ⟨hLM, hM⟩ ↦
      ⟨hM, (hM.ncard_edgeSet_eq_ncard_iff_subset_verts h).2 hLM⟩,
    fun ⟨hM, hML⟩ ↦ ⟨(hM.ncard_edgeSet_eq_ncard_iff_subset_verts h).1 hML, hM⟩⟩

/-- On a finite simple graph with a covering bipartition (`L ∪ R = Set.univ`), a perfect matching
exists if and only if `L.ncard = R.ncard` and Hall's condition holds for subsets of `L`. -/
theorem IsBipartiteWith.exists_isPerfectMatching_iff_ncard_eq_and_forall_ncard_le [Finite V]
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

end SimpleGraph
