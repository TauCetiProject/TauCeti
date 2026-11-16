/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.Combinatorics.SimpleGraph.Matching.Basic
public import TauCeti.Combinatorics.SimpleGraph.VertexCover

import TauCeti.Combinatorics.Graph.Matching.Capacitated
import TauCeti.Combinatorics.Graph.Matching.OfSimpleGraph
import TauCeti.Combinatorics.Graph.VertexCover.SimpleGraph

/-!
# Kőnig's theorem for simple graphs

In any simple graph, every edge of a matching contains at least one vertex of any vertex cover, and
no vertex belongs to two distinct matching edges. Consequently `M.edgeSet.encard ≤ c.encard` for
every matching `M` and every vertex cover `c`, and hence `G.matchingNum ≤ G.vertexCoverNum`,
without any bipartiteness or finiteness assumptions. Whenever equality holds for a matching `M` and
a vertex cover `c`, `M` is automatically a maximum matching and `c` is a minimum vertex cover.

For finite bipartite simple graphs, **Kőnig's theorem** states that this bound is attained: there
exist a matching `M` and a vertex cover `c` of the same size, `G.matchingNum = G.vertexCoverNum`,
and every maximum matching has the same number of edges as every minimum vertex cover has vertices.
In particular, optimality of a matching (respectively, of a vertex cover) is certified by the
existence of a vertex cover (respectively, of a matching) of the same size.

The attainment proof transports the unit-capacity case of the multigraph capacitated Kőnig theorem
(`TauCeti.Combinatorics.Graph.Matching.Capacitated`) across the simple-graph matching, vertex-cover,
and bipartition correspondences.

## Main results

* `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_le_of_isVertexCover` and
  `SimpleGraph.matchingNum_le_vertexCoverNum`: weak duality between matchings and vertex covers in
  arbitrary simple graphs.
* `SimpleGraph.Subgraph.IsMatching.isMaximumMatching_of_encard_edgeSet_eq` and
  `SimpleGraph.IsVertexCover.isMinimumVertexCover_of_encard_eq`: optimality certificates from equal
  matching and cover sizes.
* `SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_encard_eq` and
  `SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_ncard_eq`: Kőnig's theorem in witness
  form for finite bipartite simple graphs.
* `SimpleGraph.IsBipartite.matchingNum_eq_vertexCoverNum`: equality of the matching number and the
  vertex cover number for finite bipartite simple graphs.
* `SimpleGraph.IsBipartite.encard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover` and
  `SimpleGraph.IsBipartite.ncard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover`: equality
  of sizes of maximum matchings and minimum vertex covers.
* `SimpleGraph.IsBipartite.isMaximumMatching_iff_exists_isVertexCover_encard_eq` and
  `SimpleGraph.IsBipartite.isMinimumVertexCover_iff_exists_isMatching_encard_eq`: duality
  characterizations of maximum matchings and minimum vertex covers in finite bipartite simple
  graphs.

## References

* D. Kőnig, *Gráfok és mátrixok*, Mat. Fiz. Lapok 38 (1931), 116--119.
* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Theorem 2.1.1.
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Theorem 16.2.
-/

public section

open scoped Graph

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {M : G.Subgraph} {c : Set V}

/-! ### Weak duality and optimality certificates -/

/-- **Weak duality.** Every matching of a simple graph has at most as many edges as any vertex
cover has vertices. No bipartiteness or finiteness assumption is required. -/
theorem Subgraph.IsMatching.encard_edgeSet_le_of_isVertexCover (hM : M.IsMatching)
    (hc : G.IsVertexCover c) : M.edgeSet.encard ≤ c.encard := by
  have hex : ∀ e : M.edgeSet, ∃ v ∈ c, v ∈ (e : Sym2 V) := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u w =>
      rcases hc (M.adj_sub he) with hu | hw
      · exact ⟨u, hu, Sym2.mem_mk_left u w⟩
      · exact ⟨w, hw, Sym2.mem_mk_right u w⟩
  let f : M.edgeSet → c := fun e ↦ ⟨(hex e).choose, (hex e).choose_spec.1⟩
  have hf : Function.Injective f := by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ h
    have hv : (hex ⟨e₁, he₁⟩).choose = (hex ⟨e₂, he₂⟩).choose := congrArg Subtype.val h
    have hmem₁ : (hex ⟨e₁, he₁⟩).choose ∈ e₁ := (hex ⟨e₁, he₁⟩).choose_spec.2
    have hmem₂ : (hex ⟨e₁, he₁⟩).choose ∈ e₂ := hv ▸ (hex ⟨e₂, he₂⟩).choose_spec.2
    obtain ⟨w₁, hw₁⟩ := Sym2.mem_iff_exists.mp hmem₁
    obtain ⟨w₂, hw₂⟩ := Sym2.mem_iff_exists.mp hmem₂
    have hadj₁ : M.Adj (hex ⟨e₁, he₁⟩).choose w₁ := M.mem_edgeSet.mp (hw₁ ▸ he₁)
    have hadj₂ : M.Adj (hex ⟨e₁, he₁⟩).choose w₂ := M.mem_edgeSet.mp (hw₂ ▸ he₂)
    exact Subtype.ext (hw₁.trans ((hM.eq_of_adj_left hadj₁ hadj₂) ▸ hw₂.symm))
  exact Function.Embedding.encard_le ⟨f, hf⟩

/-- Every matching of a simple graph has `ncard` at most that of any finite vertex cover. -/
theorem Subgraph.IsMatching.ncard_edgeSet_le_of_isVertexCover (hM : M.IsMatching)
    (hc : G.IsVertexCover c) (hfin : c.Finite) : M.edgeSet.ncard ≤ c.ncard :=
  ENat.toNat_le_toNat (hM.encard_edgeSet_le_of_isVertexCover hc) (Set.encard_ne_top_iff.mpr hfin)

/-- Every matching of a simple graph has at most `G.vertexCoverNum` edges. -/
theorem Subgraph.IsMatching.encard_edgeSet_le_vertexCoverNum (hM : M.IsMatching) :
    M.edgeSet.encard ≤ G.vertexCoverNum := by
  obtain ⟨c, hc_eq, hc⟩ := G.vertexCoverNum_exists
  exact (hM.encard_edgeSet_le_of_isVertexCover hc).trans_eq hc_eq

/-- **Weak duality.** The matching number of a simple graph is at most its vertex cover number. -/
theorem matchingNum_le_vertexCoverNum (G : SimpleGraph V) : G.matchingNum ≤ G.vertexCoverNum :=
  matchingNum_le_iff.mpr fun _ hM ↦ hM.encard_edgeSet_le_vertexCoverNum

/-- The matching number of a simple graph is at most the cardinality of any vertex cover. -/
theorem IsVertexCover.matchingNum_le_encard (hc : G.IsVertexCover c) : G.matchingNum ≤ c.encard :=
  G.matchingNum_le_vertexCoverNum.trans hc.vertexCoverNum_le

/-- A simple graph with finite vertex cover number has finite matching number. -/
theorem matchingNum_ne_top_of_vertexCoverNum_ne_top (h : G.vertexCoverNum ≠ ⊤) :
    G.matchingNum ≠ ⊤ :=
  ne_top_of_le_ne_top h G.matchingNum_le_vertexCoverNum

/-- A matching whose edge-set cardinality equals that of some vertex cover is a maximum matching. -/
theorem Subgraph.IsMatching.isMaximumMatching_of_encard_edgeSet_eq (hM : M.IsMatching)
    (hc : G.IsVertexCover c) (h : M.edgeSet.encard = c.encard) : M.IsMaximumMatching :=
  Subgraph.isMaximumMatching_def.mpr
    ⟨hM, fun _ hM' ↦ (hM'.encard_edgeSet_le_of_isVertexCover hc).trans_eq h.symm⟩

/-- A vertex cover whose cardinality equals the edge-set cardinality of some matching is a minimum
vertex cover. -/
theorem IsVertexCover.isMinimumVertexCover_of_encard_eq (hc : G.IsVertexCover c) (hM : M.IsMatching)
    (h : M.edgeSet.encard = c.encard) : G.IsMinimumVertexCover c :=
  isMinimumVertexCover_def.mpr
    ⟨hc, fun _ hc' ↦ h.symm.trans_le (hM.encard_edgeSet_le_of_isVertexCover hc')⟩

/-- If some matching and some vertex cover have equal cardinalities, then the matching number equals
the vertex cover number. -/
theorem matchingNum_eq_vertexCoverNum_of_encard_eq (hM : M.IsMatching) (hc : G.IsVertexCover c)
    (h : M.edgeSet.encard = c.encard) : G.matchingNum = G.vertexCoverNum :=
  le_antisymm G.matchingNum_le_vertexCoverNum
    (hc.vertexCoverNum_le.trans (h.symm.trans_le hM.encard_edgeSet_le_matchingNum))

/-- For a finite vertex cover `c`, equality of `ncard` with a matching `M` upgrades to equality of
`encard`, since weak duality forces `M.edgeSet` to be finite. -/
theorem Subgraph.IsMatching.encard_edgeSet_eq_of_ncard_eq (hM : M.IsMatching)
    (hc : G.IsVertexCover c) (hfin : c.Finite) (h : M.edgeSet.ncard = c.ncard) :
    M.edgeSet.encard = c.encard := by
  have hMf : M.edgeSet.Finite := Set.encard_ne_top_iff.mp <|
    ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hfin) (hM.encard_edgeSet_le_of_isVertexCover hc)
  rw [← hMf.cast_ncard_eq, ← hfin.cast_ncard_eq, h]

/-- A matching whose edge-set `ncard` equals the `ncard` of a finite vertex cover is a maximum
matching. -/
theorem Subgraph.IsMatching.isMaximumMatching_of_ncard_edgeSet_eq (hM : M.IsMatching)
    (hc : G.IsVertexCover c) (hfin : c.Finite) (h : M.edgeSet.ncard = c.ncard) :
    M.IsMaximumMatching :=
  hM.isMaximumMatching_of_encard_edgeSet_eq hc (hM.encard_edgeSet_eq_of_ncard_eq hc hfin h)

/-- A finite vertex cover whose `ncard` equals the edge-set `ncard` of a matching is a minimum
vertex cover. -/
theorem IsVertexCover.isMinimumVertexCover_of_ncard_eq (hc : G.IsVertexCover c) (hM : M.IsMatching)
    (hfin : c.Finite) (h : M.edgeSet.ncard = c.ncard) : G.IsMinimumVertexCover c :=
  hc.isMinimumVertexCover_of_encard_eq hM (hM.encard_edgeSet_eq_of_ncard_eq hc hfin h)

/-! ### Kőnig's theorem for finite bipartite simple graphs -/

namespace IsBipartite

/-- **Kőnig's theorem** (witness form in `ℕ∞`). A finite bipartite simple graph has a matching and
a vertex cover of the same cardinality. -/
theorem exists_isMatching_isVertexCover_encard_eq [Finite V] (h : G.IsBipartite) :
    ∃ (M : G.Subgraph) (c : Set V), M.IsMatching ∧ G.IsVertexCover c ∧
      M.edgeSet.encard = c.encard := by
  classical
  obtain ⟨L, R, hLR⟩ := h.exists_isBipartition_ofSimpleGraph
  let _ : Fintype E(Graph.ofSimpleGraph G) := Fintype.ofFinite _
  obtain ⟨x, C, hx, hC, hxC⟩ :=
    hLR.exists_isCapacitatedMatching_isVertexCover_sum_eq (fun _ ↦ 1)
  let M : Finset E(Graph.ofSimpleGraph G) := Finset.univ.filter fun e ↦ x e ≠ 0
  have hM : (Graph.ofSimpleGraph G).IsMatching (M : Set E(Graph.ofSimpleGraph G)) :=
    hx.supportFinset_isMatching hLR.loopless
  have hcard : M.card = C.card := by
    rw [← hx.sum_eq_card_support, hxC]
    simp
  refine ⟨G.matchingSubgraph (M : Set E(Graph.ofSimpleGraph G)),
    Subtype.val '' (C : Set V(Graph.ofSimpleGraph G)),
    (matchingSubgraph_isMatching_iff (H := G) _).2 hM,
    (isVertexCover_ofSimpleGraph_image_iff (H := G)).2 hC, ?_⟩
  rw [edgeSet_matchingSubgraph, Subtype.val_injective.encard_image,
    Subtype.val_injective.encard_image, Set.encard_coe_eq_coe_finsetCard,
    Set.encard_coe_eq_coe_finsetCard, hcard]

/-- **Kőnig's theorem** (witness form in `ℕ`). A finite bipartite simple graph has a matching and a
vertex cover of the same `ncard`. -/
theorem exists_isMatching_isVertexCover_ncard_eq [Finite V] (h : G.IsBipartite) :
    ∃ (M : G.Subgraph) (c : Set V), M.IsMatching ∧ G.IsVertexCover c ∧
      M.edgeSet.ncard = c.ncard := by
  obtain ⟨M, c, hM, hc, hcard⟩ := h.exists_isMatching_isVertexCover_encard_eq
  exact ⟨M, c, hM, hc, congrArg ENat.toNat hcard⟩

/-- **Kőnig's theorem.** In a finite bipartite simple graph, the matching number equals the vertex
cover number. -/
theorem matchingNum_eq_vertexCoverNum [Finite V] (h : G.IsBipartite) :
    G.matchingNum = G.vertexCoverNum := by
  obtain ⟨_, _, hM, hc, hcard⟩ := h.exists_isMatching_isVertexCover_encard_eq
  exact matchingNum_eq_vertexCoverNum_of_encard_eq hM hc hcard

/-- **Kőnig's theorem** (extremal witness form in `ℕ∞`). A finite bipartite simple graph admits a
maximum matching and a minimum vertex cover of the same cardinality. -/
theorem exists_isMaximumMatching_isMinimumVertexCover_encard_eq [Finite V] (h : G.IsBipartite) :
    ∃ (M : G.Subgraph) (c : Set V), M.IsMaximumMatching ∧ G.IsMinimumVertexCover c ∧
      M.edgeSet.encard = c.encard := by
  obtain ⟨M, c, hM, hc, hcard⟩ := h.exists_isMatching_isVertexCover_encard_eq
  exact ⟨M, c, hM.isMaximumMatching_of_encard_edgeSet_eq hc hcard,
    hc.isMinimumVertexCover_of_encard_eq hM hcard, hcard⟩

/-- **Kőnig's theorem** (extremal witness form in `ℕ`). A finite bipartite simple graph admits a
maximum matching and a minimum vertex cover of the same `ncard`. -/
theorem exists_isMaximumMatching_isMinimumVertexCover_ncard_eq [Finite V] (h : G.IsBipartite) :
    ∃ (M : G.Subgraph) (c : Set V), M.IsMaximumMatching ∧ G.IsMinimumVertexCover c ∧
      M.edgeSet.ncard = c.ncard := by
  obtain ⟨M, c, hM, hc, hcard⟩ := h.exists_isMaximumMatching_isMinimumVertexCover_encard_eq
  exact ⟨M, c, hM, hc, congrArg ENat.toNat hcard⟩

/-- In a finite bipartite simple graph, every maximum matching has the same edge-set cardinality as
every minimum vertex cover has vertices. -/
theorem encard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover [Finite V]
    (h : G.IsBipartite) (hM : M.IsMaximumMatching) (hc : G.IsMinimumVertexCover c) :
    M.edgeSet.encard = c.encard := by
  rw [hM.encard_edgeSet_eq, hc.encard_eq, h.matchingNum_eq_vertexCoverNum]

/-- In a finite bipartite simple graph, every maximum matching has the same edge-set `ncard` as
every minimum vertex cover has vertices. -/
theorem ncard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover [Finite V]
    (h : G.IsBipartite) (hM : M.IsMaximumMatching) (hc : G.IsMinimumVertexCover c) :
    M.edgeSet.ncard = c.ncard :=
  congrArg ENat.toNat (h.encard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover hM hc)

/-- In a finite bipartite simple graph, a matching is maximum if and only if some vertex cover has
the same cardinality. -/
theorem isMaximumMatching_iff_exists_isVertexCover_encard_eq [Finite V] (h : G.IsBipartite) :
    M.IsMaximumMatching ↔
      M.IsMatching ∧ ∃ c : Set V, G.IsVertexCover c ∧ M.edgeSet.encard = c.encard := by
  refine ⟨fun hM ↦ ⟨hM.isMatching, ?_⟩, fun ⟨hM, _, hc, hcard⟩ ↦
    hM.isMaximumMatching_of_encard_edgeSet_eq hc hcard⟩
  obtain ⟨c, hc⟩ := G.exists_isMinimumVertexCover
  exact ⟨c, hc.isVertexCover,
    h.encard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover hM hc⟩

/-- In a finite bipartite simple graph, a vertex cover is minimum if and only if some matching has
the same cardinality. -/
theorem isMinimumVertexCover_iff_exists_isMatching_encard_eq [Finite V] (h : G.IsBipartite) :
    G.IsMinimumVertexCover c ↔
      G.IsVertexCover c ∧ ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = c.encard := by
  refine ⟨fun hc ↦ ⟨hc.isVertexCover, ?_⟩, fun ⟨hc, _, hM, hcard⟩ ↦
    hc.isMinimumVertexCover_of_encard_eq hM hcard⟩
  obtain ⟨M, hM⟩ := G.exists_isMaximumMatching
  exact ⟨M, hM.isMatching, h.encard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover hM hc⟩

/-- In a finite bipartite simple graph, a matching is maximum if and only if some vertex cover has
the same `ncard`. -/
theorem isMaximumMatching_iff_exists_isVertexCover_ncard_eq [Finite V] (h : G.IsBipartite) :
    M.IsMaximumMatching ↔
      M.IsMatching ∧ ∃ c : Set V, G.IsVertexCover c ∧ M.edgeSet.ncard = c.ncard := by
  refine ⟨fun hM ↦ ⟨hM.isMatching, ?_⟩, fun ⟨hM, c, hc, hcard⟩ ↦
    hM.isMaximumMatching_of_ncard_edgeSet_eq hc c.toFinite hcard⟩
  obtain ⟨c, hc⟩ := G.exists_isMinimumVertexCover
  exact ⟨c, hc.isVertexCover,
    h.ncard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover hM hc⟩

/-- In a finite bipartite simple graph, a vertex cover is minimum if and only if some matching has
the same `ncard`. -/
theorem isMinimumVertexCover_iff_exists_isMatching_ncard_eq [Finite V] (h : G.IsBipartite) :
    G.IsMinimumVertexCover c ↔
      G.IsVertexCover c ∧ ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = c.ncard := by
  refine ⟨fun hc ↦ ⟨hc.isVertexCover, ?_⟩, fun ⟨hc, _, hM, hcard⟩ ↦
    hc.isMinimumVertexCover_of_ncard_eq hM c.toFinite hcard⟩
  obtain ⟨M, hM⟩ := G.exists_isMaximumMatching
  exact ⟨M, hM.isMatching, h.ncard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover hM hc⟩

end IsBipartite

end SimpleGraph
