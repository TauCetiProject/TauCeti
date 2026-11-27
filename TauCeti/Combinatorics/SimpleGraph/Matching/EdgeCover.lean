/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Matching.Basic

/-!
# Edge covers and Gallai's matching identity

An edge cover is a set of edges meeting every vertex. The edge cover number is the infimum of
the sizes of such sets in `ℕ∞`. It is infinite if the graph has an isolated vertex or if the
vertex type is infinite.

A maximal matching extends to an edge cover by adding one edge at each unmatched vertex. This
construction also applies to the graph formed by the edges of any given edge cover. These two
uses yield Gallai's identity, which equates the sum of the matching and edge cover numbers
with the number of vertices in a graph without isolated vertices.

## References

* A. Schrijver, [*A Course in Combinatorial Optimization*][schrijver2017], §3.1, Theorem 3.1.

[schrijver2017]: https://homepages.cwi.nl/~lex/files/dict.pdf#page=39
-/

public section

open Set

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {F F' : Set (Sym2 V)}

/-- An edge cover of `G` is a subset of its edges containing an edge incident to every vertex. -/
def IsEdgeCover (G : SimpleGraph V) (F : Set (Sym2 V)) : Prop :=
  F ⊆ G.edgeSet ∧ ∀ v, ∃ w, s(v, w) ∈ F

/-- A set covers `G` if it consists of edges of `G` and every vertex has an incident edge in it. -/
theorem isEdgeCover_iff :
    G.IsEdgeCover F ↔ F ⊆ G.edgeSet ∧ ∀ v, ∃ w, s(v, w) ∈ F :=
  (Iff.rfl)

/-- Every member of an edge cover of `G` is an edge of `G`. -/
theorem IsEdgeCover.subset_edgeSet (hF : G.IsEdgeCover F) : F ⊆ G.edgeSet :=
  (isEdgeCover_iff.mp hF).1

/-- An edge cover contains an incident edge at every vertex. -/
theorem IsEdgeCover.exists_mem (hF : G.IsEdgeCover F) (v : V) : ∃ w, s(v, w) ∈ F :=
  (isEdgeCover_iff.mp hF).2 v

/-- Adding edges of `G` to an edge cover preserves the edge cover property. -/
theorem IsEdgeCover.mono (hF : G.IsEdgeCover F) (hFF' : F ⊆ F') (hF' : F' ⊆ G.edgeSet) :
    G.IsEdgeCover F' :=
  isEdgeCover_iff.mpr ⟨hF', fun v ↦ (hF.exists_mem v).imp fun _ h ↦ hFF' h⟩

/-- The entire edge set is an edge cover precisely when each vertex has a neighbour. -/
@[simp]
theorem isEdgeCover_edgeSet_iff : G.IsEdgeCover G.edgeSet ↔ ∀ v, ∃ w, G.Adj v w := by
  simp [isEdgeCover_iff]

/-- The edge cover number is the infimum of the extended cardinalities of the edge covers.
If there are no edge covers, the infimum is `⊤`. -/
noncomputable def edgeCoverNum (G : SimpleGraph V) : ℕ∞ :=
  ⨅ (F : Set (Sym2 V)) (_ : G.IsEdgeCover F), F.encard

/-- The edge cover number is the infimum over edge covers of the graph. -/
theorem edgeCoverNum_def (G : SimpleGraph V) :
    G.edgeCoverNum = ⨅ (F : Set (Sym2 V)) (_ : G.IsEdgeCover F), F.encard :=
  (rfl)

/-- A lower bound for the edge cover number is a lower bound for every edge cover size. -/
theorem le_edgeCoverNum_iff {n : ℕ∞} :
    n ≤ G.edgeCoverNum ↔ ∀ F, G.IsEdgeCover F → n ≤ F.encard := by
  simp [edgeCoverNum_def]

/-- The edge cover number is at most the size of any edge cover. -/
theorem IsEdgeCover.edgeCoverNum_le (hF : G.IsEdgeCover F) : G.edgeCoverNum ≤ F.encard :=
  le_edgeCoverNum_iff.mp le_rfl F hF

/-- If every vertex has a neighbour, there is an edge cover attaining the edge cover number. -/
theorem edgeCoverNum_exists (hG : ∀ v, ∃ w, G.Adj v w) :
    ∃ F, G.IsEdgeCover F ∧ F.encard = G.edgeCoverNum := by
  have : Nonempty {F // G.IsEdgeCover F} := ⟨⟨G.edgeSet, isEdgeCover_edgeSet_iff.mpr hG⟩⟩
  obtain ⟨⟨F, hF⟩, hcard⟩ := ENat.exists_eq_iInf fun F : {F // G.IsEdgeCover F} ↦ F.val.encard
  exact ⟨F, hF, by simpa only [edgeCoverNum_def, iInf_subtype] using hcard⟩

/-- A graph with an isolated vertex has infinite edge cover number. -/
theorem edgeCoverNum_eq_top_of_isIsolated {v : V} (hv : G.IsIsolated v) : G.edgeCoverNum = ⊤ := by
  refine top_unique (le_edgeCoverNum_iff.mpr fun F hF ↦ ?_)
  obtain ⟨w, hw⟩ := hF.exists_mem v
  exact (hv w ((mem_edgeSet G).mp (hF.subset_edgeSet hw))).elim

/-- On an empty vertex type the empty set is an edge cover, so the edge cover number is zero. -/
@[simp]
theorem edgeCoverNum_of_isEmpty [IsEmpty V] : G.edgeCoverNum = 0 := by
  have h : G.IsEdgeCover ∅ := isEdgeCover_iff.mpr ⟨empty_subset _, isEmptyElim⟩
  simpa using h.edgeCoverNum_le

/-- The graph formed by the edges of an edge cover has no isolated vertices. -/
theorem IsEdgeCover.exists_adj_fromEdgeSet (hF : G.IsEdgeCover F) (v : V) :
    ∃ w, (fromEdgeSet F).Adj v w := by
  obtain ⟨w, hw⟩ := hF.exists_mem v
  exact ⟨w, (fromEdgeSet_adj F).mpr ⟨hw, ((mem_edgeSet G).mp (hF.subset_edgeSet hw)).ne⟩⟩

/-- Every edge cover of a graph with infinitely many vertices is infinite. -/
theorem IsEdgeCover.infinite [Infinite V] (hF : G.IsEdgeCover F) : F.Infinite := by
  intro hfin
  have hs : (fromEdgeSet F).support = univ :=
    eq_univ_of_forall fun v ↦ (mem_support _).mpr (hF.exists_adj_fromEdgeSet v)
  have he : (fromEdgeSet F).edgeSet.Finite := by
    rw [edgeSet_fromEdgeSet]
    exact hfin.subset sdiff_subset
  exact infinite_univ (hs ▸ finite_edgeSet_iff_finite_support.mp he)

/-- On an infinite vertex type, the edge cover number is infinite. -/
@[simp]
theorem edgeCoverNum_eq_top_of_infinite [Infinite V] : G.edgeCoverNum = ⊤ :=
  top_unique (le_edgeCoverNum_iff.mpr fun _ hF ↦ hF.infinite.encard_eq.ge)

/-- In a graph without isolated vertices, every maximal matching is contained in an edge cover
such that the extended cardinalities of the matching's edge set and the cover sum to the extended
cardinality of the vertex type. -/
theorem Subgraph.exists_isEdgeCover_superset_of_maximal_isMatching {M : G.Subgraph}
    (hM : Maximal IsMatching M) (hG : ∀ v, ∃ w, G.Adj v w) :
    ∃ F, G.IsEdgeCover F ∧ M.edgeSet ⊆ F ∧
      M.edgeSet.encard + F.encard = ENat.card V := by
  classical
  obtain ⟨hm, hcover⟩ := maximal_isMatching_iff.mp hM
  choose nbr hnbr using hG
  let e (v : V) : Sym2 V := s(v, nbr v)
  have hneigh {v : V} (hv : v ∈ M.vertsᶜ) : nbr v ∈ M.verts :=
    (hcover (hnbr v)).resolve_left hv
  -- Each chosen edge has a unique unmatched endpoint.
  have hinj : InjOn e M.vertsᶜ := by
    intro u hu v hv huv
    rcases Sym2.eq_iff.mp huv with h | h
    · exact h.1
    · exact (hu (h.1 ▸ hneigh hv)).elim
  have hdisj : Disjoint M.edgeSet (e '' M.vertsᶜ) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ he ⟨v, hv, rfl⟩
    exact hv (Subgraph.mem_edgeSet.mp he).fst_mem
  refine ⟨M.edgeSet ∪ e '' M.vertsᶜ, isEdgeCover_iff.mpr ⟨?_, ?_⟩, subset_union_left, ?_⟩
  · refine union_subset M.edgeSet_subset (image_subset_iff.mpr ?_)
    exact fun v _ ↦ (mem_edgeSet G).mpr (hnbr v)
  · intro v
    by_cases hv : v ∈ M.verts
    · obtain ⟨w, hw, -⟩ := hm hv
      exact ⟨w, mem_union_left _ (Subgraph.mem_edgeSet.mpr hw)⟩
    · exact ⟨nbr v, mem_union_right _ (mem_image_of_mem e hv)⟩
  rw [encard_union_eq hdisj, hinj.encard_image, ← add_assoc, ← two_mul, ← hm.encard_verts,
    encard_add_encard_compl]

/-- The size of any edge cover plus the matching number is at least the number of vertices. -/
theorem IsEdgeCover.card_le_matchingNum_add_encard (hF : G.IsEdgeCover F) :
    ENat.card V ≤ G.matchingNum + F.encard := by
  by_cases htop : F.encard = ⊤
  · simp [htop]
  -- Extend a maximal matching within the graph whose edges come from the given cover.
  let H := fromEdgeSet F
  have hH : H.edgeSet ⊆ F := edgeSet_fromEdgeSet F ▸ sdiff_subset
  have hHG : H ≤ G := edgeSet_subset_edgeSet.mp (hH.trans hF.subset_edgeSet)
  have hfin := (encard_ne_top_iff.mp htop).subset hH
  obtain ⟨M, hM⟩ := H.exists_maximal_isMatching (matchingNum_ne_top_of_finite_edgeSet hfin)
  obtain ⟨F', hF', -, hcard⟩ :=
    M.exists_isEdgeCover_superset_of_maximal_isMatching hM hF.exists_adj_fromEdgeSet
  exact hcard.ge.trans <| add_le_add
    (hM.1.encard_edgeSet_le_matchingNum.trans (matchingNum_mono hHG))
    (encard_le_encard (hF'.subset_edgeSet.trans hH))

/-- The matching number plus the edge cover number is at least the number of vertices. -/
theorem card_le_matchingNum_add_edgeCoverNum :
    ENat.card V ≤ G.matchingNum + G.edgeCoverNum := by
  rw [edgeCoverNum_def, ENat.add_iInf₂]
  exact le_iInf₂ fun _ hF ↦ hF.card_le_matchingNum_add_encard

/-- **Gallai's matching and edge cover identity.** In a graph with no isolated vertices, the
matching number plus the edge cover number equals the extended cardinality of the vertex type. -/
theorem matchingNum_add_edgeCoverNum (hG : ∀ v, ∃ w, G.Adj v w) :
    G.matchingNum + G.edgeCoverNum = ENat.card V := by
  refine le_antisymm ?_ card_le_matchingNum_add_edgeCoverNum
  by_cases htop : G.matchingNum = ⊤
  · simp [top_unique (htop ▸ matchingNum_le_card (G := G))]
  obtain ⟨M, hM⟩ := G.exists_isMaximumMatching htop
  have hfin := hM.isMatching.finite_edgeSet_of_matchingNum_ne_top htop
  obtain ⟨F, hF, -, hcard⟩ :=
    M.exists_isEdgeCover_superset_of_maximal_isMatching (hM.maximal hfin) hG
  rw [← hcard, hM.encard_edgeSet_eq]
  exact add_le_add_right hF.edgeCoverNum_le _

end SimpleGraph
