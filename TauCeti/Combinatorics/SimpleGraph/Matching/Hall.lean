/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hall

import TauCeti.Data.Set.Card

/-!
# Matched-vertex bijections and Hall marriage equivalences for simple graphs

This file supplies the elementary bijection between matched vertices on one side of a bipartite
simple graph and matching edges, together with the necessity direction and two-way equivalence
forms of **Hall's marriage theorem** for `SimpleGraph`, complementing the sufficiency theorems
`SimpleGraph.exists_isMatching_of_forall_ncard_le` and
`SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le` in
`Mathlib.Combinatorics.SimpleGraph.Hall`.

In any bipartite graph `G.IsBipartiteWith L R`, every edge of a matching `M` meets `L` in a unique
vertex, giving a canonical equivalence `↥(L ∩ M.verts) ≃ M.edgeSet`
(`SimpleGraph.Subgraph.IsMatching.interVertsEquivEdgeSet`). In particular, when `L` is finite, a
matching has `L.ncard` edges if and only if it saturates `L`.

In any simple graph (without bipartiteness or finiteness assumptions), every vertex set `S`
saturated by a matching `M` satisfies `S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard`, and hence
`S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard` whenever every vertex of `S` has a finite
neighbourhood. Combining this necessity bound with Mathlib's sufficiency theorems gives two-way
Hall characterizations whenever every vertex of `G` has a finite neighbourhood (discharged
automatically under either `[G.LocallyFinite]` or `[Finite V]`).

## Main declarations

* `SimpleGraph.Subgraph.IsMatching.interVertsEquivEdgeSet`: the canonical equivalence
  `↥(L ∩ M.verts) ≃ M.edgeSet` for a matching `M` in a bipartite graph `G.IsBipartiteWith L R`,
  with characteristic lemmas for both directions and induced `encard`/`ncard` identities.
* `SimpleGraph.Subgraph.IsMatching.encard_le_encard_biUnion_neighborSet` and
  `SimpleGraph.Subgraph.IsMatching.ncard_le_ncard_biUnion_neighborSet`: necessity of Hall's
  neighbourhood condition on arbitrary simple graphs.
* `SimpleGraph.IsBipartiteWith.exists_isMatching_iff`,
  `SimpleGraph.IsBipartiteWith.exists_isMatching_right_iff`, and
  `SimpleGraph.IsBipartite.exists_isPerfectMatching_iff`: two-way **Hall marriage
  characterizations** for bipartite simple graphs whose vertices have finite neighbourhoods.

## References

* P. Hall, *On representatives of subsets*, J. London Math. Soc. 10 (1935).
* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Section 2.1.
-/

public section

open Function Set

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Matched-vertex bijections in bipartite simple graphs -/

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

/-- `interVertsEquivEdgeSet` maps each matched vertex of `L` to its incident matching edge. -/
@[simp]
theorem interVertsEquivEdgeSet_apply {M : G.Subgraph} (hM : M.IsMatching) {L R : Set V}
    (h : G.IsBipartiteWith L R) (v : ↥(L ∩ M.verts)) :
    hM.interVertsEquivEdgeSet h v = hM.toEdge ⟨v.1, v.2.2⟩ :=
  (rfl)

/-- In a bipartite graph `G.IsBipartiteWith L R`, the inverse of `interVertsEquivEdgeSet` sends an
edge `s(u, w)` of `M` with `u ∈ L` to `u`. -/
theorem interVertsEquivEdgeSet_symm_eq_of_adj {M : G.Subgraph} (hM : M.IsMatching)
    {L R : Set V} (h : G.IsBipartiteWith L R) {u w : V} (huL : u ∈ L) (huw : M.Adj u w) :
    (hM.interVertsEquivEdgeSet h).symm ⟨s(u, w), Subgraph.mem_edgeSet.2 huw⟩ =
      ⟨u, huL, huw.fst_mem⟩ :=
  (hM.interVertsEquivEdgeSet h).symm_apply_eq.2 (hM.toEdge_eq_of_adj huw).symm

/-- Every matching edge contains the `L`-endpoint selected by `(interVertsEquivEdgeSet h).symm`. -/
@[simp]
theorem mem_coe_interVertsEquivEdgeSet_symm {M : G.Subgraph} (hM : M.IsMatching)
    {L R : Set V} (h : G.IsBipartiteWith L R) (e : M.edgeSet) :
    ((hM.interVertsEquivEdgeSet h).symm e : V) ∈ (e : Sym2 V) := by
  obtain ⟨v, rfl⟩ := (hM.interVertsEquivEdgeSet h).surjective e
  rw [Equiv.symm_apply_apply, interVertsEquivEdgeSet_apply]
  exact hM.mem_coe_toEdge v.2.2

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

/-! ### Hall's marriage characterizations -/

/-- In any simple graph (without bipartiteness or finiteness assumptions), every vertex set `S`
saturated by a matching `M` has extended cardinality at most that of its neighbourhood union. -/
theorem encard_le_encard_biUnion_neighborSet {M : G.Subgraph}
    (hM : M.IsMatching) {S : Set V} (hSM : S ⊆ M.verts) :
    S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard := by
  choose partner hpartner _ using fun x : S ↦ hM (hSM x.2)
  refine Function.Embedding.encard_le
    ⟨fun x ↦ ⟨partner x, Set.mem_biUnion x.2 (M.adj_sub (hpartner x))⟩, fun x y hxy ↦ ?_⟩
  apply Subtype.ext
  have hp : partner x = partner y := congrArg Subtype.val hxy
  exact hM.eq_of_adj_right (hpartner x) (hp ▸ hpartner y)

/-- Every vertex set `S` saturated by a matching `M` whose vertices have finite neighbourhoods
satisfies `S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem ncard_le_ncard_biUnion_neighborSet {M : G.Subgraph}
    (hM : M.IsMatching) {S : Set V} (hSM : S ⊆ M.verts)
    (hN : ∀ x ∈ S, (G.neighborSet x).Finite := by intro _ _; toFinite_tac) :
    S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  obtain hSf | hSi := S.finite_or_infinite
  · exact Set.ncard_le_ncard_of_encard_le
      (hM.encard_le_encard_biUnion_neighborSet hSM) (hSf.biUnion hN)
  · simp [hSi.ncard]

end Subgraph.IsMatching

/-- **Hall's marriage theorem (equivalence form)** for a bipartite simple graph whose vertices have
finite neighbourhoods (discharged automatically under `[G.LocallyFinite]` or `[Finite V]`): a
matching saturating `L` exists if and only if every `S ⊆ L` satisfies
`S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem IsBipartiteWith.exists_isMatching_iff {L R : Set V}
    (h : G.IsBipartiteWith L R)
    (hN : ∀ x, (G.neighborSet x).Finite := by intro _; toFinite_tac) :
    (∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ S ⊆ L, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  let _ : G.LocallyFinite := fun v ↦ (hN v).fintype
  exact ⟨fun ⟨_, hLM, hM⟩ _ hSL ↦
      hM.ncard_le_ncard_biUnion_neighborSet (hSL.trans hLM) fun x _ ↦ hN x,
    exists_isMatching_of_forall_ncard_le h⟩

/-- **Hall's marriage theorem (equivalence form)** saturating the right side `R` of a bipartite
simple graph whose vertices have finite neighbourhoods. -/
theorem IsBipartiteWith.exists_isMatching_right_iff {L R : Set V}
    (h : G.IsBipartiteWith L R)
    (hN : ∀ x, (G.neighborSet x).Finite := by intro _; toFinite_tac) :
    (∃ M : G.Subgraph, R ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ T ⊆ R, T.ncard ≤ (⋃ y ∈ T, G.neighborSet y).ncard :=
  h.symm.exists_isMatching_iff hN

/-- **Hall's condition for a perfect matching (equivalence form)** in a bipartite simple graph
whose vertices have finite neighbourhoods: a perfect matching exists if and only if every vertex
set `S` satisfies `S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem IsBipartite.exists_isPerfectMatching_iff (h : G.IsBipartite)
    (hN : ∀ x, (G.neighborSet x).Finite := by intro _; toFinite_tac) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ∀ S : Set V, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  let _ : G.LocallyFinite := fun v ↦ (hN v).fintype
  obtain ⟨_, _, hLR⟩ := h.exists_isBipartiteWith
  exact ⟨fun ⟨_, hM, hspan⟩ S ↦
      hM.ncard_le_ncard_biUnion_neighborSet (hspan.verts_eq_univ ▸ Set.subset_univ S)
        fun x _ ↦ hN x,
    exists_isPerfectMatching_of_forall_ncard_le hLR⟩

end SimpleGraph
