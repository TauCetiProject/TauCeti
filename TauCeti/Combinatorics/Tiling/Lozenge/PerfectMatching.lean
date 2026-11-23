/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.HexGraph
public import TauCeti.Combinatorics.Tiling.Lozenge.Tiling
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Lozenge tilings are perfect matchings

A lozenge is the union of the two faces containing an edge, that is an edge of the dual hexagonal
graph `hexGraph`. A tiling `M` of a region `R` therefore gives the spanning subgraph
`tilingSubgraph R M` of `SimpleGraph.induce R hexGraph` whose edges are the pairs of faces of `R`
sharing an edge of `M`, and the tilings of `R` are exactly the perfect matchings of
`SimpleGraph.induce R hexGraph`, for every region `R`, finite or infinite.

## Main definitions

* `TauCeti.tilingSubgraph`: the subgraph of `SimpleGraph.induce R hexGraph` of the lozenges of a
  set `M` of edges.

## Main statements

* `TauCeti.tilingSubgraph_adj`: two faces of `R` are adjacent in `tilingSubgraph R M` exactly when
  they are distinct and some edge of `M` lies in both.
* `TauCeti.tilingSubgraph_inter_interiorEdges`: only the interior edges of `M` count.
* `TauCeti.tilingSubgraph_bijOn`: **tilings are perfect matchings**: `tilingSubgraph R` is a
  bijection from the tilings of `R` onto the perfect matchings of `SimpleGraph.induce R hexGraph`.

## References

* A. Aggarwal, *Universality for lozenge tiling local statistics*, Ann. of Math. 198 (2023),
  Section 1.2.
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lecture 2.
* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009), Section 1.1.
-/

public section

namespace TauCeti

/-- The spanning subgraph of `SimpleGraph.induce R hexGraph` whose edges are the pairs of faces of
`R` sharing an edge of `M`. -/
def tilingSubgraph (R : Set TriFace) (M : Set TriEdge) :
    (SimpleGraph.induce R hexGraph).Subgraph :=
  SimpleGraph.toSubgraph
    (SimpleGraph.fromRel fun f g : R => ∃ e ∈ M, e ∈ f.val.edges ∧ e ∈ g.val.edges) (by
      intro f g h
      rw [SimpleGraph.fromRel_adj] at h
      obtain ⟨hne, h⟩ := h
      rw [SimpleGraph.induce_adj, hexGraph_adj]
      refine ⟨fun hfg => hne (Subtype.ext hfg), ?_⟩
      rcases h with ⟨e, -, h₁, h₂⟩ | ⟨e, -, h₁, h₂⟩
      exacts [⟨e, h₁, h₂⟩, ⟨e, h₂, h₁⟩])

variable {R : Set TriFace} {M M' : Set TriEdge} {f g : R}

/-- Two faces of `R` are adjacent in `tilingSubgraph R M` exactly when they are distinct and some
edge of `M` lies in both. -/
theorem tilingSubgraph_adj :
    (tilingSubgraph R M).Adj f g ↔ f ≠ g ∧ ∃ e ∈ M, e ∈ f.val.edges ∧ e ∈ g.val.edges := by
  rw [tilingSubgraph, SimpleGraph.toSubgraph_adj, SimpleGraph.fromRel_adj]
  refine and_congr_right fun _ => ⟨?_, Or.inl⟩
  rintro (h | ⟨e, he, h₁, h₂⟩)
  exacts [h, ⟨e, he, h₂, h₁⟩]

/-- Every face of `R` is a vertex of `tilingSubgraph R M`. -/
@[simp] theorem tilingSubgraph_verts : (tilingSubgraph R M).verts = Set.univ := (rfl)

theorem tilingSubgraph_isSpanning : (tilingSubgraph R M).IsSpanning :=
  SimpleGraph.Subgraph.isSpanning_iff.2 tilingSubgraph_verts

/-- `tilingSubgraph R M` grows with `M`. -/
theorem tilingSubgraph_mono (h : M ⊆ M') : tilingSubgraph R M ≤ tilingSubgraph R M' := by
  refine ⟨subset_rfl, fun f g hfg => ?_⟩
  obtain ⟨hne, e, he, h₁, h₂⟩ := tilingSubgraph_adj.1 hfg
  exact tilingSubgraph_adj.2 ⟨hne, e, h he, h₁, h₂⟩

/-- Only the interior edges of `M` count: an edge lying in two distinct faces of `R` is an
interior edge of `R`. -/
theorem tilingSubgraph_inter_interiorEdges :
    tilingSubgraph R (M ∩ interiorEdges R) = tilingSubgraph R M := by
  refine le_antisymm (tilingSubgraph_mono Set.inter_subset_left) ⟨subset_rfl, fun f g hfg => ?_⟩
  obtain ⟨hne, e, he, h₁, h₂⟩ := tilingSubgraph_adj.1 hfg
  refine tilingSubgraph_adj.2 ⟨hne, e, ⟨he, mem_interiorEdges.2 fun k hk => ?_⟩, h₁, h₂⟩
  rcases TriFace.eq_or_eq_of_mem_edges (fun h => hne (Subtype.ext h)) h₁ h₂ hk with rfl | rfl
  exacts [f.property, g.property]

/-- The subgraph of `M` lies in that of `M'` exactly when every interior edge of `R` in `M` lies
in `M'`. -/
theorem tilingSubgraph_le_iff :
    tilingSubgraph R M ≤ tilingSubgraph R M' ↔ M ∩ interiorEdges R ⊆ M' := by
  refine ⟨fun h e ⟨he, hi⟩ => ?_, fun h =>
    tilingSubgraph_inter_interiorEdges.ge.trans (tilingSubgraph_mono h)⟩
  rw [mem_interiorEdges_iff] at hi
  have hadj : (tilingSubgraph R M).Adj ⟨_, hi.1⟩ ⟨_, hi.2⟩ :=
    tilingSubgraph_adj.2 ⟨fun h => e.whiteFace_ne_blackFace (congrArg Subtype.val h), e, he,
      e.mem_whiteFace_edges, e.mem_blackFace_edges⟩
  obtain ⟨-, e', he', h₁, h₂⟩ := tilingSubgraph_adj.1 (h.2 hadj)
  rwa [TriFace.eq_of_mem_edges_of_mem_edges e.whiteFace_ne_blackFace e.mem_whiteFace_edges
    e.mem_blackFace_edges h₁ h₂]

/-- If `M` is a tiling of `R`, every set `M'` whose subgraph contains that of `M` contains `M`. -/
theorem IsTiling.subset_of_tilingSubgraph_le (hM : IsTiling R M)
    (h : tilingSubgraph R M ≤ tilingSubgraph R M') : M ⊆ M' := by
  simpa [Set.inter_eq_left.2 hM.subset_interiorEdges] using tilingSubgraph_le_iff.1 h

/-- The subgraph of a tiling is a perfect matching. -/
theorem IsTiling.isPerfectMatching_tilingSubgraph (hM : IsTiling R M) :
    (tilingSubgraph R M).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  rintro ⟨f, hf⟩
  obtain ⟨e, ⟨he, hfe⟩, huniq⟩ := hM.existsUnique hf
  obtain ⟨g, hgf, hge⟩ := TriFace.exists_ne_mem_edges hfe
  refine ⟨⟨g, hM.mem_of_mem_edges he hge⟩,
    tilingSubgraph_adj.2 ⟨fun h => hgf (congrArg Subtype.val h).symm, e, he, hfe, hge⟩,
    fun g' hg' => Subtype.ext ?_⟩
  obtain ⟨hne, e', he', h₁, h₂⟩ := tilingSubgraph_adj.1 hg'
  obtain rfl := huniq e' ⟨he', h₁⟩
  exact (TriFace.eq_or_eq_of_mem_edges hgf.symm hfe hge h₂).resolve_left
    fun h => hne (Subtype.ext h.symm)

/-- The set of edges of a perfect matching `P` of `SimpleGraph.induce R hexGraph`: the edges lying
in both faces of an edge of `P`. -/
private def matchingEdges (P : (SimpleGraph.induce R hexGraph).Subgraph) : Set TriEdge :=
  {e | ∃ f g : R, P.Adj f g ∧ e ∈ f.val.edges ∧ e ∈ g.val.edges}

private theorem faces_eq_of_adj {P : (SimpleGraph.induce R hexGraph).Subgraph} {e : TriEdge}
    {f g f' g' : R} (hfg : f ≠ g) (hf : e ∈ f.val.edges) (hg : e ∈ g.val.edges)
    (hfg' : f' ≠ g') (hf' : e ∈ f'.val.edges) (hg' : e ∈ g'.val.edges) (hP : P.Adj f' g') :
    P.Adj f g := by
  have hne : f'.val ≠ g'.val := fun h => hfg' (Subtype.ext h)
  rcases TriFace.eq_or_eq_of_mem_edges hne hf' hg' hf with h₁ | h₁ <;>
    rcases TriFace.eq_or_eq_of_mem_edges hne hf' hg' hg with h₂ | h₂
  · exact absurd (Subtype.ext (h₁.trans h₂.symm)) hfg
  · rwa [Subtype.ext h₁, Subtype.ext h₂]
  · rw [Subtype.ext h₁, Subtype.ext h₂]
    exact hP.symm
  · exact absurd (Subtype.ext (h₁.trans h₂.symm)) hfg

private theorem isTiling_matchingEdges {P : (SimpleGraph.induce R hexGraph).Subgraph}
    (hP : P.IsPerfectMatching) : IsTiling R (matchingEdges P) := by
  refine isTiling_def.2 ⟨fun e ⟨f, g, hfg, hf, hg⟩ k hk => ?_, fun f hf => ?_⟩
  · rcases TriFace.eq_or_eq_of_mem_edges (fun h => hfg.ne (Subtype.ext h)) hf hg hk with rfl | rfl
    exacts [f.property, g.property]
  · obtain ⟨g, hfg, huniq⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.1 hP ⟨f, hf⟩
    obtain ⟨e, ⟨hfe, hge⟩, -⟩ := existsUnique_mem_edges_of_hexGraph_adj (P.adj_sub hfg)
    refine ⟨e, ⟨⟨_, g, hfg, hfe, hge⟩, hfe⟩, fun e' ⟨⟨f', g', hfg', hf', hg'⟩, he'⟩ => ?_⟩
    have hadj : P.Adj ⟨f, hf⟩ (if f = f'.val then g' else f') := by
      split_ifs with h
      · rwa [show (⟨f, hf⟩ : R) = f' from Subtype.ext h]
      · rcases TriFace.eq_or_eq_of_mem_edges (fun h => hfg'.ne (Subtype.ext h)) hf' hg' he'
          with h' | h'
        · exact absurd h' h
        · rw [show (⟨f, hf⟩ : R) = g' from Subtype.ext h']
          exact hfg'.symm
    have hg'' := huniq _ hadj
    have hmem : e' ∈ g.val.edges := by
      rw [← hg'']
      split_ifs
      exacts [hg', hf']
    exact TriFace.eq_of_mem_edges_of_mem_edges (fun h => hfg.ne (Subtype.ext h)) he' hmem hfe hge

private theorem tilingSubgraph_matchingEdges {P : (SimpleGraph.induce R hexGraph).Subgraph}
    (hP : P.IsPerfectMatching) : tilingSubgraph R (matchingEdges P) = P := by
  refine SimpleGraph.Subgraph.ext ?_ ?_
  · rw [tilingSubgraph_verts, hP.2.verts_eq_univ]
  · ext f g
    rw [tilingSubgraph_adj]
    constructor
    · rintro ⟨hfg, e, ⟨f', g', hP', hf', hg'⟩, hf, hg⟩
      exact faces_eq_of_adj hfg hf hg hP'.ne hf' hg' hP'
    · intro h
      obtain ⟨e, ⟨hf, hg⟩, -⟩ := existsUnique_mem_edges_of_hexGraph_adj (P.adj_sub h)
      exact ⟨h.ne, e, ⟨f, g, h, hf, hg⟩, hf, hg⟩

/-- **Tilings are perfect matchings.** For every region `R`, finite or infinite,
`M ↦ tilingSubgraph R M` is a bijection from the tilings of `R` onto the perfect matchings of
`SimpleGraph.induce R hexGraph`. For `R = Set.univ` this identifies the plane tilings with the
perfect matchings of `hexGraph`. -/
theorem tilingSubgraph_bijOn (R : Set TriFace) :
    Set.BijOn (tilingSubgraph R) {M | IsTiling R M} {P | P.IsPerfectMatching} := by
  refine ⟨fun M hM => IsTiling.isPerfectMatching_tilingSubgraph hM,
    fun M hM M' hM' h => (hM.subset_of_tilingSubgraph_le h.le).antisymm
      (hM'.subset_of_tilingSubgraph_le h.ge), fun P hP => ?_⟩
  exact ⟨matchingEdges P, isTiling_matchingEdges hP, tilingSubgraph_matchingEdges hP⟩

end TauCeti
