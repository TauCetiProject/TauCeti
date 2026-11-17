/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.Combinatorics.SimpleGraph.Matching.Basic

import TauCeti.Combinatorics.Graph.Matching.OfSimpleGraph
import TauCeti.Combinatorics.Graph.Matching.VertexCover
import TauCeti.Combinatorics.SimpleGraph.VertexCover

/-!
# Kőnig's theorem and the Kőnig–Ore deficiency formula for simple graphs

In any bipartite simple graph `G : SimpleGraph V`, the matching number equals the vertex cover
number:

`G.matchingNum = G.vertexCoverNum`,

and there exist a matching `M : G.Subgraph` and a vertex cover `C : Set V` with
`M.edgeSet.encard = C.encard`. No finiteness assumption on `V` or `G` is required for the
`ℕ∞`-valued theorem:

* on a finite vertex type, enlarging a bipartition `(L, R)` of `G` to `(L, Lᶜ)` partitions all
  vertices of `Graph.ofSimpleGraph G`, and the multigraph Kőnig theorem transports to `G` across
  `SimpleGraph.matchingSubgraph`;
* when `G.vertexCoverNum < ⊤` on an arbitrary vertex type, finite-cover neighbourhood kernelization
  (`SimpleGraph.IsVertexCover.exists_finite_verts_isVertexCover_image`) produces an induced
  subgraph on finitely many vertices whose minimum cover pushes forward to `G`;
* when `G.vertexCoverNum = ⊤`, `G.matchingNum = ⊤` as well by
  `SimpleGraph.matchingNum_eq_top_iff_vertexCoverNum_eq_top`, so the witnesses attaining
  `G.matchingNum` and `G.vertexCoverNum` both have cardinality `⊤`.

When `G` is equipped with a displayed bipartition `G.IsBipartiteWith L R` (which allows isolated
vertices outside `L ∪ R`), normalizing a minimum vertex cover `C` to `S = L \ C` yields the
finiteness-free **Kőnig–Ore deficiency formula**: there exist a matching `M` and `S ⊆ L` with
`M.edgeSet.encard = (L \ S).encard + (⋃ x ∈ S, G.neighborSet x).encard`, matching the universal
bound `(L \ S) ∪ N(S)` gives for every matching and every `S : Set V` (and yielding the additive
`Set.ncard` identity `M.edgeSet.ncard + S.ncard = L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard` when
`L` is finite). For finite `L`, this yields

`G.matchingNum = L.encard - ⨆ (S : Set V) (_ : S ⊆ L),
  (S.encard - (⋃ x ∈ S, G.neighborSet x).encard)`.

As an immediate consequence, a matching saturating `L` exists if and only if Hall's neighbourhood
condition holds on subsets of `L`, recovering the finite specialization of
`SimpleGraph.exists_isMatching_of_forall_ncard_le`.

## Main results

* `SimpleGraph.IsBipartite.matchingNum_eq_vertexCoverNum`: **Kőnig's theorem** in extremality form,
  `G.matchingNum = G.vertexCoverNum`, with no finiteness assumptions.
* `SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_encard_eq` and
  `SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_ncard_eq`: **Kőnig's theorem** in
  witness form.
* `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_le_encard_sdiff_add_encard`,
  `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_add_encard_le`, and
  `SimpleGraph.Subgraph.IsMatching.ncard_edgeSet_add_ncard_le`: the universal Kőnig–Ore
  inequalities.
* `SimpleGraph.IsBipartiteWith.exists_isMatching_encard_edgeSet_eq_encard_sdiff_add_encard`,
  `SimpleGraph.IsBipartiteWith.exists_isMatching_ncard_edgeSet_add_ncard_eq`, and
  `SimpleGraph.IsBipartiteWith.matchingNum_eq_encard_sub_iSup`: the **Kőnig–Ore deficiency
  formula** in witness and numerical forms.
* `SimpleGraph.IsBipartiteWith.exists_isMatching_subset_verts_iff_forall_encard_le` and
  `SimpleGraph.IsBipartiteWith.exists_isMatching_subset_verts_iff`: finite Hall characterizations
  recovered from Kőnig–Ore deficiency.

## References

* D. Kőnig, *Gráfok és mátrixok*, Mat. Fiz. Lapok 38 (1931), 116–119.
* Ø. Ore, *Graphs and matching theorems*, Duke Math. J. 22 (1955), 625–639.
-/

section

open scoped Graph

/-- Auxiliary finite-vertex case of Kőnig's theorem, deduced from the multigraph Kőnig theorem via
`Graph.ofSimpleGraph`. -/
private theorem SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_encard_eq_of_finite
    {V : Type*} {G : SimpleGraph V} [Finite V] (hG : G.IsBipartite) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧
      M.edgeSet.encard = C.encard := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨L, R, hLR'⟩ := hG.exists_isBipartiteWith
  -- Enlarge `R` to `Lᶜ` so the two sides partition all vertices of `Graph.ofSimpleGraph G`,
  -- including any isolated vertices.
  have hLLc : G.IsBipartiteWith L Lᶜ :=
    ⟨disjoint_compl_right, fun _ _ huv ↦
      (hLR'.mem_of_adj huv).imp
        (And.imp_right fun h ↦ hLR'.disjoint.subset_compl_left h)
        (And.imp_left fun h ↦ hLR'.disjoint.subset_compl_left h)⟩
  have himg (s : Set V) :
      Subtype.val '' (((Subtype.val ⁻¹' s : Set V(Graph.ofSimpleGraph G)).toFinset :
        Finset V(Graph.ofSimpleGraph G)) : Set V(Graph.ofSimpleGraph G)) = s := by
    ext x
    simp
  let L₀ : Finset V(Graph.ofSimpleGraph G) := (Subtype.val ⁻¹' L).toFinset
  let R₀ : Finset V(Graph.ofSimpleGraph G) := (Subtype.val ⁻¹' Lᶜ).toFinset
  have hLR : (Graph.ofSimpleGraph G).IsBipartition L₀ R₀ := by
    rw [G.isBipartition_ofSimpleGraph_iff, himg L, himg Lᶜ]
    exact ⟨hLLc, Set.union_compl_self L⟩
  obtain ⟨M₀, C₀, hM₀, hC₀, hcard⟩ := hLR.exists_isMatching_isVertexCover_card_eq
  refine ⟨G.matchingSubgraph (M₀ : Set E(Graph.ofSimpleGraph G)),
    Subtype.val '' (C₀ : Set V(Graph.ofSimpleGraph G)),
    (G.matchingSubgraph_isMatching_iff _).2 hM₀,
    G.isVertexCover_ofSimpleGraph_image_iff.2 hC₀, ?_⟩
  rw [edgeSet_matchingSubgraph, Subtype.val_injective.encard_image,
    Subtype.val_injective.encard_image, Set.encard_coe_eq_coe_finsetCard,
    Set.encard_coe_eq_coe_finsetCard, hcard]

end

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {L R : Set V}

/-! ### Kőnig's theorem -/

/-- **Kőnig's theorem** in `ℕ∞` witness form, with no finiteness assumptions: every bipartite
simple graph has a matching and a vertex cover of equal extended cardinality. -/
theorem IsBipartite.exists_isMatching_isVertexCover_encard_eq (hG : G.IsBipartite) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧
      M.edgeSet.encard = C.encard := by
  obtain ⟨C₀, hC₀num, hC₀⟩ := G.vertexCoverNum_exists
  by_cases htop : G.vertexCoverNum = ⊤
  · obtain ⟨M, hMnum, hM⟩ := G.matchingNum_exists
    refine ⟨M, C₀, hM, hC₀, ?_⟩
    rw [hMnum, matchingNum_eq_top_iff_vertexCoverNum_eq_top.2 htop, hC₀num, htop]
  · have hC₀fin : C₀.Finite := Set.encard_ne_top_iff.1 (hC₀num.trans_ne htop)
    obtain ⟨S, -, -, hSfin, hScov⟩ := hC₀.exists_finite_verts_isVertexCover_image hC₀fin
    let _ : Finite S.verts := hSfin.to_subtype
    obtain ⟨M₀, C₁, hM₀, hC₁, hMC₁⟩ :=
      (hG.subgraph S).exists_isMatching_isVertexCover_encard_eq_of_finite
    have hC₁le : C₁.encard ≤ C₀.encard := by
      calc
        C₁.encard = M₀.edgeSet.encard := hMC₁.symm
        _ ≤ (S.hom ⁻¹' C₀).encard :=
          hM₀.encard_edgeSet_le_of_isVertexCover (hC₀.preimage S.hom)
        _ = (Subtype.val ⁻¹' C₀ : Set S.verts).encard := by rw [S.coe_hom]
        _ ≤ C₀.encard := Set.encard_preimage_val_le_encard_right S.verts C₀
    refine ⟨Subgraph.coeSubgraph M₀, Subtype.val '' C₁, hM₀.coeSubgraph, hScov hC₁ hC₁le, ?_⟩
    rw [Subgraph.coeSubgraph, Subgraph.edgeSet_map,
      (Sym2.map.injective S.hom_injective).encard_image,
      Subtype.val_injective.encard_image, hMC₁]

/-- **Kőnig's theorem.** In any bipartite simple graph, the matching number equals the vertex cover
number. -/
theorem IsBipartite.matchingNum_eq_vertexCoverNum (hG : G.IsBipartite) :
    G.matchingNum = G.vertexCoverNum := by
  obtain ⟨M, C, hM, hC, hMC⟩ := hG.exists_isMatching_isVertexCover_encard_eq
  exact matchingNum_eq_vertexCoverNum_of_isMatching_of_isVertexCover hM hC hMC.symm.le

/-- **Kőnig's theorem** in `Set.ncard` form when `G.vertexCoverNum ≠ ⊤`: there exist a matching and
a finite vertex cover of equal cardinality. -/
theorem IsBipartite.exists_isMatching_isVertexCover_ncard_eq_of_vertexCoverNum_ne_top
    (hG : G.IsBipartite) (hfin : G.vertexCoverNum ≠ ⊤) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧ C.Finite ∧
      M.edgeSet.ncard = C.ncard := by
  obtain ⟨M, C, hM, hC, hMC⟩ := hG.exists_isMatching_isVertexCover_encard_eq
  have hCnum : C.encard = G.vertexCoverNum :=
    hC.encard_eq_vertexCoverNum_of_isMatching hM hMC.symm.le
  have hCf : C.Finite := Set.encard_ne_top_iff.1 (hCnum.trans_ne hfin)
  exact ⟨M, C, hM, hC, hCf, by simp [Set.ncard_def, hMC]⟩

/-- **Kőnig's theorem** in `Set.ncard` form for a bipartite simple graph with finitely many
edges: there exist a matching and a finite vertex cover of equal cardinality. -/
theorem IsBipartite.exists_isMatching_isVertexCover_ncard_eq_of_finite_edgeSet
    (hG : G.IsBipartite) (hE : G.edgeSet.Finite) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧ C.Finite ∧
      M.edgeSet.ncard = C.ncard :=
  hG.exists_isMatching_isVertexCover_ncard_eq_of_vertexCoverNum_ne_top
    (vertexCoverNum_ne_top_of_finite_edgeSet hE)

/-- **Kőnig's theorem** in `Set.ncard` witness form on a finite vertex type. -/
theorem IsBipartite.exists_isMatching_isVertexCover_ncard_eq [Finite V] (hG : G.IsBipartite) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧
      M.edgeSet.ncard = C.ncard := by
  obtain ⟨M, C, hM, hC, -, hMC⟩ :=
    hG.exists_isMatching_isVertexCover_ncard_eq_of_finite_edgeSet G.edgeSet.toFinite
  exact ⟨M, C, hM, hC, hMC⟩

/-! ### Matchings on a displayed bipartition -/

namespace IsBipartiteWith

/-- For a matching `M` in a graph with bipartition `(L, R)`, the set `M.verts ∩ L` of matched
vertices in `L` has the same extended cardinality as `M.edgeSet`. -/
theorem encard_verts_inter_left (hLR : G.IsBipartiteWith L R) {M : G.Subgraph}
    (hM : M.IsMatching) :
    (M.verts ∩ L).encard = M.edgeSet.encard := by
  have hbij : Function.Bijective (fun v : ↑(M.verts ∩ L) ↦ hM.toEdge ⟨v.1, v.2.1⟩) := by
    refine ⟨fun v₁ v₂ h ↦ Subtype.ext ?_, fun e ↦ ?_⟩
    · dsimp only at h
      have h1 : v₁.1 ∈ (hM.toEdge ⟨v₁.1, v₁.2.1⟩ : Sym2 V) := hM.mem_coe_toEdge v₁.2.1
      have h2 : v₂.1 ∈ (hM.toEdge ⟨v₁.1, v₁.2.1⟩ : Sym2 V) :=
        h ▸ hM.mem_coe_toEdge v₂.2.1
      set ed := hM.toEdge ⟨v₁.1, v₁.2.1⟩
      have hadj : M.Adj ed.1.out.1 ed.1.out.2 := by
        rw [← M.mem_edgeSet, Sym2.mk_fst_out_snd_out]
        exact ed.2
      rw [← Sym2.mk_fst_out_snd_out ed.1, Sym2.mem_iff] at h1 h2
      rcases hLR.mem_of_adj (M.adj_sub hadj) with ⟨_, houtR⟩ | ⟨houtR, _⟩
      · have hnotL : ed.1.out.2 ∉ L := Set.disjoint_right.1 hLR.disjoint houtR
        exact (h1.resolve_right fun h' ↦ hnotL (h' ▸ v₁.2.2)).trans
          (h2.resolve_right fun h' ↦ hnotL (h' ▸ v₂.2.2)).symm
      · have hnotL : ed.1.out.1 ∉ L := Set.disjoint_right.1 hLR.disjoint houtR
        exact (h1.resolve_left fun h' ↦ hnotL (h' ▸ v₁.2.2)).trans
          (h2.resolve_left fun h' ↦ hnotL (h' ▸ v₂.2.2)).symm
    · have hadj : M.Adj e.1.out.1 e.1.out.2 := by
        rw [← M.mem_edgeSet, Sym2.mk_fst_out_snd_out]
        exact e.2
      rcases hLR.mem_of_adj (M.adj_sub hadj) with ⟨h1L, -⟩ | ⟨-, h2L⟩
      · refine ⟨⟨e.1.out.1, hadj.fst_mem, h1L⟩, Subtype.ext ?_⟩
        exact (congrArg Subtype.val (hM.toEdge_eq_of_adj hadj)).trans
          (Sym2.mk_fst_out_snd_out e.1)
      · refine ⟨⟨e.1.out.2, hadj.snd_mem, h2L⟩, Subtype.ext ?_⟩
        exact (congrArg Subtype.val (hM.toEdge_eq_of_adj hadj.symm)).trans
          (Sym2.eq_swap.trans (Sym2.mk_fst_out_snd_out e.1))
  exact ENat.card_congr (Equiv.ofBijective _ hbij)

/-- For a matching `M` in a graph with bipartition `(L, R)`, the set `M.verts ∩ R` of matched
vertices in `R` has the same extended cardinality as `M.edgeSet`. -/
theorem encard_verts_inter_right (hLR : G.IsBipartiteWith L R) {M : G.Subgraph}
    (hM : M.IsMatching) :
    (M.verts ∩ R).encard = M.edgeSet.encard :=
  hLR.symm.encard_verts_inter_left hM

/-- `Set.ncard` form of `encard_verts_inter_left`. -/
theorem ncard_verts_inter_left (hLR : G.IsBipartiteWith L R) {M : G.Subgraph}
    (hM : M.IsMatching) :
    (M.verts ∩ L).ncard = M.edgeSet.ncard := by
  simp [Set.ncard_def, hLR.encard_verts_inter_left hM]

/-- `Set.ncard` form of `encard_verts_inter_right`. -/
theorem ncard_verts_inter_right (hLR : G.IsBipartiteWith L R) {M : G.Subgraph}
    (hM : M.IsMatching) :
    (M.verts ∩ R).ncard = M.edgeSet.ncard :=
  hLR.symm.ncard_verts_inter_left hM

/-- A matching has at most `L.encard` edges. -/
theorem encard_edgeSet_le_left (hLR : G.IsBipartiteWith L R) {M : G.Subgraph}
    (hM : M.IsMatching) :
    M.edgeSet.encard ≤ L.encard :=
  hM.encard_edgeSet_le_of_isVertexCover hLR.isVertexCover_left

/-- A matching has at most `R.encard` edges. -/
theorem encard_edgeSet_le_right (hLR : G.IsBipartiteWith L R) {M : G.Subgraph}
    (hM : M.IsMatching) :
    M.edgeSet.encard ≤ R.encard :=
  hLR.symm.encard_edgeSet_le_left hM

/-- When `L` is finite, every matching has finitely many edges. -/
theorem finite_edgeSet_of_finite_left (hLR : G.IsBipartiteWith L R) (hL : L.Finite)
    {M : G.Subgraph} (hM : M.IsMatching) :
    M.edgeSet.Finite :=
  hM.finite_edgeSet_of_isVertexCover hLR.isVertexCover_left hL

/-- When `R` is finite, every matching has finitely many edges. -/
theorem finite_edgeSet_of_finite_right (hLR : G.IsBipartiteWith L R) (hR : R.Finite)
    {M : G.Subgraph} (hM : M.IsMatching) :
    M.edgeSet.Finite :=
  hLR.symm.finite_edgeSet_of_finite_left hR hM

/-- When `L` is finite, a matching has at most `L.ncard` edges. -/
theorem ncard_edgeSet_le_left (hLR : G.IsBipartiteWith L R) (hL : L.Finite)
    {M : G.Subgraph} (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ L.ncard :=
  hM.ncard_edgeSet_le_of_isVertexCover hLR.isVertexCover_left hL

/-- When `R` is finite, a matching has at most `R.ncard` edges. -/
theorem ncard_edgeSet_le_right (hLR : G.IsBipartiteWith L R) (hR : R.Finite)
    {M : G.Subgraph} (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ R.ncard :=
  hLR.symm.ncard_edgeSet_le_left hR hM

/-- The matching number is at most `L.encard`. -/
theorem matchingNum_le_encard_left (hLR : G.IsBipartiteWith L R) :
    G.matchingNum ≤ L.encard :=
  matchingNum_le_vertexCoverNum.trans hLR.isVertexCover_left.vertexCoverNum_le

/-- The matching number is at most `R.encard`. -/
theorem matchingNum_le_encard_right (hLR : G.IsBipartiteWith L R) :
    G.matchingNum ≤ R.encard :=
  hLR.symm.matchingNum_le_encard_left

/-- When `L` is finite, a matching saturates `L` if and only if it has `L.encard` edges. -/
theorem subset_verts_iff_encard_edgeSet_eq (hLR : G.IsBipartiteWith L R) (hL : L.Finite)
    {M : G.Subgraph} (hM : M.IsMatching) :
    L ⊆ M.verts ↔ M.edgeSet.encard = L.encard := by
  rw [← hLR.encard_verts_inter_left hM]
  refine ⟨fun h ↦ by rw [Set.inter_eq_self_of_subset_right h], fun h ↦ ?_⟩
  have heq := hL.eq_of_subset_of_encard_le' Set.inter_subset_right h.symm.le
  exact heq ▸ Set.inter_subset_left

/-- When `L` is finite, a matching saturates `L` if and only if it has `L.ncard` edges. -/
theorem subset_verts_iff_ncard_edgeSet_eq (hLR : G.IsBipartiteWith L R) (hL : L.Finite)
    {M : G.Subgraph} (hM : M.IsMatching) :
    L ⊆ M.verts ↔ M.edgeSet.ncard = L.ncard := by
  have hMf : M.edgeSet.Finite := hLR.finite_edgeSet_of_finite_left hL hM
  rw [hLR.subset_verts_iff_encard_edgeSet_eq hL hM, ← hMf.cast_ncard_eq, ← hL.cast_ncard_eq,
    Nat.cast_inj]

end IsBipartiteWith

/-! ### The Kőnig–Ore deficiency formula and Hall's condition -/

/-- **Universal Kőnig–Ore inequality** in `ℕ∞`: for every matching `M` and every `S : Set V`,
`M.edgeSet.encard ≤ (L \ S).encard + (⋃ x ∈ S, G.neighborSet x).encard`, with no finiteness
assumptions. -/
theorem Subgraph.IsMatching.encard_edgeSet_le_encard_sdiff_add_encard
    {M : G.Subgraph} (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) (S : Set V) :
    M.edgeSet.encard ≤ (L \ S).encard + (⋃ x ∈ S, G.neighborSet x).encard :=
  hM.encard_edgeSet_le_encard_sdiff_add_encard_of_isVertexCover hLR.isVertexCover_left S

/-- **Additive universal Kőnig–Ore inequality** in `ℕ∞`: for every matching `M` and every `S ⊆ L`,
`M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard`. See
`Subgraph.IsMatching.encard_edgeSet_le_encard_sdiff_add_encard` for the un-cancelled form that
remains non-trivial when `L` is infinite. -/
theorem Subgraph.IsMatching.encard_edgeSet_add_encard_le {M : G.Subgraph} (hM : M.IsMatching)
    (hLR : G.IsBipartiteWith L R) {S : Set V} (hS : S ⊆ L) :
    M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
  calc
    M.edgeSet.encard + S.encard
      ≤ ((L \ S).encard + (⋃ x ∈ S, G.neighborSet x).encard) + S.encard :=
        add_le_add_left (hM.encard_edgeSet_le_encard_sdiff_add_encard hLR S) S.encard
    _ = ((L \ S).encard + S.encard) + (⋃ x ∈ S, G.neighborSet x).encard := by ac_rfl
    _ = L.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
        rw [Set.encard_sdiff_add_encard_of_subset hS]

/-- **Universal Kőnig–Ore inequality** in `Set.ncard` form when `L` and the neighbourhood of `S`
are finite. -/
theorem Subgraph.IsMatching.ncard_edgeSet_add_ncard_le_of_finite {M : G.Subgraph}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) {S : Set V} (hS : S ⊆ L) (hL : L.Finite)
    (hN : (⋃ x ∈ S, G.neighborSet x).Finite) :
    M.edgeSet.ncard + S.ncard ≤ L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard := by
  have hMf : M.edgeSet.Finite := hLR.finite_edgeSet_of_finite_left hL hM
  have hSf : S.Finite := hL.subset hS
  have hle := hM.encard_edgeSet_add_encard_le hLR hS
  rwa [← hMf.cast_ncard_eq, ← hSf.cast_ncard_eq, ← hL.cast_ncard_eq, ← hN.cast_ncard_eq,
    ← Nat.cast_add, ← Nat.cast_add, Nat.cast_le] at hle

/-- **Universal Kőnig–Ore inequality** on a finite vertex type. -/
theorem Subgraph.IsMatching.ncard_edgeSet_add_ncard_le [Finite V] {M : G.Subgraph}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) {S : Set V} (hS : S ⊆ L) :
    M.edgeSet.ncard + S.ncard ≤ L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard :=
  hM.ncard_edgeSet_add_ncard_le_of_finite hLR hS L.toFinite (Set.toFinite _)

namespace IsBipartiteWith

/-- **Kőnig–Ore deficiency formula** in `ℕ∞` witness form, with no finiteness assumptions: there
exist a matching `M` and a subset `S ⊆ L` attaining equality in
`Subgraph.IsMatching.encard_edgeSet_le_encard_sdiff_add_encard`. -/
theorem exists_isMatching_encard_edgeSet_eq_encard_sdiff_add_encard
    (hLR : G.IsBipartiteWith L R) :
    ∃ (M : G.Subgraph) (S : Set V), M.IsMatching ∧ S ⊆ L ∧
      M.edgeSet.encard = (L \ S).encard + (⋃ x ∈ S, G.neighborSet x).encard := by
  obtain ⟨M, C, hM, hC, hMC⟩ := hLR.isBipartite.exists_isMatching_isVertexCover_encard_eq
  -- Set `S = L \ C`. Every neighbour of `S` must lie in `C` (since `C` covers `G`) and in `R`
  -- (since `S ⊆ L`), so `N(S) ⊆ C \ L` is disjoint from `L \ S = L ∩ C`.
  let S : Set V := L \ C
  have hNsub : (⋃ x ∈ S, G.neighborSet x) ⊆ C \ L := by
    rintro y hy
    obtain ⟨x, ⟨hxL, hxC⟩, hxy⟩ := Set.mem_iUnion₂.1 hy
    exact ⟨(hC hxy).resolve_left hxC,
      Set.disjoint_right.1 hLR.disjoint (hLR.mem_of_mem_adj hxL hxy)⟩
  have hdisj : Disjoint (L ∩ C) (⋃ x ∈ S, G.neighborSet x) :=
    Set.disjoint_sdiff_right.mono Set.inter_subset_left hNsub
  have hsubC : (L ∩ C) ∪ (⋃ x ∈ S, G.neighborSet x) ⊆ C :=
    Set.union_subset Set.inter_subset_right (hNsub.trans Set.sdiff_subset)
  refine ⟨M, S, hM, Set.sdiff_subset,
    le_antisymm (hM.encard_edgeSet_le_encard_sdiff_add_encard hLR S) ?_⟩
  calc
    (L \ S).encard + (⋃ x ∈ S, G.neighborSet x).encard
      = (L ∩ C).encard + (⋃ x ∈ S, G.neighborSet x).encard := by
        rw [sdiff_sdiff_right_self]
    _ = ((L ∩ C) ∪ ⋃ x ∈ S, G.neighborSet x).encard := (Set.encard_union_eq hdisj).symm
    _ ≤ C.encard := Set.encard_mono hsubC
    _ = M.edgeSet.encard := hMC.symm

/-- **Kőnig–Ore deficiency formula** in `Set.ncard` witness form when `L` is finite: the witness
subset `S ⊆ L` automatically has finite neighbourhood `(⋃ x ∈ S, G.neighborSet x)`. -/
theorem exists_isMatching_ncard_edgeSet_add_ncard_eq_of_finite (hLR : G.IsBipartiteWith L R)
    (hL : L.Finite) :
    ∃ (M : G.Subgraph) (S : Set V), M.IsMatching ∧ S ⊆ L ∧
      (⋃ x ∈ S, G.neighborSet x).Finite ∧
      M.edgeSet.ncard + S.ncard = L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard := by
  obtain ⟨M, S, hM, hS, heq⟩ := hLR.exists_isMatching_encard_edgeSet_eq_encard_sdiff_add_encard
  have hMf : M.edgeSet.Finite := hLR.finite_edgeSet_of_finite_left hL hM
  have hSf : S.Finite := hL.subset hS
  have hNf : (⋃ x ∈ S, G.neighborSet x).Finite :=
    hMf.finite_of_encard_le (le_add_self.trans_eq heq.symm)
  refine ⟨M, S, hM, hS, hNf, ?_⟩
  have hadd : M.edgeSet.encard + S.encard = L.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
    calc
      M.edgeSet.encard + S.encard
        = ((L \ S).encard + (⋃ x ∈ S, G.neighborSet x).encard) + S.encard := by rw [heq]
      _ = ((L \ S).encard + S.encard) + (⋃ x ∈ S, G.neighborSet x).encard := by ac_rfl
      _ = L.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
          rw [Set.encard_sdiff_add_encard_of_subset hS]
  rwa [← hMf.cast_ncard_eq, ← hSf.cast_ncard_eq, ← hL.cast_ncard_eq, ← hNf.cast_ncard_eq,
    ← Nat.cast_add, ← Nat.cast_add, Nat.cast_inj] at hadd

/-- **Kőnig–Ore deficiency formula** in witness form on a finite vertex type. -/
theorem exists_isMatching_ncard_edgeSet_add_ncard_eq [Finite V] (hLR : G.IsBipartiteWith L R) :
    ∃ (M : G.Subgraph) (S : Set V), M.IsMatching ∧ S ⊆ L ∧
      M.edgeSet.ncard + S.ncard = L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard := by
  obtain ⟨M, S, hM, hS, -, heq⟩ :=
    hLR.exists_isMatching_ncard_edgeSet_add_ncard_eq_of_finite L.toFinite
  exact ⟨M, S, hM, hS, heq⟩

/-- **Numerical Kőnig–Ore deficiency formula.** For finite `L`, the matching number equals
`L.encard` minus the maximum deficiency `S.encard - (⋃ x ∈ S, G.neighborSet x).encard` over
`S ⊆ L`. -/
theorem matchingNum_eq_encard_sub_iSup (hLR : G.IsBipartiteWith L R) (hL : L.Finite) :
    G.matchingNum =
      L.encard - ⨆ (S : Set V) (_ : S ⊆ L), (S.encard - (⋃ x ∈ S, G.neighborSet x).encard) := by
  obtain ⟨M, S₀, hM, hS₀, heq⟩ :=
    hLR.exists_isMatching_encard_edgeSet_eq_encard_sdiff_add_encard
  have hMnum : G.matchingNum = M.edgeSet.encard :=
    le_antisymm (matchingNum_le_iff.2 fun M' hM' ↦
      (hM'.encard_edgeSet_le_encard_sdiff_add_encard hLR S₀).trans_eq heq.symm)
      hM.encard_edgeSet_le_matchingNum
  have hLtop : L.encard ≠ ⊤ := hL.encard_lt_top.ne
  have hMle : M.edgeSet.encard ≤ L.encard := hLR.encard_edgeSet_le_left hM
  have hMtop : M.edgeSet.encard ≠ ⊤ := ne_top_of_le_ne_top hLtop hMle
  have hDeq : (⨆ (S : Set V) (_ : S ⊆ L), (S.encard - (⋃ x ∈ S, G.neighborSet x).encard)) =
      L.encard - M.edgeSet.encard := by
    refine le_antisymm (iSup₂_le fun S hS ↦ tsub_le_iff_right.2 ?_)
      (le_trans ?_ (le_iSup₂
        (f := fun S (_ : S ⊆ L) ↦ S.encard - (⋃ x ∈ S, G.neighborSet x).encard) S₀ hS₀))
    · refine (ENat.add_le_add_iff_left hMtop).1 ?_
      calc
        M.edgeSet.encard + S.encard
          ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard :=
            hM.encard_edgeSet_add_encard_le hLR hS
        _ = (L.encard - M.edgeSet.encard + M.edgeSet.encard) +
            (⋃ x ∈ S, G.neighborSet x).encard := by rw [tsub_add_cancel_of_le hMle]
        _ = M.edgeSet.encard +
            ((L.encard - M.edgeSet.encard) + (⋃ x ∈ S, G.neighborSet x).encard) := by ac_rfl
    · have hpart : (L \ S₀).encard + S₀.encard = L.encard :=
        Set.encard_sdiff_add_encard_of_subset hS₀
      have hLStop : (L \ S₀).encard ≠ ⊤ :=
        ne_top_of_le_ne_top hLtop (Set.encard_mono Set.sdiff_subset)
      have hN₀le : (⋃ x ∈ S₀, G.neighborSet x).encard ≤ S₀.encard :=
        (ENat.add_le_add_iff_left hLStop).1 (heq ▸ hpart.symm ▸ hMle)
      refine tsub_le_iff_right.2 (le_of_eq ?_)
      calc
        L.encard = (L \ S₀).encard + S₀.encard := hpart.symm
        _ = (L \ S₀).encard + (S₀.encard - (⋃ x ∈ S₀, G.neighborSet x).encard +
            (⋃ x ∈ S₀, G.neighborSet x).encard) := by rw [tsub_add_cancel_of_le hN₀le]
        _ = (S₀.encard - (⋃ x ∈ S₀, G.neighborSet x).encard) +
            ((L \ S₀).encard + (⋃ x ∈ S₀, G.neighborSet x).encard) := by ac_rfl
        _ = (S₀.encard - (⋃ x ∈ S₀, G.neighborSet x).encard) + M.edgeSet.encard := by rw [heq]
  rw [hMnum, hDeq, ENat.sub_sub_cancel hLtop hMle]

/-- **Hall's marriage theorem** for finite `L`, in `ℕ∞` form without local finiteness: there exists
a matching saturating `L` if and only if every `S ⊆ L` has `(⋃ x ∈ S, G.neighborSet x).encard` at
least `S.encard`. -/
theorem exists_isMatching_subset_verts_iff_forall_encard_le (hLR : G.IsBipartiteWith L R)
    (hL : L.Finite) :
    (∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ S ⊆ L, S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard := by
  refine ⟨fun ⟨M, hsub, hM⟩ S hS ↦ ?_, fun hHall ↦ ?_⟩
  · have hML : M.edgeSet.encard = L.encard :=
      (hLR.subset_verts_iff_encard_edgeSet_eq hL hM).1 hsub
    have hle := hM.encard_edgeSet_add_encard_le hLR hS
    rwa [hML, ENat.add_le_add_iff_left hL.encard_lt_top.ne] at hle
  · obtain ⟨M, S, hM, hS, heq⟩ :=
      hLR.exists_isMatching_encard_edgeSet_eq_encard_sdiff_add_encard
    have hle : L.encard ≤ M.edgeSet.encard := by
      calc
        L.encard = (L \ S).encard + S.encard := (Set.encard_sdiff_add_encard_of_subset hS).symm
        _ ≤ (L \ S).encard + (⋃ x ∈ S, G.neighborSet x).encard :=
          add_le_add_right (hHall S hS) _
        _ = M.edgeSet.encard := heq.symm
    exact ⟨M, (hLR.subset_verts_iff_encard_edgeSet_eq hL hM).2
      (le_antisymm (hLR.encard_edgeSet_le_left hM) hle), hM⟩

/-- **Hall's marriage theorem** on a finite vertex type: a matching saturating `L` exists if and
only if every `S ⊆ L` has at least `S.ncard` neighbours, with backward direction matching the finite
specialization of `SimpleGraph.exists_isMatching_of_forall_ncard_le`. -/
theorem exists_isMatching_subset_verts_iff [Finite V] (hLR : G.IsBipartiteWith L R) :
    (∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ S ⊆ L, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  rw [hLR.exists_isMatching_subset_verts_iff_forall_encard_le L.toFinite]
  refine forall₂_congr fun S _ ↦ ?_
  rw [← S.toFinite.cast_ncard_eq, ← (Set.toFinite _).cast_ncard_eq, Nat.cast_le]

end IsBipartiteWith

end SimpleGraph
