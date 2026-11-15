/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.OfSimpleGraph
public import TauCeti.Combinatorics.Graph.Matching.VertexCover
public import TauCeti.Combinatorics.SimpleGraph.Matching.Basic

/-!
# Kőnig's theorem and the Kőnig–Ore deficiency formula for simple graphs

In any bipartite simple graph `G : SimpleGraph V`, the matching number equals the vertex cover
number:

`G.matchingNum = G.vertexCoverNum`,

and there exist a matching `M : G.Subgraph` and a vertex cover `C : Set V` with
`M.edgeSet.encard = C.encard`. No finiteness assumption on `V` or `G` is required for the
`ℕ∞`-valued theorem:

* on a finite vertex type, a `2`-colouring partitions `V` into two finite sides covering every
  vertex, and the multigraph Kőnig theorem on `Graph.ofSimpleGraph G` transports to `G` across
  `SimpleGraph.matchingSubgraph`;
* when `G.vertexCoverNum < ⊤` on an arbitrary vertex type, choosing a finite vertex cover `C₀` of
  size `k` and retaining at most `k + 1` neighbours of each `u ∈ C₀` produces a finite induced
  subgraph whose minimum cover has size at most `k`, so any vertex of `C₀` with more than `k`
  retained neighbours is forced into the cover and the cover extends to all of `G`;
* when `G.vertexCoverNum = ⊤`, any inclusion-maximal matching has infinitely many edges and its
  vertex set covers `G`.

When `G` is equipped with a displayed bipartition `G.IsBipartiteWith L R` (which allows isolated
vertices outside `L ∪ R`), normalizing a minimum vertex cover `C` to `S = L \ C` yields the
**Kőnig–Ore deficiency formula**: there exist a matching `M` and `S ⊆ L` with
`M.edgeSet.encard + S.encard = L.encard + (⋃ x ∈ S, G.neighborSet x).encard` (and the
corresponding `Set.ncard` identity when `L` is finite), matching the universal inequality
`(L \ S) ∪ N(S)` gives for every matching and every `S ⊆ L`. For finite `L`, this yields

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
* `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_add_encard_le` and
  `SimpleGraph.Subgraph.IsMatching.ncard_edgeSet_add_ncard_le`: the universal Kőnig–Ore inequality.
* `SimpleGraph.IsBipartiteWith.exists_isMatching_encard_edgeSet_add_encard_eq`,
  `SimpleGraph.IsBipartiteWith.exists_isMatching_ncard_edgeSet_add_ncard_eq`, and
  `SimpleGraph.IsBipartiteWith.matchingNum_eq_encard_sub_iSup`: the **Kőnig–Ore deficiency
  formula** in witness and numerical forms.
* `SimpleGraph.IsBipartiteWith.exists_isMatching_subset_verts_iff`: finite Hall characterization
  recovered from Kőnig–Ore deficiency.

## References

* D. Kőnig, *Gráfok és mátrixok*, Mat. Fiz. Lapok 38 (1931), 116–119.
* Ø. Ore, *Graphs and matching theorems*, Duke Math. J. 22 (1955), 625–639.
-/

public section

open scoped Graph

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {L R : Set V}

/-! ### Kőnig's theorem -/

/-- Auxiliary finite-vertex case of Kőnig's theorem, deduced from the multigraph Kőnig theorem via
`Graph.ofSimpleGraph`. -/
private theorem IsBipartite.exists_isMatching_isVertexCover_encard_eq_of_finite [Finite V]
    (hG : G.IsBipartite) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧
      M.edgeSet.encard = C.encard := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨c⟩ := hG
  -- Use the `2`-colouring to partition all vertices of `Graph.ofSimpleGraph G`, including any
  -- isolated vertices.
  let L₀ : Finset V(Graph.ofSimpleGraph G) := Finset.univ.filter fun x ↦ c x.1 = 0
  let R₀ : Finset V(Graph.ofSimpleGraph G) := Finset.univ.filter fun x ↦ c x.1 = 1
  have hLR : (Graph.ofSimpleGraph G).IsBipartition L₀ R₀ := by
    refine ⟨Finset.disjoint_left.2 fun x hxL hxR ↦ ?_, fun x ↦ ?_, fun {e x y} he ↦ ?_⟩
    · simp only [L₀, R₀, Finset.mem_filter, Finset.mem_univ, true_and] at hxL hxR
      exact absurd (hxL.symm.trans hxR) (by decide)
    · simp only [L₀, R₀, Finset.mem_filter, Finset.mem_univ, true_and]
      have hlt : (c x.1).val < 2 := (c x.1).isLt
      rcases (by omega : (c x.1).val = 0 ∨ (c x.1).val = 1) with h0 | h1
      · exact Or.inl (Fin.ext h0)
      · exact Or.inr (Fin.ext h1)
    · have hxy : G.Adj x.1 y.1 := (Graph.ofSimpleGraph_adj_iff x.1 y.1).1 ⟨e, he⟩
      have hne : c x.1 ≠ c y.1 := c.valid hxy
      simp only [L₀, R₀, Finset.mem_filter, Finset.mem_univ, true_and]
      have hx2 : (c x.1).val < 2 := (c x.1).isLt
      have hy2 : (c y.1).val < 2 := (c y.1).isLt
      have hnev : (c x.1).val ≠ (c y.1).val := fun h ↦ hne (Fin.ext h)
      rcases (by omega :
          (c x.1).val = 0 ∧ (c y.1).val = 1 ∨ (c x.1).val = 1 ∧ (c y.1).val = 0) with
        ⟨hx0, hy1⟩ | ⟨hx1, hy0⟩
      · exact Or.inl ⟨Fin.ext hx0, Fin.ext hy1⟩
      · exact Or.inr ⟨Fin.ext hx1, Fin.ext hy0⟩
  obtain ⟨M₀, C₀, hM₀, hC₀, hcard⟩ := hLR.exists_isMatching_isVertexCover_card_eq
  refine ⟨G.matchingSubgraph (M₀ : Set E(Graph.ofSimpleGraph G)),
    Subtype.val '' (C₀ : Set V(Graph.ofSimpleGraph G)),
    (G.matchingSubgraph_isMatching_iff _).2 hM₀,
    G.isVertexCover_ofSimpleGraph_image_iff.2 hC₀, ?_⟩
  rw [edgeSet_matchingSubgraph, Subtype.val_injective.encard_image,
    Subtype.val_injective.encard_image, Set.encard_coe_eq_coe_finsetCard,
    Set.encard_coe_eq_coe_finsetCard, hcard]

/-- Given a finite vertex cover `C₀` of `G`, there exists an induced subgraph `S : G.Subgraph` on a
finite vertex set `S.verts ⊇ C₀` such that every vertex cover of `S.coe` of extended cardinality at
most `C₀.encard` pushes forward to a vertex cover of `G`. -/
theorem IsVertexCover.exists_finite_verts_isVertexCover_image {C₀ : Set V}
    (hC₀ : G.IsVertexCover C₀) (hC₀fin : C₀.Finite) :
    ∃ S : G.Subgraph, C₀ ⊆ S.verts ∧ S.verts.Finite ∧
      ∀ ⦃C₁ : Set S.verts⦄, S.coe.IsVertexCover C₁ → C₁.encard ≤ C₀.encard →
        G.IsVertexCover (Subtype.val '' C₁) := by
  -- Retain at most `C₀.ncard + 1` neighbours of each vertex of `C₀`; any cover of the resulting
  -- finite induced subgraph of size at most `C₀.ncard` must include every vertex of `C₀` that has
  -- neighbours outside the induced subgraph.
  let k : ℕ := C₀.ncard
  have hk : C₀.encard = k := hC₀fin.cast_ncard_eq.symm
  have hexA (x : V) : ∃ A : Set V, A ⊆ G.neighborSet x ∧ A.Finite ∧
      (G.neighborSet x ⊆ A ∨ A.encard = (k + 1 : ℕ)) := by
    by_cases hle : ((k + 1 : ℕ) : ℕ∞) ≤ (G.neighborSet x).encard
    · obtain ⟨A, hAsub, hAcard⟩ := Set.exists_subset_encard_eq hle
      exact ⟨A, hAsub, Set.encard_ne_top_iff.1 (by simp [hAcard]), Or.inr hAcard⟩
    · have hfin : (G.neighborSet x).Finite :=
        Set.encard_lt_top_iff.1 ((lt_of_not_ge hle).trans_le le_top)
      exact ⟨G.neighborSet x, Set.Subset.rfl, hfin, Or.inl Set.Subset.rfl⟩
  choose A hAsub hAfin hAcase using hexA
  let S : G.Subgraph := (⊤ : G.Subgraph).induce (C₀ ∪ ⋃ x ∈ C₀, A x)
  refine ⟨S, Set.subset_union_left, hC₀fin.union (hC₀fin.biUnion fun x _ ↦ hAfin x),
    fun C₁ hC₁ hC₁le ↦ ?_⟩
  have hcov_left {u v : V} (huv : G.Adj u v) (hu₀ : u ∈ C₀) :
      u ∈ Subtype.val '' C₁ ∨ v ∈ Subtype.val '' C₁ := by
    have huU : u ∈ S.verts := Or.inl hu₀
    rcases hAcase u with hall | hlarge
    · have hvU : v ∈ S.verts := Or.inr (Set.mem_iUnion₂.2 ⟨u, hu₀, hall huv⟩)
      have hadjS : S.coe.Adj ⟨u, huU⟩ ⟨v, hvU⟩ := ⟨huU, hvU, huv⟩
      exact (hC₁ hadjS).imp (fun h ↦ ⟨⟨u, huU⟩, h, rfl⟩) (fun h ↦ ⟨⟨v, hvU⟩, h, rfl⟩)
    · refine Or.inl ?_
      by_contra huC
      have hsub : A u ⊆ Subtype.val '' C₁ := fun w hw ↦ by
        have hwU : w ∈ S.verts := Or.inr (Set.mem_iUnion₂.2 ⟨u, hu₀, hw⟩)
        have hadjS : S.coe.Adj ⟨u, huU⟩ ⟨w, hwU⟩ := ⟨huU, hwU, hAsub u hw⟩
        rcases hC₁ hadjS with hu1 | hw1
        · exact absurd ⟨⟨u, huU⟩, hu1, rfl⟩ huC
        · exact ⟨⟨w, hwU⟩, hw1, rfl⟩
      have hbad : ((k + 1 : ℕ) : ℕ∞) ≤ k := by
        calc
          ((k + 1 : ℕ) : ℕ∞) = (A u).encard := hlarge.symm
          _ ≤ (Subtype.val '' C₁).encard := Set.encard_mono hsub
          _ = C₁.encard := Subtype.val_injective.encard_image C₁
          _ ≤ k := hC₁le.trans_eq hk
      exact absurd (Nat.cast_le.1 hbad) (by omega)
  intro u v huv
  rcases hC₀ huv with hu₀ | hv₀
  · exact hcov_left huv hu₀
  · exact (hcov_left huv.symm hv₀).symm

/-- **Kőnig's theorem** in `ℕ∞` witness form, with no finiteness assumptions: every bipartite
simple graph has a matching and a vertex cover of equal extended cardinality. -/
theorem IsBipartite.exists_isMatching_isVertexCover_encard_eq (hG : G.IsBipartite) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧
      M.edgeSet.encard = C.encard := by
  by_cases htop : G.vertexCoverNum = ⊤
  · -- When the cover number is infinite, any maximal matching has infinitely many edges and its
    -- vertex set covers `G`.
    obtain ⟨M, -, hmax⟩ := (Subgraph.isMatching_bot (G := G)).exists_le_maximal
    have hcov := Subgraph.isVertexCover_verts_of_maximal_isMatching hmax
    have hMtop : M.edgeSet.encard = ⊤ := by
      have hle : 2 * M.edgeSet.encard = ⊤ := eq_top_iff.2 <| by
        rw [← hmax.prop.encard_verts, ← htop]
        exact hcov.vertexCoverNum_le
      simpa [two_mul] using hle
    exact ⟨M, M.verts, hmax.prop, hcov, by simp [hmax.prop.encard_verts, hMtop]⟩
  · obtain ⟨C₀, hC₀num, hC₀⟩ := G.vertexCoverNum_exists
    have hC₀fin : C₀.Finite := Set.encard_ne_top_iff.1 (hC₀num.trans_ne htop)
    obtain ⟨S, -, hSfin, hScov⟩ := hC₀.exists_finite_verts_isVertexCover_image hC₀fin
    let _ : Finite S.verts := hSfin.to_subtype
    obtain ⟨M₀, C₁, hM₀, hC₁, hMC₁⟩ :=
      (hG.subgraph S).exists_isMatching_isVertexCover_encard_eq_of_finite
    have hC₀S : S.coe.IsVertexCover {u : S.verts | u.1 ∈ C₀} := fun _ _ huv ↦ hC₀ (S.adj_sub huv)
    have hC₁le : C₁.encard ≤ C₀.encard := by
      calc
        C₁.encard = M₀.edgeSet.encard := hMC₁.symm
        _ ≤ {u : S.verts | u.1 ∈ C₀}.encard := hM₀.encard_edgeSet_le_of_isVertexCover hC₀S
        _ = (Subtype.val '' {u : S.verts | u.1 ∈ C₀}).encard :=
          (Subtype.val_injective.encard_image _).symm
        _ ≤ C₀.encard := Set.encard_mono (by rintro _ ⟨u, hu, rfl⟩; exact hu)
    refine ⟨Subgraph.coeSubgraph M₀, Subtype.val '' C₁, hM₀.coeSubgraph, hScov hC₁ hC₁le, ?_⟩
    have hhom : Function.Injective S.hom := fun _ _ h ↦ Subtype.ext h
    rw [Subgraph.coeSubgraph, Subgraph.edgeSet_map, (Sym2.map.injective hhom).encard_image,
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
edges. -/
theorem IsBipartite.exists_isMatching_isVertexCover_ncard_eq_of_finite_edgeSet
    (hG : G.IsBipartite) (hE : G.edgeSet.Finite) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧
      M.edgeSet.ncard = C.ncard := by
  obtain ⟨M, C, hM, hC, -, hMC⟩ :=
    hG.exists_isMatching_isVertexCover_ncard_eq_of_vertexCoverNum_ne_top
      (vertexCoverNum_ne_top_of_finite_edgeSet hE)
  exact ⟨M, C, hM, hC, hMC⟩

/-- **Kőnig's theorem** in `Set.ncard` witness form on a finite vertex type. -/
theorem IsBipartite.exists_isMatching_isVertexCover_ncard_eq [Finite V] (hG : G.IsBipartite) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧
      M.edgeSet.ncard = C.ncard :=
  hG.exists_isMatching_isVertexCover_ncard_eq_of_finite_edgeSet G.edgeSet.toFinite

/-! ### Matchings on a displayed bipartition -/

namespace IsBipartiteWith

/-- The left side of a displayed bipartition is a vertex cover of `G`; isolated vertices outside
`L ∪ R` have no incident edges. -/
theorem isVertexCover_left (hLR : G.IsBipartiteWith L R) : G.IsVertexCover L :=
  fun _ _ hadj ↦ (hLR.mem_of_adj hadj).imp And.left And.right

/-- The right side of a displayed bipartition is a vertex cover of `G`. -/
theorem isVertexCover_right (hLR : G.IsBipartiteWith L R) : G.IsVertexCover R :=
  hLR.symm.isVertexCover_left

/-- For any subset `S`, removing `S` from `L` and adding its neighbourhood `(⋃ x ∈ S,
G.neighborSet x)` yields a vertex cover of `G`. -/
theorem isVertexCover_sdiff_union_biUnion_neighborSet (hLR : G.IsBipartiteWith L R) (S : Set V) :
    G.IsVertexCover ((L \ S) ∪ ⋃ x ∈ S, G.neighborSet x) := by
  intro u v huv
  rcases hLR.mem_of_adj huv with ⟨huL, -⟩ | ⟨-, hvL⟩
  · by_cases huS : u ∈ S
    · exact Or.inr (Or.inr <| Set.mem_iUnion₂.2 ⟨u, huS, huv⟩)
    · exact Or.inl (Or.inl ⟨huL, huS⟩)
  · by_cases hvS : v ∈ S
    · exact Or.inl (Or.inr <| Set.mem_iUnion₂.2 ⟨v, hvS, huv.symm⟩)
    · exact Or.inr (Or.inl ⟨hvL, hvS⟩)

/-- Every edge of a matching in a graph with bipartition `(L, R)` meets `L` in a unique vertex,
identifying `M.verts ∩ L` with `M.edgeSet`. -/
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

/-- Every edge of a matching in a graph with bipartition `(L, R)` meets `R` in a unique vertex. -/
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
  have hMf : M.edgeSet.Finite := hL.finite_of_encard_le (hLR.encard_edgeSet_le_left hM)
  rw [hLR.subset_verts_iff_encard_edgeSet_eq hL hM, ← hMf.cast_ncard_eq, ← hL.cast_ncard_eq,
    Nat.cast_inj]

end IsBipartiteWith

/-! ### The Kőnig–Ore deficiency formula and Hall's condition -/

/-- **Universal Kőnig–Ore inequality** in `ℕ∞`: for every matching `M` and every `S ⊆ L`,
`M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard`, with no finiteness
assumptions. -/
theorem Subgraph.IsMatching.encard_edgeSet_add_encard_le {M : G.Subgraph} (hM : M.IsMatching)
    (hLR : G.IsBipartiteWith L R) {S : Set V} (hS : S ⊆ L) :
    M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
  have hcov := hLR.isVertexCover_sdiff_union_biUnion_neighborSet S
  calc
    M.edgeSet.encard + S.encard
      ≤ ((L \ S) ∪ ⋃ x ∈ S, G.neighborSet x).encard + S.encard :=
        add_le_add_left (hM.encard_edgeSet_le_of_isVertexCover hcov) S.encard
    _ ≤ ((L \ S).encard + (⋃ x ∈ S, G.neighborSet x).encard) + S.encard :=
        add_le_add_left (Set.encard_union_le _ _) S.encard
    _ = ((L \ S).encard + S.encard) + (⋃ x ∈ S, G.neighborSet x).encard := by ac_rfl
    _ = L.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
        rw [Set.encard_sdiff_add_encard_of_subset hS]

/-- **Universal Kőnig–Ore inequality** in `Set.ncard` form when `L` and the neighbourhood of `S`
are finite. -/
theorem Subgraph.IsMatching.ncard_edgeSet_add_ncard_le_of_finite {M : G.Subgraph}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) {S : Set V} (hS : S ⊆ L) (hL : L.Finite)
    (hN : (⋃ x ∈ S, G.neighborSet x).Finite) :
    M.edgeSet.ncard + S.ncard ≤ L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard := by
  have hMf : M.edgeSet.Finite := hL.finite_of_encard_le (hLR.encard_edgeSet_le_left hM)
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
`Subgraph.IsMatching.encard_edgeSet_add_encard_le`. -/
theorem exists_isMatching_encard_edgeSet_add_encard_eq (hLR : G.IsBipartiteWith L R) :
    ∃ (M : G.Subgraph) (S : Set V), M.IsMatching ∧ S ⊆ L ∧
      M.edgeSet.encard + S.encard = L.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
  obtain ⟨M, C, hM, hC, hMC⟩ := hLR.isBipartite.exists_isMatching_isVertexCover_encard_eq
  -- Set `S = L \ C`. Every neighbour of `S` must lie in `C` (since `C` covers `G`) and in `R`
  -- (since `S ⊆ L`), so `N(S) ⊆ C \ L` is disjoint from `L ∩ C`.
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
    le_antisymm (hM.encard_edgeSet_add_encard_le hLR Set.sdiff_subset) ?_⟩
  calc
    L.encard + (⋃ x ∈ S, G.neighborSet x).encard
      = (S.encard + (L ∩ C).encard) + (⋃ x ∈ S, G.neighborSet x).encard := by
        rw [Set.encard_sdiff_add_encard_inter L C]
    _ = ((L ∩ C).encard + (⋃ x ∈ S, G.neighborSet x).encard) + S.encard := by ac_rfl
    _ = ((L ∩ C) ∪ ⋃ x ∈ S, G.neighborSet x).encard + S.encard := by
        rw [Set.encard_union_eq hdisj]
    _ ≤ C.encard + S.encard := add_le_add_left (Set.encard_mono hsubC) S.encard
    _ = M.edgeSet.encard + S.encard := by rw [hMC]

/-- **Kőnig–Ore deficiency formula** in `Set.ncard` witness form when `L` is finite: the witness
subset `S ⊆ L` automatically has finite neighbourhood `(⋃ x ∈ S, G.neighborSet x)`. -/
theorem exists_isMatching_ncard_edgeSet_add_ncard_eq_of_finite (hLR : G.IsBipartiteWith L R)
    (hL : L.Finite) :
    ∃ (M : G.Subgraph) (S : Set V), M.IsMatching ∧ S ⊆ L ∧
      (⋃ x ∈ S, G.neighborSet x).Finite ∧
      M.edgeSet.ncard + S.ncard = L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard := by
  obtain ⟨M, S, hM, hS, heq⟩ := hLR.exists_isMatching_encard_edgeSet_add_encard_eq
  have hMf : M.edgeSet.Finite := hL.finite_of_encard_le (hLR.encard_edgeSet_le_left hM)
  have hSf : S.Finite := hL.subset hS
  have hNf : (⋃ x ∈ S, G.neighborSet x).Finite := by
    refine Set.encard_ne_top_iff.1 fun htop ↦ ?_
    have hsum : M.edgeSet.encard + S.encard ≠ ⊤ := by
      simp [hMf.encard_lt_top.ne, hSf.encard_lt_top.ne]
    exact hsum (heq.trans (by simp [htop]))
  refine ⟨M, S, hM, hS, hNf, ?_⟩
  rwa [← hMf.cast_ncard_eq, ← hSf.cast_ncard_eq, ← hL.cast_ncard_eq, ← hNf.cast_ncard_eq,
    ← Nat.cast_add, ← Nat.cast_add, Nat.cast_inj] at heq

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
  set D : ℕ∞ := ⨆ (S : Set V) (_ : S ⊆ L), (S.encard - (⋃ x ∈ S, G.neighborSet x).encard)
  have hDle : D ≤ L.encard := iSup₂_le fun S hS ↦ tsub_le_self.trans (Set.encard_mono hS)
  have hLtop : L.encard ≠ ⊤ := hL.encard_lt_top.ne
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top hLtop hDle)
  obtain ⟨Mmax, hMmax_eq, hMmax⟩ := G.matchingNum_exists
  have hMmaxf : Mmax.edgeSet.Finite := hL.finite_of_encard_le (hLR.encard_edgeSet_le_left hMmax)
  -- First show `d ≤ L.ncard - Mmax.edgeSet.ncard` via the universal Kőnig–Ore inequality.
  have hd_upper : d ≤ L.ncard - Mmax.edgeSet.ncard := by
    rw [← Nat.cast_le (α := ℕ∞), hd]
    refine iSup₂_le fun S hS ↦ ?_
    by_cases hNtop : (⋃ x ∈ S, G.neighborSet x).encard = ⊤
    · simp [hNtop]
    · have hNf : (⋃ x ∈ S, G.neighborSet x).Finite := Set.encard_ne_top_iff.1 hNtop
      have hSf : S.Finite := hL.subset hS
      have hineq := hMmax.ncard_edgeSet_add_ncard_le_of_finite hLR hS hL hNf
      rw [← hSf.cast_ncard_eq, ← hNf.cast_ncard_eq, ← ENat.natCast_sub, Nat.cast_le]
      omega
  -- Next show `L.ncard - M.edgeSet.ncard ≤ d` from the Kőnig–Ore witness `(M, S)`.
  obtain ⟨M, S, hM, hS, hNf, heq⟩ := hLR.exists_isMatching_ncard_edgeSet_add_ncard_eq_of_finite hL
  have hSf : S.Finite := hL.subset hS
  have hMle_max : M.edgeSet.ncard ≤ Mmax.edgeSet.ncard := by
    have hMf : M.edgeSet.Finite := hL.finite_of_encard_le (hLR.encard_edgeSet_le_left hM)
    have hle : M.edgeSet.encard ≤ Mmax.edgeSet.encard := hMmax_eq ▸ hM.le_matchingNum
    rwa [← hMf.cast_ncard_eq, ← hMmaxf.cast_ncard_eq, Nat.cast_le] at hle
  have hd_lower : S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard ≤ d := by
    rw [← Nat.cast_le (α := ℕ∞), ENat.natCast_sub, hSf.cast_ncard_eq, hNf.cast_ncard_eq, hd]
    exact le_iSup₂ (f := fun S (_ : S ⊆ L) ↦ S.encard - (⋃ x ∈ S, G.neighborSet x).encard) S hS
  have hMleL : Mmax.edgeSet.ncard ≤ L.ncard := by
    have hle := hLR.encard_edgeSet_le_left hMmax
    rwa [← hMmaxf.cast_ncard_eq, ← hL.cast_ncard_eq, Nat.cast_le] at hle
  rw [← hMmax_eq, ← hMmaxf.cast_ncard_eq, ← hL.cast_ncard_eq, ← hd, ← ENat.natCast_sub,
    Nat.cast_inj]
  omega

/-- **Hall's marriage theorem** for finite `L`, in `ℕ∞` form without local finiteness: there exists
a matching saturating `L` if and only if every `S ⊆ L` has `(⋃ x ∈ S, G.neighborSet x).encard` at
least `S.encard`. -/
theorem exists_isMatching_subset_verts_iff_encard (hLR : G.IsBipartiteWith L R) (hL : L.Finite) :
    (∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ S ⊆ L, S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard := by
  refine ⟨fun ⟨M, hsub, hM⟩ S hS ↦ ?_, fun hHall ↦ ?_⟩
  · have hML : M.edgeSet.encard = L.encard :=
      (hLR.subset_verts_iff_encard_edgeSet_eq hL hM).1 hsub
    have hle := hM.encard_edgeSet_add_encard_le hLR hS
    rw [hML, ENat.add_le_add_iff_left hL.encard_lt_top.ne] at hle
    exact hle
  · obtain ⟨M, S, hM, hS, hNf, heq⟩ :=
      hLR.exists_isMatching_ncard_edgeSet_add_ncard_eq_of_finite hL
    have hSf : S.Finite := hL.subset hS
    have hSle : S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
      have h := hHall S hS
      rwa [← hSf.cast_ncard_eq, ← hNf.cast_ncard_eq, Nat.cast_le] at h
    have hMle : M.edgeSet.ncard ≤ L.ncard := by
      have hMf : M.edgeSet.Finite := hL.finite_of_encard_le (hLR.encard_edgeSet_le_left hM)
      have h := hLR.encard_edgeSet_le_left hM
      rwa [← hMf.cast_ncard_eq, ← hL.cast_ncard_eq, Nat.cast_le] at h
    exact ⟨M, (hLR.subset_verts_iff_ncard_edgeSet_eq hL hM).2 (by omega), hM⟩

/-- **Hall's marriage theorem** on a finite vertex type: a matching saturating `L` exists if and
only if every `S ⊆ L` has at least `S.ncard` neighbours, with backward direction matching the finite
specialization of `SimpleGraph.exists_isMatching_of_forall_ncard_le`. -/
theorem exists_isMatching_subset_verts_iff [Finite V] (hLR : G.IsBipartiteWith L R) :
    (∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ S ⊆ L, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  rw [hLR.exists_isMatching_subset_verts_iff_encard L.toFinite]
  refine forall₂_congr fun S _ ↦ ?_
  rw [← S.toFinite.cast_ncard_eq, ← (Set.toFinite _).cast_ncard_eq, Nat.cast_le]

end IsBipartiteWith

end SimpleGraph
