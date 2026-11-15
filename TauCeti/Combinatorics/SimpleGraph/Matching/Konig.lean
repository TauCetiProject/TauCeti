/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.Combinatorics.SimpleGraph.Matching.Basic

import TauCeti.Combinatorics.Graph.Bipartition
import TauCeti.Combinatorics.Graph.Matching.OfSimpleGraph
import TauCeti.Combinatorics.Graph.Matching.VertexCover
import TauCeti.Combinatorics.SimpleGraph.Bipartite

/-!
# Kőnig's theorem, the Kőnig–Ore deficiency formula, and Hall's theorem

This file proves Kőnig's min-max theorem and the Kőnig–Ore deficiency theorem for bipartite simple
graphs, together with the resulting equivalences for Hall's marriage theorem:

* **Kőnig's theorem** (`SimpleGraph.IsBipartite.matchingNum_eq_vertexCoverNum`): in every bipartite
  simple graph `G`, without finiteness assumptions, `G.matchingNum = G.vertexCoverNum`, and there
  exist a matching `M` and a vertex cover `C` with `M.edgeSet.encard = C.encard`
  (`SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_encard_eq`). When
  `G.vertexCoverNum ≠ ⊤` (in particular when `V` or `G.edgeSet` is finite), `C` is finite and
  `M.edgeSet.ncard = C.ncard`
  (`SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_ncard_eq`).
* **The Kőnig–Ore deficiency formula**: for any `G.IsBipartiteWith L R`, every matching `M` and
  every `S ⊆ L` satisfy `M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard`
  (`SimpleGraph.Subgraph.IsMatching.encard_edgeSet_add_encard_le`), and some matching `M` and
  `S ⊆ L` attain equality in both `ℕ∞` and `ℕ`
  (`SimpleGraph.IsBipartiteWith.exists_isMatching_encard_add_encard_eq`,
  `SimpleGraph.IsBipartiteWith.exists_isMatching_ncard_add_ncard_eq`).
* **Hall's marriage theorem**: equivalences characterizing when a matching saturates `L` (under
  `L.Finite` in `ℕ∞`, or under `(⋃ x ∈ L, G.neighborSet x).Finite` in `ℕ`) and when a finite
  covering bipartition admits a perfect matching.

## Implementation notes

For a finite vertex type, Kőnig's theorem is transported from the multigraph theorem
`Graph.IsBipartition.exists_isCapacitatedMatching_sum_eq_vertexCoverNum` on `Graph.ofSimpleGraph G`
after extending a bipartition `G.IsBipartiteWith s t` to the covering bipartition
`G.IsBipartiteWith s sᶜ`. For an arbitrary bipartite graph with `G.matchingNum = k < ⊤`, a maximal
matching `M` has `2 * k` vertices covering every edge of `G`; keeping `M.verts` together with at
most `k + 1` external neighbours of each vertex of `M.verts` gives a finite induced subgraph whose
minimum vertex cover of size at most `k` already covers `G`.

From a matching `M` and vertex cover `C` with `M.edgeSet.encard = C.encard`, setting `S = L \ C`
places all neighbours of `S` inside `C \ L`, yielding Kőnig–Ore directly without subtraction in
`ℕ∞`.

## References

* D. Kőnig, *Gráfok és alkalmazásuk a determinánsok és a halmazok elméletére*, Mat. Természett.
  Ért. 34 (1916), 104--119.
* P. Hall, *On representatives of subsets*, J. London Math. Soc. 10 (1935), 26--30.
* Ø. Ore, *Graphs and matching theorems*, Duke Math. J. 22 (1955), 625--639.
-/

public section

open Function Set

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Bipartitions, vertex covers, and matched sides -/

section Bipartite

variable {L R : Set V}

/-- The left side of a bipartition is a vertex cover. -/
theorem IsBipartiteWith.isVertexCover_left (h : G.IsBipartiteWith L R) :
    G.IsVertexCover L :=
  fun _ _ hadj ↦ (h.mem_of_adj hadj).imp And.left And.right

/-- The right side of a bipartition is a vertex cover. -/
theorem IsBipartiteWith.isVertexCover_right (h : G.IsBipartiteWith L R) :
    G.IsVertexCover R :=
  h.symm.isVertexCover_left

/-- Removing any set `S` from the left side `L` of a bipartition and adjoining the neighbours of
`S` yields a vertex cover of `G`. -/
theorem IsBipartiteWith.isVertexCover_sdiff_union_biUnion_neighborSet
    (h : G.IsBipartiteWith L R) (S : Set V) :
    G.IsVertexCover ((L \ S) ∪ ⋃ x ∈ S, G.neighborSet x) := by
  intro u v huv
  rcases h.mem_of_adj huv with ⟨huL, -⟩ | ⟨-, hvL⟩
  · by_cases huS : u ∈ S
    · exact Or.inr ( subset_union_right <| mem_biUnion huS huv )
    · exact Or.inl ( subset_union_left ⟨huL, huS⟩ )
  · by_cases hvS : v ∈ S
    · exact Or.inl ( subset_union_right <| mem_biUnion hvS huv.symm )
    · exact Or.inr ( subset_union_left ⟨hvL, hvS⟩ )

/-- In a bipartite graph with sides `L` and `R`, sending each matched vertex in `L` to its incident
matching edge is a bijection `(M.verts ∩ L : Set V) ≃ M.edgeSet`. -/
private noncomputable def vertsInterLeftEquivEdgeSet {M : G.Subgraph}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) :
    ↑(M.verts ∩ L) ≃ M.edgeSet := by
  refine Equiv.ofBijective (fun x ↦ hM.toEdge ⟨x.1, x.2.1⟩) ⟨fun x₁ x₂ hx ↦ ?_, fun e ↦ ?_⟩
  · have hm₂ : x₂.1 ∈ (hM.toEdge ⟨x₁.1, x₁.2.1⟩ : Sym2 V) := by
      simpa [← hx] using hM.mem_coe_toEdge x₂.2.1
    obtain ⟨w, hw, -⟩ := hM x₁.2.1
    have heq : (hM.toEdge ⟨x₁.1, x₁.2.1⟩ : Sym2 V) = s(x₁.1, w) :=
      congrArg Subtype.val (hM.toEdge_eq_of_adj hw)
    rw [heq, Sym2.mem_iff] at hm₂
    rcases hm₂ with h₁₂ | h₂w
    · exact Subtype.ext h₁₂.symm
    · subst h₂w
      exact False.elim <| hLR.disjoint.ne_of_mem x₂.2.2
        (hLR.mem_of_mem_adj x₁.2.2 (M.adj_sub hw)) rfl
  · have hout : M.Adj e.1.out.1 e.1.out.2 := by
      have he := e.2
      rwa [← Sym2.mk_fst_out_snd_out e.1, Subgraph.mem_edgeSet] at he
    have hfst : hM.toEdge ⟨e.1.out.1, hout.fst_mem⟩ = e :=
      Subtype.ext <| (congrArg Subtype.val (hM.toEdge_eq_of_adj hout)).trans
        (Sym2.mk_fst_out_snd_out e.1)
    rcases hLR.mem_of_adj (M.adj_sub hout) with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact ⟨⟨e.1.out.1, hout.fst_mem, h₁⟩, hfst⟩
    · exact ⟨⟨e.1.out.2, hout.snd_mem, h₂⟩,
        (hM.toEdge_eq_toEdge_of_adj hout).symm.trans hfst⟩

/-- In a bipartite graph with sides `L` and `R`, the number of matched vertices in `L` equals the
number of edges of the matching in `ℕ∞`. -/
theorem Subgraph.IsMatching.encard_verts_inter_left {M : G.Subgraph}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) :
    (M.verts ∩ L).encard = M.edgeSet.encard :=
  ENat.card_congr (vertsInterLeftEquivEdgeSet hM hLR)

/-- In a bipartite graph with sides `L` and `R`, the number of matched vertices in `L` equals the
number of edges of the matching in `ℕ`. -/
theorem Subgraph.IsMatching.ncard_verts_inter_left {M : G.Subgraph}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) :
    (M.verts ∩ L).ncard = M.edgeSet.ncard := by
  simpa only [Nat.card_coe_set_eq] using Nat.card_congr (vertsInterLeftEquivEdgeSet hM hLR)

/-- When the left side `L` is finite, a matching saturates `L` if and only if its edge set has
extended cardinality `L.encard`. -/
theorem Subgraph.IsMatching.verts_superset_iff_encard_edgeSet_eq {M : G.Subgraph}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) (hL : L.Finite) :
    L ⊆ M.verts ↔ M.edgeSet.encard = L.encard := by
  rw [← hM.encard_verts_inter_left hLR]
  exact ⟨fun h ↦ by rw [inter_eq_right.2 h], fun h ↦
    (hL.subset inter_subset_right).eq_of_subset_of_encard_le inter_subset_right h.ge ▸
      inter_subset_left⟩

/-- When the left side `L` is finite, a matching saturates `L` if and only if its edge set has
natural cardinality `L.ncard`. -/
theorem Subgraph.IsMatching.verts_superset_iff_ncard_edgeSet_eq {M : G.Subgraph}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) (hL : L.Finite) :
    L ⊆ M.verts ↔ M.edgeSet.ncard = L.ncard := by
  rw [← hM.ncard_verts_inter_left hLR]
  exact ⟨fun h ↦ by rw [inter_eq_right.2 h],
    fun h ↦ eq_of_subset_of_ncard_le inter_subset_right h.ge hL ▸ inter_subset_left⟩

end Bipartite

/-! ### Kőnig's theorem -/

open scoped Graph in
/-- Finite-carrier Kőnig witness theorem, transported from
`Graph.IsBipartition.exists_isCapacitatedMatching_sum_eq_vertexCoverNum` on `Graph.ofSimpleGraph G`.
Used as the finite kernel step for `SimpleGraph.IsBipartite.matchingNum_eq_vertexCoverNum`. -/
private theorem exists_isMatching_isVertexCover_ncard_eq_of_finite [Finite V] (h : G.IsBipartite) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧ C.Finite ∧
      M.edgeSet.ncard = C.ncard := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let _ : Fintype E(Graph.ofSimpleGraph G) := Fintype.ofFinite _
  obtain ⟨s, t, hst⟩ := h.exists_isBipartiteWith
  let L : Finset V(Graph.ofSimpleGraph G) := Finset.univ.filter fun x ↦ x.1 ∈ s
  let R : Finset V(Graph.ofSimpleGraph G) := Finset.univ.filter fun x ↦ x.1 ∈ sᶜ
  have hLimg : Subtype.val '' (L : Set V(Graph.ofSimpleGraph G)) = s := by
    ext v; simp [L]
  have hRimg : Subtype.val '' (R : Set V(Graph.ofSimpleGraph G)) = sᶜ := by
    ext v; simp [R]
  have hLR : (Graph.ofSimpleGraph G).IsBipartition L R :=
    (G.isBipartition_ofSimpleGraph_iff L R).2 ⟨hLimg ▸ hRimg ▸ hst.compl_right, by
      rw [hLimg, hRimg, union_compl_self]⟩
  obtain ⟨x, hx, hsum⟩ := hLR.exists_isCapacitatedMatching_sum_eq_vertexCoverNum
  let M₀ : Finset E(Graph.ofSimpleGraph G) := Finset.univ.filter fun e ↦ x e ≠ 0
  have hM₀ : (G.matchingSubgraph (M₀ : Set E(Graph.ofSimpleGraph G))).IsMatching :=
    (G.matchingSubgraph_isMatching_iff _).2 (hx.supportFinset_isMatching hLR.loopless)
  obtain ⟨C, hCnum, hCcov⟩ := G.vertexCoverNum_exists
  have hMfin : (G.matchingSubgraph (M₀ : Set E(Graph.ofSimpleGraph G))).edgeSet.Finite :=
    Set.toFinite _
  have hCfin : C.Finite := Set.toFinite _
  refine ⟨G.matchingSubgraph (M₀ : Set E(Graph.ofSimpleGraph G)), C, hM₀, hCcov, hCfin, ?_⟩
  apply Nat.cast_injective (R := ℕ∞)
  rw [hMfin.cast_ncard_eq, hCfin.cast_ncard_eq, hCnum, ← hMfin.cast_ncard_eq,
    G.ncard_edgeSet_matchingSubgraph, Set.ncard_coe_finset, ← hx.sum_eq_card_support, hsum,
    vertexCoverNum_congr (Graph.toSimpleGraphOfSimpleGraphIso G)]

/-- Choose either all external neighbours of `x` outside `A` when there are at most `k`, or a
`(k + 1)`-element subset when there are more. -/
private theorem exists_finite_subset_neighborSet_sdiff (G : SimpleGraph V) (A : Set V)
    (k : ℕ) (x : V) :
    ∃ U ⊆ G.neighborSet x \ A, U.Finite ∧ (U = G.neighborSet x \ A ∨ U.encard = k + 1) := by
  by_cases hle : (G.neighborSet x \ A).encard ≤ k
  · exact ⟨G.neighborSet x \ A, Subset.rfl,
      encard_lt_top_iff.1 (hle.trans_lt (ENat.natCast_lt_top k)), Or.inl rfl⟩
  · have hk1 : ((k + 1 : ℕ) : ℕ∞) ≤ (G.neighborSet x \ A).encard :=
      Order.add_one_le_of_lt (not_le.1 hle)
    obtain ⟨U, hUsub, hUcard⟩ := exists_subset_encard_eq hk1
    exact ⟨U, hUsub, encard_lt_top_iff.1 (hUcard ▸ ENat.natCast_lt_top (k + 1)),
      Or.inr (by simpa using hUcard)⟩

/-- If `A` covers all edges of `G` and `U x` records either all of `G.neighborSet x \ A` or `k + 1`
elements of it, then any vertex cover `C₀` of `G.induce (A ∪ ⋃ x ∈ A, U x)` of size at most `k`
already covers every edge of `G`. -/
private theorem isVertexCover_image_of_induce_kernel {A : Set V} {U : V → Set V} {k : ℕ}
    (hAcov : G.IsVertexCover A)
    (hUsub : ∀ x, U x ⊆ G.neighborSet x \ A)
    (hUcases : ∀ x, U x = G.neighborSet x \ A ∨ (U x).encard = k + 1)
    {C₀ : Set (A ∪ ⋃ x ∈ A, U x : Set V)}
    (hC₀cov : (G.induce (A ∪ ⋃ x ∈ A, U x)).IsVertexCover C₀)
    (hCcard : (Subtype.val '' C₀).encard ≤ k) :
    G.IsVertexCover (Subtype.val '' C₀) := by
  let S : Set V := A ∪ ⋃ x ∈ A, U x
  intro u v huv
  wlog hu : u ∈ A generalizing u v
  · exact (this huv.symm ((hAcov huv).resolve_left hu)).symm
  have huS : u ∈ S := subset_union_left hu
  by_cases hvS : v ∈ S
  · exact (@hC₀cov ⟨u, huS⟩ ⟨v, hvS⟩ huv).imp
      (fun h ↦ ⟨⟨u, huS⟩, h, rfl⟩) (fun h ↦ ⟨⟨v, hvS⟩, h, rfl⟩)
  · refine Or.inl ?_
    by_contra huC
    have hvA : v ∉ A := fun hv ↦ hvS (subset_union_left hv)
    have hvU : v ∉ U u := fun hv ↦ hvS (subset_union_right (mem_biUnion hu hv))
    have hUeq : (U u).encard = k + 1 :=
      (hUcases u).resolve_left fun hEq ↦ hvU (hEq ▸ ⟨huv, hvA⟩)
    have hUsubC : U u ⊆ Subtype.val '' C₀ := fun w hw ↦ by
      have hwS : w ∈ S := subset_union_right (mem_biUnion hu hw)
      have hadj : (G.induce S).Adj ⟨u, huS⟩ ⟨w, hwS⟩ := (hUsub u hw).1
      exact ⟨⟨w, hwS⟩, (hC₀cov hadj).resolve_left (fun h ↦ huC ⟨⟨u, huS⟩, h, rfl⟩), rfl⟩
    exact ((hUeq ▸ encard_le_encard hUsubC).trans hCcard).not_gt
      (Nat.cast_lt.2 (Nat.lt_succ_self k))

/-- **Kőnig's theorem.** In any bipartite simple graph, without finiteness assumptions, the
matching number equals the vertex cover number. -/
theorem IsBipartite.matchingNum_eq_vertexCoverNum (h : G.IsBipartite) :
    G.matchingNum = G.vertexCoverNum := by
  refine le_antisymm G.matchingNum_le_vertexCoverNum ?_
  rcases eq_or_ne G.matchingNum ⊤ with htop | hfin
  · simp [htop]
  · set k : ℕ := G.matchingNum.toNat
    have hk : (k : ℕ∞) = G.matchingNum := ENat.natCast_toNat hfin
    obtain ⟨M, hM, hMcard⟩ := G.matchingNum_exists
    have hMcov : G.IsVertexCover M.verts :=
      (Subgraph.maximal_isMatching_iff.1
        (hM.maximal_of_encard_edgeSet_eq_matchingNum hfin hMcard)).2
    have hMfin : M.verts.Finite := by
      rw [← encard_lt_top_iff, hM.encard_verts, hMcard, ← hk]
      exact ENat.natCast_lt_top (2 * k)
    choose U hUsub hUfin hUcases using exists_finite_subset_neighborSet_sdiff G M.verts k
    let S : Set V := M.verts ∪ ⋃ x ∈ M.verts, U x
    have hSfin : S.Finite := hMfin.union (hMfin.biUnion fun x _ ↦ hUfin x)
    let _ : Finite S := hSfin.to_subtype
    let f : G.induce S ↪g G := Embedding.induce S
    have hHbip : (G.induce S).IsBipartite := let ⟨c⟩ := h; ⟨c.comp f.toHom⟩
    have hHle : (G.induce S).matchingNum ≤ k :=
      (IsContained.matchingNum_le_matchingNum ⟨f.toHom, f.injective⟩).trans_eq hk.symm
    obtain ⟨M₀, C₀, hM₀, hC₀cov, hC₀fin, hMC₀⟩ :=
      exists_isMatching_isVertexCover_ncard_eq_of_finite hHbip
    have hC₀le : C₀.encard ≤ k := by
      rw [← hC₀fin.cast_ncard_eq, ← hMC₀]
      exact hM₀.ncard_edgeSet_le_matchingNum.trans hHle
    have hCcard : (Subtype.val '' C₀).encard ≤ k :=
      (Function.Injective.encard_image Subtype.val_injective C₀).trans_le hC₀le
    exact (isVertexCover_image_of_induce_kernel hMcov hUsub hUcases hC₀cov hCcard).vertexCoverNum_le
      |>.trans (hCcard.trans_eq hk)

/-- **Kőnig's theorem with witnesses in `ℕ∞`.** Every bipartite simple graph has a matching and a
vertex cover of equal extended cardinality. -/
theorem IsBipartite.exists_isMatching_isVertexCover_encard_eq (h : G.IsBipartite) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧
      M.edgeSet.encard = C.encard := by
  obtain ⟨M, hM, hMcard⟩ := G.matchingNum_exists
  obtain ⟨C, hCcard, hC⟩ := G.vertexCoverNum_exists
  exact ⟨M, C, hM, hC, hMcard.trans (h.matchingNum_eq_vertexCoverNum.trans hCcard.symm)⟩

/-- **Kőnig's theorem with finite witnesses in `ℕ`.** Every bipartite simple graph with finite
vertex cover number (in particular, when `V` or `G.edgeSet` is finite) has a matching and a finite
vertex cover of equal cardinality. -/
theorem IsBipartite.exists_isMatching_isVertexCover_ncard_eq (h : G.IsBipartite)
    (hfin : G.vertexCoverNum ≠ ⊤) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧ C.Finite ∧
      M.edgeSet.ncard = C.ncard := by
  obtain ⟨M, hM, hMcard⟩ := G.matchingNum_exists
  obtain ⟨C, hCcard, hC⟩ := G.vertexCoverNum_exists
  have hCfin : C.Finite := encard_ne_top_iff.1 (hCcard.trans_ne hfin)
  have heq : M.edgeSet.encard = C.encard :=
    hMcard.trans (h.matchingNum_eq_vertexCoverNum.trans hCcard.symm)
  have hMfin : M.edgeSet.Finite := encard_ne_top_iff.1 (heq.trans hCcard |>.trans_ne hfin)
  rw [← hMfin.cast_ncard_eq, ← hCfin.cast_ncard_eq, Nat.cast_inj] at heq
  exact ⟨M, C, hM, hC, hCfin, heq⟩

/-! ### The Kőnig–Ore deficiency formula and Hall's theorem -/

section KonigOre

variable {L R S : Set V}

/-- **The Kőnig–Ore inequality in `ℕ∞`.** In a bipartite graph with sides `L` and `R`, every
matching `M` and every `S ⊆ L` satisfy
`M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard`. -/
theorem Subgraph.IsMatching.encard_edgeSet_add_encard_le {M : G.Subgraph}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) (hS : S ⊆ L) :
    M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
  have hcov := hLR.isVertexCover_sdiff_union_biUnion_neighborSet S
  have hle := (hM.encard_edgeSet_le_encard_of_isVertexCover hcov).trans (encard_union_le _ _)
  calc
    M.edgeSet.encard + S.encard
      ≤ ((L \ S).encard + (⋃ x ∈ S, G.neighborSet x).encard) + S.encard :=
        add_le_add_left hle S.encard
    _ = ((L \ S).encard + S.encard) + (⋃ x ∈ S, G.neighborSet x).encard := by ac_rfl
    _ = L.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
        rw [← encard_union_eq disjoint_sdiff_left, sdiff_union_of_subset hS]

/-- **The Kőnig–Ore inequality in `ℕ`.** When `L` and the neighbourhood of `S ⊆ L` are finite,
every matching `M` satisfies
`M.edgeSet.ncard + S.ncard ≤ L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem Subgraph.IsMatching.ncard_edgeSet_add_ncard_le {M : G.Subgraph}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) (hS : S ⊆ L)
    (hL : L.Finite) (hN : (⋃ x ∈ S, G.neighborSet x).Finite) :
    M.edgeSet.ncard + S.ncard ≤ L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard := by
  have hSfin : S.Finite := hL.subset hS
  have hMfin : M.edgeSet.Finite :=
    encard_lt_top_iff.1 <| (hM.encard_verts_inter_left hLR).symm.trans_lt
      (hL.subset inter_subset_right).encard_lt_top
  have hle := hM.encard_edgeSet_add_encard_le hLR hS
  rwa [← hMfin.cast_ncard_eq, ← hSfin.cast_ncard_eq, ← hL.cast_ncard_eq, ← hN.cast_ncard_eq,
    ← Nat.cast_add, ← Nat.cast_add, Nat.cast_le] at hle

/-- **The Kőnig–Ore formula in `ℕ∞`.** In a bipartite graph with sides `L` and `R`, there exist a
matching `M` and `S ⊆ L` with
`M.edgeSet.encard + S.encard = L.encard + (⋃ x ∈ S, G.neighborSet x).encard`. -/
theorem IsBipartiteWith.exists_isMatching_encard_add_encard_eq (hLR : G.IsBipartiteWith L R) :
    ∃ (M : G.Subgraph) (S : Set V), M.IsMatching ∧ S ⊆ L ∧
      M.edgeSet.encard + S.encard = L.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
  obtain ⟨M, C, hM, hC, heq⟩ := hLR.isBipartite.exists_isMatching_isVertexCover_encard_eq
  refine ⟨M, L \ C, hM, sdiff_subset,
    le_antisymm (hM.encard_edgeSet_add_encard_le hLR sdiff_subset) ?_⟩
  have hNsub := hC.biUnion_neighborSet_sdiff_subset L
  have hdisj : Disjoint (L ∩ C) (⋃ x ∈ L \ C, G.neighborSet x) :=
    hLR.disjoint.mono inter_subset_left
      (iUnion₂_subset fun x hx ↦ isBipartiteWith_neighborSet_subset hLR hx.1)
  have hCle : (L ∩ C).encard + (⋃ x ∈ L \ C, G.neighborSet x).encard ≤ M.edgeSet.encard := by
    rw [heq, ← encard_union_eq hdisj]
    exact encard_le_encard (union_subset inter_subset_right hNsub)
  calc
    L.encard + (⋃ x ∈ L \ C, G.neighborSet x).encard
      = ((L ∩ C).encard + (L \ C).encard) + (⋃ x ∈ L \ C, G.neighborSet x).encard := by
        rw [← encard_union_eq (disjoint_of_subset_left inter_subset_right disjoint_sdiff_right),
          inter_union_sdiff]
    _ = ((L ∩ C).encard + (⋃ x ∈ L \ C, G.neighborSet x).encard) + (L \ C).encard := by ac_rfl
    _ ≤ M.edgeSet.encard + (L \ C).encard := add_le_add_left hCle _

/-- **The Kőnig–Ore formula in `ℕ`.** In a bipartite graph with sides `L` and `R`, there exist a
matching `M` and `S ⊆ L` with
`M.edgeSet.ncard + S.ncard = L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem IsBipartiteWith.exists_isMatching_ncard_add_ncard_eq (hLR : G.IsBipartiteWith L R) :
    ∃ (M : G.Subgraph) (S : Set V), M.IsMatching ∧ S ⊆ L ∧
      M.edgeSet.ncard + S.ncard = L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard := by
  obtain hL | hL := L.finite_or_infinite
  · have hvc : G.vertexCoverNum ≠ ⊤ :=
      ne_top_of_le_ne_top hL.encard_lt_top.ne hLR.isVertexCover_left.vertexCoverNum_le
    obtain ⟨M, C, hM, hC, hCfin, hMC⟩ :=
      hLR.isBipartite.exists_isMatching_isVertexCover_ncard_eq hvc
    have hSfin : (L \ C).Finite := hL.subset sdiff_subset
    have hNsub := hC.biUnion_neighborSet_sdiff_subset L
    have hNfin : (⋃ x ∈ L \ C, G.neighborSet x).Finite := hCfin.subset hNsub
    refine ⟨M, L \ C, hM, sdiff_subset,
      le_antisymm (hM.ncard_edgeSet_add_ncard_le hLR sdiff_subset hL hNfin) ?_⟩
    have hdisj : Disjoint (L ∩ C) (⋃ x ∈ L \ C, G.neighborSet x) :=
      hLR.disjoint.mono inter_subset_left
        (iUnion₂_subset fun x hx ↦ isBipartiteWith_neighborSet_subset hLR hx.1)
    have hCle : (L ∩ C).ncard + (⋃ x ∈ L \ C, G.neighborSet x).ncard ≤ M.edgeSet.ncard := by
      rw [hMC, ← ncard_union_eq hdisj (hL.subset inter_subset_left) hNfin]
      exact ncard_le_ncard (union_subset inter_subset_right hNsub) hCfin
    have hLsplit : (L ∩ C).ncard + (L \ C).ncard = L.ncard := by
      rw [← ncard_union_eq (disjoint_of_subset_left inter_subset_right disjoint_sdiff_right)
        (hL.subset inter_subset_left) hSfin, inter_union_sdiff]
    omega
  · exact ⟨⊥, ∅, Subgraph.isMatching_bot, empty_subset _, by simp [hL.ncard]⟩

/-- **Numerical Kőnig–Ore deficiency formula in `ℕ∞`.** When the left side `L` is finite, the
matching number of `G` is `L.encard` minus the largest deficiency `S.encard - N(S).encard` over
subsets `S ⊆ L`. -/
theorem IsBipartiteWith.matchingNum_eq_encard_sub_iSup (hLR : G.IsBipartiteWith L R)
    (hL : L.Finite) :
    G.matchingNum =
      L.encard - ⨆ (S : Set V) (_ : S ⊆ L), (S.encard - (⋃ x ∈ S, G.neighborSet x).encard) := by
  let f (S : Set V) : ℕ∞ := S.encard - (⋃ x ∈ S, G.neighborSet x).encard
  have : Nonempty {S : Set V // S ⊆ L} := ⟨⟨∅, empty_subset L⟩⟩
  have hsup_eq : (⨆ S : {S : Set V // S ⊆ L}, f S.1) = ⨆ (S : Set V) (_ : S ⊆ L), f S :=
    iSup_subtype
  have hsup_lt : (⨆ S : {S : Set V // S ⊆ L}, f S.1) < ⊤ :=
    (iSup_le fun S ↦ tsub_le_self.trans (encard_le_encard S.2)).trans_lt hL.encard_lt_top
  obtain ⟨⟨S₀, hS₀⟩, hS₀eq⟩ := ENat.exists_eq_iSup_of_lt_top hsup_lt
  rw [← hsup_eq, ← hS₀eq]
  refine le_antisymm (matchingNum_le_iff.2 fun M hM ↦ ?_) ?_
  · refine ENat.le_sub_of_add_le_right (hS₀eq ▸ hsup_lt.ne) ?_
    by_cases hle : S₀.encard ≤ (⋃ x ∈ S₀, G.neighborSet x).encard
    · simp only [f, tsub_eq_zero_of_le hle, add_zero, ← hM.encard_verts_inter_left hLR]
      exact encard_le_encard inter_subset_right
    · have hNlt : (⋃ x ∈ S₀, G.neighborSet x).encard < S₀.encard := not_le.1 hle
      have hNne : (⋃ x ∈ S₀, G.neighborSet x).encard ≠ ⊤ :=
        (lt_trans (lt_of_lt_of_le hNlt (encard_le_encard hS₀)) hL.encard_lt_top).ne
      refine (ENat.add_le_add_iff_right hNne).1 ?_
      rw [add_assoc, tsub_add_cancel_of_le hNlt.le]
      exact hM.encard_edgeSet_add_encard_le hLR hS₀
  · obtain ⟨M, S₁, hM, hS₁, heq⟩ := hLR.exists_isMatching_encard_add_encard_eq
    have hMle : M.edgeSet.encard ≤ L.encard :=
      (hM.encard_verts_inter_left hLR).symm.trans_le (encard_le_encard inter_subset_right)
    have hSle : S₁.encard ≤ L.encard := encard_le_encard hS₁
    have hNlt : (⋃ x ∈ S₁, G.neighborSet x).encard < ⊤ := by
      have hsum : L.encard + (⋃ x ∈ S₁, G.neighborSet x).encard < ⊤ :=
        heq ▸ WithTop.add_lt_top.2 ⟨hMle.trans_lt hL.encard_lt_top, hSle.trans_lt hL.encard_lt_top⟩
      exact le_add_self.trans_lt hsum
    have hLle : L.encard ≤ M.edgeSet.encard + f S₁ := by
      refine (ENat.add_le_add_iff_right hNlt.ne).1 ?_
      calc
        L.encard + (⋃ x ∈ S₁, G.neighborSet x).encard
          = M.edgeSet.encard + S₁.encard := heq.symm
        _ ≤ M.edgeSet.encard + (f S₁ + (⋃ x ∈ S₁, G.neighborSet x).encard) :=
          add_le_add_right le_tsub_add _
        _ = (M.edgeSet.encard + f S₁) + (⋃ x ∈ S₁, G.neighborSet x).encard := by ac_rfl
    have hf₁ : f S₁ ≤ f S₀ := hS₀eq ▸ le_iSup (fun S : {S : Set V // S ⊆ L} ↦ f S.1) ⟨S₁, hS₁⟩
    exact (tsub_le_tsub_left hf₁ L.encard).trans
      ((tsub_le_iff_right.2 hLle).trans hM.encard_edgeSet_le_matchingNum)

/-- **Hall's marriage theorem in `ℕ∞`.** When the left side `L` is finite, `G` has a matching
saturating `L` if and only if `S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard` for every `S ⊆ L`. -/
theorem IsBipartiteWith.exists_isMatching_verts_superset_iff_forall_encard_le
    (hLR : G.IsBipartiteWith L R) (hL : L.Finite) :
    (∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ S ⊆ L, S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard := by
  refine ⟨fun ⟨M, hLM, hM⟩ _ hS ↦ hM.encard_le_encard_biUnion_neighborSet (hS.trans hLM),
    fun hHall ↦ ?_⟩
  obtain ⟨M, hM, hMcard⟩ := G.matchingNum_exists
  have hsup : (⨆ (S : Set V) (_ : S ⊆ L), (S.encard - (⋃ x ∈ S, G.neighborSet x).encard)) = 0 := by
    simpa [tsub_eq_zero_iff_le] using hHall
  refine ⟨M, (hM.verts_superset_iff_encard_edgeSet_eq hLR hL).2 ?_, hM⟩
  rw [hMcard, hLR.matchingNum_eq_encard_sub_iSup hL, hsup, tsub_zero]

/-- **Hall's marriage theorem in `ℕ`.** When the neighbourhood of `L` is finite, `G` has a matching
saturating `L` if and only if `S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard` for every `S ⊆ L`. -/
theorem IsBipartiteWith.exists_isMatching_verts_superset_iff_forall_ncard_le
    (hLR : G.IsBipartiteWith L R) (hN : (⋃ x ∈ L, G.neighborSet x).Finite) :
    (∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ S ⊆ L, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  refine ⟨fun ⟨M, hLM, hM⟩ S hS ↦ hM.ncard_le_ncard_biUnion_neighborSet (hS.trans hLM)
    (hN.subset (biUnion_mono hS fun _ _ ↦ Subset.rfl)), fun hHall ↦ ?_⟩
  have hL : L.Finite := by
    by_contra hLinf
    obtain ⟨S, hSL, -, hScard⟩ :=
      Set.Infinite.exists_subset_ncard_eq hLinf ((⋃ x ∈ L, G.neighborSet x).ncard + 1)
    have hNSle : (⋃ x ∈ S, G.neighborSet x).ncard ≤ (⋃ x ∈ L, G.neighborSet x).ncard :=
      ncard_le_ncard (biUnion_mono hSL fun _ _ ↦ Subset.rfl) hN
    exact absurd ((hScard ▸ hHall S hSL).trans hNSle) (Nat.not_succ_le_self _)
  refine (hLR.exists_isMatching_verts_superset_iff_forall_encard_le hL).2 fun S hS ↦ ?_
  have hSfin : S.Finite := hL.subset hS
  have hNSfin : (⋃ x ∈ S, G.neighborSet x).Finite :=
    hN.subset (biUnion_mono hS fun _ _ ↦ Subset.rfl)
  rw [← hSfin.cast_ncard_eq, ← hNSfin.cast_ncard_eq, Nat.cast_le]
  exact hHall S hS

/-- **Hall's marriage theorem for perfect matchings.** On a finite graph with covering bipartition
`L ∪ R = Set.univ`, `G` has a perfect matching if and only if `L.ncard = R.ncard` and every
`S ⊆ L` satisfies `S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem IsBipartiteWith.exists_isPerfectMatching_iff_ncard_eq_and_forall_ncard_le [Finite V]
    (hLR : G.IsBipartiteWith L R) (hcov : L ∪ R = Set.univ) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      L.ncard = R.ncard ∧ ∀ S ⊆ L, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  refine ⟨fun ⟨M, hM, hspan⟩ ↦ ?_, fun ⟨hcard, hHall⟩ ↦ ?_⟩
  · have hLM : L ⊆ M.verts := fun x _ ↦ hspan x
    have hRM : R ⊆ M.verts := fun x _ ↦ hspan x
    have hLcard := (hM.verts_superset_iff_ncard_edgeSet_eq hLR (Set.toFinite L)).1 hLM
    have hRcard := (hM.verts_superset_iff_ncard_edgeSet_eq hLR.symm (Set.toFinite R)).1 hRM
    exact ⟨hLcard.symm.trans hRcard,
      (hLR.exists_isMatching_verts_superset_iff_forall_ncard_le (Set.toFinite _)).1 ⟨M, hLM, hM⟩⟩
  · obtain ⟨M, hLM, hM⟩ :=
      (hLR.exists_isMatching_verts_superset_iff_forall_ncard_le (Set.toFinite _)).2 hHall
    have hMcard : M.edgeSet.ncard = R.ncard :=
      ((hM.verts_superset_iff_ncard_edgeSet_eq hLR (Set.toFinite L)).1 hLM).trans hcard
    have hRM : R ⊆ M.verts :=
      (hM.verts_superset_iff_ncard_edgeSet_eq hLR.symm (Set.toFinite R)).2 hMcard
    exact ⟨M, hM, Subgraph.isSpanning_iff.2 <| univ_subset_iff.1 (hcov ▸ union_subset hLM hRM)⟩

end KonigOre

end SimpleGraph
