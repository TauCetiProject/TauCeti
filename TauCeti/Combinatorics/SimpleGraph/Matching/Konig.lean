/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.Combinatorics.SimpleGraph.Matching.Basic

import Mathlib.Combinatorics.SimpleGraph.Hall
import TauCeti.Combinatorics.Graph.Bipartition
import TauCeti.Combinatorics.Graph.Matching.OfSimpleGraph
import TauCeti.Combinatorics.Graph.Matching.VertexCover
import TauCeti.Combinatorics.SimpleGraph.Bipartite

/-!
# Kőnig's theorem, the Kőnig–Ore deficiency formula, and Hall's theorem

This file proves Kőnig's min-max theorem and the Kőnig–Ore deficiency theorem for finite bipartite
simple graphs, together with the resulting finite Hall marriage equivalences:

* **Kőnig's theorem** (`SimpleGraph.IsBipartite.matchingNum_eq_vertexCoverNum`): in every finite
  bipartite simple graph `G`, `G.matchingNum = G.vertexCoverNum`, and there exist a matching `M`
  and a vertex cover `C` with `M.edgeSet.encard = C.encard`
  (`SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_encard_eq`) and
  `M.edgeSet.ncard = C.ncard`
  (`SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_ncard_eq`).
* **The Kőnig–Ore deficiency formula**: for any `G.IsBipartiteWith L R`, every matching `M` and
  every `S ⊆ L` satisfy `M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard`
  (`SimpleGraph.Subgraph.IsMatching.encard_edgeSet_add_encard_le`, with finite `ℕ` form
  `SimpleGraph.Subgraph.IsMatching.ncard_edgeSet_add_ncard_le`). On a finite vertex type, some
  matching `M` and `S ⊆ L` attain equality in both `ℕ∞` and `ℕ`
  (`SimpleGraph.IsBipartiteWith.exists_isMatching_encard_add_encard_eq`,
  `SimpleGraph.IsBipartiteWith.exists_isMatching_ncard_add_ncard_eq`), yielding the numerical
  deficiency formula `SimpleGraph.IsBipartiteWith.matchingNum_eq_encard_sub_iSup`.
* **Hall's marriage theorem**: Mathlib's `SimpleGraph.exists_isMatching_of_forall_ncard_le` already
  gives the sufficient Hall condition (for locally finite bipartite graphs). On a finite bipartite
  graph, this file supplies the converse and two-way equivalences in `ℕ` and `ℕ∞`
  (`SimpleGraph.IsBipartiteWith.exists_isMatching_verts_superset_iff_forall_ncard_le`, reusing
  `SimpleGraph.exists_isMatching_of_forall_ncard_le`, and
  `SimpleGraph.IsBipartiteWith.exists_isMatching_verts_superset_iff_forall_encard_le`), together
  with the equal-side perfect-matching equivalence
  (`SimpleGraph.IsBipartiteWith.exists_isPerfectMatching_iff_ncard_eq_and_forall_ncard_le`).

## Implementation notes

On a finite vertex type, Kőnig's theorem is transported from the multigraph theorem
`Graph.IsBipartition.exists_isCapacitatedMatching_sum_eq_vertexCoverNum` on `Graph.ofSimpleGraph G`
after extending a bipartition `G.IsBipartiteWith s t` to the covering bipartition
`G.IsBipartiteWith s sᶜ`.

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
    · exact Or.inr (subset_union_right <| mem_biUnion huS huv)
    · exact Or.inl (subset_union_left ⟨huL, huS⟩)
  · by_cases hvS : v ∈ S
    · exact Or.inl (subset_union_right <| mem_biUnion hvS huv.symm)
    · exact Or.inr (subset_union_left ⟨hvL, hvS⟩)

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
/-- **Kőnig's theorem.** In any finite bipartite simple graph, the matching number equals the
vertex cover number. -/
theorem IsBipartite.matchingNum_eq_vertexCoverNum [Finite V] (h : G.IsBipartite) :
    G.matchingNum = G.vertexCoverNum := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let _ : Fintype E(Graph.ofSimpleGraph G) := Fintype.ofFinite _
  obtain ⟨s, _, hst⟩ := h.exists_isBipartiteWith
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
  refine le_antisymm G.matchingNum_le_vertexCoverNum ?_
  calc
    G.vertexCoverNum
      = (Graph.ofSimpleGraph G).toSimpleGraph.vertexCoverNum :=
        (vertexCoverNum_congr (Graph.toSimpleGraphOfSimpleGraphIso G)).symm
    _ = ((∑ e, x e : ℕ) : ℕ∞) := hsum.symm
    _ = (G.matchingSubgraph (M₀ : Set E(Graph.ofSimpleGraph G))).edgeSet.encard := by
        rw [← (Set.toFinite _).cast_ncard_eq, G.ncard_edgeSet_matchingSubgraph,
          Set.ncard_coe_finset, ← hx.sum_eq_card_support]
    _ ≤ G.matchingNum := hM₀.encard_edgeSet_le_matchingNum

/-- **Kőnig's theorem with witnesses in `ℕ∞`.** Every finite bipartite simple graph has a matching
and a vertex cover of equal extended cardinality. -/
theorem IsBipartite.exists_isMatching_isVertexCover_encard_eq [Finite V] (h : G.IsBipartite) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧
      M.edgeSet.encard = C.encard := by
  obtain ⟨M, hM, hMcard⟩ := G.matchingNum_exists G.matchingNum_ne_top_of_finite
  obtain ⟨C, hCcard, hC⟩ := G.vertexCoverNum_exists
  exact ⟨M, C, hM, hC, hMcard.trans (h.matchingNum_eq_vertexCoverNum.trans hCcard.symm)⟩

/-- **Kőnig's theorem with witnesses in `ℕ`.** Every finite bipartite simple graph has a matching
and a vertex cover of equal cardinality. -/
theorem IsBipartite.exists_isMatching_isVertexCover_ncard_eq [Finite V] (h : G.IsBipartite) :
    ∃ (M : G.Subgraph) (C : Set V), M.IsMatching ∧ G.IsVertexCover C ∧
      M.edgeSet.ncard = C.ncard := by
  obtain ⟨M, C, hM, hC, heq⟩ := h.exists_isMatching_isVertexCover_encard_eq
  rw [← (Set.toFinite M.edgeSet).cast_ncard_eq, ← (Set.toFinite C).cast_ncard_eq,
    Nat.cast_inj] at heq
  exact ⟨M, C, hM, hC, heq⟩

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

/-- **The Kőnig–Ore formula in `ℕ∞`.** In a finite bipartite graph with sides `L` and `R`, there
exist a matching `M` and `S ⊆ L` with
`M.edgeSet.encard + S.encard = L.encard + (⋃ x ∈ S, G.neighborSet x).encard`. -/
theorem IsBipartiteWith.exists_isMatching_encard_add_encard_eq [Finite V]
    (hLR : G.IsBipartiteWith L R) :
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

/-- **The Kőnig–Ore formula in `ℕ`.** In a finite bipartite graph with sides `L` and `R`, there
exist a matching `M` and `S ⊆ L` with
`M.edgeSet.ncard + S.ncard = L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem IsBipartiteWith.exists_isMatching_ncard_add_ncard_eq [Finite V]
    (hLR : G.IsBipartiteWith L R) :
    ∃ (M : G.Subgraph) (S : Set V), M.IsMatching ∧ S ⊆ L ∧
      M.edgeSet.ncard + S.ncard = L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard := by
  obtain ⟨M, S, hM, hS, heq⟩ := hLR.exists_isMatching_encard_add_encard_eq
  refine ⟨M, S, hM, hS, ?_⟩
  rwa [← (Set.toFinite M.edgeSet).cast_ncard_eq, ← (Set.toFinite S).cast_ncard_eq,
    ← (Set.toFinite L).cast_ncard_eq, ← (Set.toFinite _).cast_ncard_eq,
    ← Nat.cast_add, ← Nat.cast_add, Nat.cast_inj] at heq

/-- **Numerical Kőnig–Ore deficiency formula in `ℕ∞`.** On a finite bipartite graph with sides `L`
and `R`, the matching number of `G` is `L.encard` minus the largest deficiency
`S.encard - N(S).encard` over subsets `S ⊆ L`. -/
theorem IsBipartiteWith.matchingNum_eq_encard_sub_iSup [Finite V] (hLR : G.IsBipartiteWith L R) :
    G.matchingNum =
      L.encard - ⨆ (S : Set V) (_ : S ⊆ L), (S.encard - (⋃ x ∈ S, G.neighborSet x).encard) := by
  let f (S : Set V) : ℕ∞ := S.encard - (⋃ x ∈ S, G.neighborSet x).encard
  have : Nonempty {S : Set V // S ⊆ L} := ⟨⟨∅, empty_subset L⟩⟩
  have hsup_eq : (⨆ S : {S : Set V // S ⊆ L}, f S.1) = ⨆ (S : Set V) (_ : S ⊆ L), f S :=
    iSup_subtype
  have hsup_lt : (⨆ S : {S : Set V // S ⊆ L}, f S.1) < ⊤ :=
    (iSup_le fun S ↦ tsub_le_self.trans (encard_le_encard S.2)).trans_lt
      (Set.toFinite L).encard_lt_top
  obtain ⟨⟨S₀, hS₀⟩, hS₀eq⟩ := ENat.exists_eq_iSup_of_lt_top hsup_lt
  rw [← hsup_eq, ← hS₀eq]
  refine le_antisymm (matchingNum_le_iff.2 fun M hM ↦ ?_) ?_
  · refine ENat.le_sub_of_add_le_right (hS₀eq ▸ hsup_lt.ne) ?_
    by_cases hle : S₀.encard ≤ (⋃ x ∈ S₀, G.neighborSet x).encard
    · simp only [f, tsub_eq_zero_of_le hle, add_zero, ← hM.encard_verts_inter_left hLR]
      exact encard_le_encard inter_subset_right
    · have hNlt : (⋃ x ∈ S₀, G.neighborSet x).encard < S₀.encard := not_le.1 hle
      refine (ENat.add_le_add_iff_right
        (Set.toFinite (⋃ x ∈ S₀, G.neighborSet x)).encard_lt_top.ne).1 ?_
      rw [add_assoc, tsub_add_cancel_of_le hNlt.le]
      exact hM.encard_edgeSet_add_encard_le hLR hS₀
  · obtain ⟨M, S₁, hM, hS₁, heq⟩ := hLR.exists_isMatching_encard_add_encard_eq
    have hLle : L.encard ≤ M.edgeSet.encard + f S₁ := by
      refine (ENat.add_le_add_iff_right
        (Set.toFinite (⋃ x ∈ S₁, G.neighborSet x)).encard_lt_top.ne).1 ?_
      calc
        L.encard + (⋃ x ∈ S₁, G.neighborSet x).encard
          = M.edgeSet.encard + S₁.encard := heq.symm
        _ ≤ M.edgeSet.encard + (f S₁ + (⋃ x ∈ S₁, G.neighborSet x).encard) :=
          add_le_add_right le_tsub_add _
        _ = (M.edgeSet.encard + f S₁) + (⋃ x ∈ S₁, G.neighborSet x).encard := by ac_rfl
    have hf₁ : f S₁ ≤ f S₀ := hS₀eq ▸ le_iSup (fun S : {S : Set V // S ⊆ L} ↦ f S.1) ⟨S₁, hS₁⟩
    exact (tsub_le_tsub_left hf₁ L.encard).trans
      ((tsub_le_iff_right.2 hLle).trans hM.encard_edgeSet_le_matchingNum)

/-- **Hall's marriage theorem in `ℕ` on a finite graph.** A finite bipartite graph with sides `L`
and `R` has a matching saturating `L` if and only if
`S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard` for every `S ⊆ L`. The reverse implication is the
finite specialization of `SimpleGraph.exists_isMatching_of_forall_ncard_le`. -/
theorem IsBipartiteWith.exists_isMatching_verts_superset_iff_forall_ncard_le [Finite V]
    (hLR : G.IsBipartiteWith L R) :
    (∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ S ⊆ L, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  refine ⟨fun ⟨M, hLM, hM⟩ S hS ↦
    hM.ncard_le_ncard_biUnion_neighborSet (hS.trans hLM) (Set.toFinite _), fun hHall ↦ ?_⟩
  let _ : G.LocallyFinite := fun v ↦ (Set.toFinite _).fintype
  exact exists_isMatching_of_forall_ncard_le hLR hHall

/-- **Hall's marriage theorem in `ℕ∞` on a finite graph.** A finite bipartite graph with sides `L`
and `R` has a matching saturating `L` if and only if
`S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard` for every `S ⊆ L`. -/
theorem IsBipartiteWith.exists_isMatching_verts_superset_iff_forall_encard_le [Finite V]
    (hLR : G.IsBipartiteWith L R) :
    (∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ S ⊆ L, S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard := by
  rw [hLR.exists_isMatching_verts_superset_iff_forall_ncard_le]
  refine forall₂_congr fun S _ ↦ ?_
  rw [← (Set.toFinite S).cast_ncard_eq, ← (Set.toFinite _).cast_ncard_eq, Nat.cast_le]

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
      hLR.exists_isMatching_verts_superset_iff_forall_ncard_le.1 ⟨M, hLM, hM⟩⟩
  · obtain ⟨M, hLM, hM⟩ := hLR.exists_isMatching_verts_superset_iff_forall_ncard_le.2 hHall
    have hMcard : M.edgeSet.ncard = R.ncard :=
      ((hM.verts_superset_iff_ncard_edgeSet_eq hLR (Set.toFinite L)).1 hLM).trans hcard
    have hRM : R ⊆ M.verts :=
      (hM.verts_superset_iff_ncard_edgeSet_eq hLR.symm (Set.toFinite R)).2 hMcard
    exact ⟨M, hM, Subgraph.isSpanning_iff.2 <| univ_subset_iff.1 (hcov ▸ union_subset hLM hRM)⟩

end KonigOre

end SimpleGraph
