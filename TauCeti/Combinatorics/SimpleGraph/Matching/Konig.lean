/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Matching.Basic
public import TauCeti.Combinatorics.SimpleGraph.VertexCover

import Mathlib.Combinatorics.SimpleGraph.Hall
import TauCeti.Combinatorics.Graph.Bipartition
import TauCeti.Combinatorics.Graph.Matching.OfSimpleGraph
import TauCeti.Combinatorics.Graph.Matching.VertexCover
import TauCeti.Combinatorics.SimpleGraph.Bipartite

/-!
# Kőnig's theorem, the Kőnig–Ore deficiency formula, and Hall's theorem

This file proves Kőnig's min-max theorem and the Kőnig–Ore deficiency theorem for finite bipartite
simple graphs, together with the resulting Hall marriage equivalences:

* **Kőnig's theorem** (`SimpleGraph.IsBipartite.matchingNum_eq_vertexCoverNum`): in every finite
  bipartite simple graph `G`, `G.matchingNum = G.vertexCoverNum`, and there exist a (maximum)
  matching `M` and a (minimum) vertex cover `C` with `M.edgeSet.encard = C.encard`
  (`SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_encard_eq`,
  `SimpleGraph.IsBipartite.exists_isMaximumMatching_isMinimumVertexCover_encard_eq`) and
  `M.edgeSet.ncard = C.ncard`
  (`SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_ncard_eq`,
  `SimpleGraph.IsBipartite.exists_isMaximumMatching_isMinimumVertexCover_ncard_eq`).
  Every maximum matching has the same number of edges as every minimum vertex cover has vertices
  (`SimpleGraph.IsBipartite.encard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover`), and
  being maximum/minimum is characterized by the existence of a dual witness of the same size
  (`SimpleGraph.IsBipartite.isMaximumMatching_iff_exists_isVertexCover_encard_eq`,
  `SimpleGraph.IsBipartite.isMinimumVertexCover_iff_exists_isMatching_encard_eq`).
* **The Kőnig–Ore deficiency formula**: for any `G.IsBipartiteWith L R`, every matching `M` and
  every `S ⊆ L` satisfy `M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard`
  (`SimpleGraph.Subgraph.IsMatching.encard_edgeSet_add_encard_le`, with finite `ℕ` form
  `SimpleGraph.Subgraph.IsMatching.ncard_edgeSet_add_ncard_le`). On a finite vertex type, some
  matching `M` and `S ⊆ L` attain equality in both `ℕ∞` and `ℕ`
  (`SimpleGraph.IsBipartiteWith.exists_isMatching_encard_add_encard_eq`,
  `SimpleGraph.IsBipartiteWith.exists_isMatching_ncard_add_ncard_eq`), yielding the numerical
  deficiency formula `SimpleGraph.IsBipartiteWith.matchingNum_eq_encard_sub_iSup`.
* **Hall's marriage theorem**: Mathlib's `SimpleGraph.exists_isMatching_of_forall_ncard_le` already
  gives the sufficient Hall condition for locally finite bipartite graphs. This file supplies the
  converse and two-way side-saturating equivalences in `ℕ` and `ℕ∞` under `[G.LocallyFinite]`
  (`SimpleGraph.IsBipartiteWith.exists_isMatching_verts_superset_iff_forall_ncard_le`, reusing
  `SimpleGraph.exists_isMatching_of_forall_ncard_le`, and
  `SimpleGraph.IsBipartiteWith.exists_isMatching_verts_superset_iff_forall_encard_le`), together
  with the finite equal-side perfect-matching equivalence
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

open Set

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

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
  let L : Finset V(Graph.ofSimpleGraph G) := Finset.univ.filter fun x ↦ x.val ∈ s
  let R : Finset V(Graph.ofSimpleGraph G) := Finset.univ.filter fun x ↦ x.val ∈ sᶜ
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

section Extremal

variable {M : G.Subgraph} {c : Set V}

/-- **Kőnig's theorem** (extremal witness form in `ℕ∞`). A finite bipartite simple graph admits a
maximum matching and a minimum vertex cover of the same cardinality. -/
theorem IsBipartite.exists_isMaximumMatching_isMinimumVertexCover_encard_eq [Finite V]
    (h : G.IsBipartite) :
    ∃ (M : G.Subgraph) (c : Set V), M.IsMaximumMatching ∧ G.IsMinimumVertexCover c ∧
      M.edgeSet.encard = c.encard := by
  obtain ⟨M, c, hM, hc, hcard⟩ := h.exists_isMatching_isVertexCover_encard_eq
  exact ⟨M, c, hM.isMaximumMatching_of_encard_edgeSet_eq hc hcard,
    hc.isMinimumVertexCover_of_encard_eq hM hcard, hcard⟩

/-- **Kőnig's theorem** (extremal witness form in `ℕ`). A finite bipartite simple graph admits a
maximum matching and a minimum vertex cover of the same `ncard`. -/
theorem IsBipartite.exists_isMaximumMatching_isMinimumVertexCover_ncard_eq [Finite V]
    (h : G.IsBipartite) :
    ∃ (M : G.Subgraph) (c : Set V), M.IsMaximumMatching ∧ G.IsMinimumVertexCover c ∧
      M.edgeSet.ncard = c.ncard := by
  obtain ⟨M, c, hM, hc, hcard⟩ := h.exists_isMaximumMatching_isMinimumVertexCover_encard_eq
  exact ⟨M, c, hM, hc, congrArg ENat.toNat hcard⟩

/-- In a finite bipartite simple graph, every maximum matching has the same edge-set cardinality as
every minimum vertex cover has vertices. -/
theorem IsBipartite.encard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover [Finite V]
    (h : G.IsBipartite) (hM : M.IsMaximumMatching) (hc : G.IsMinimumVertexCover c) :
    M.edgeSet.encard = c.encard := by
  rw [hM.encard_edgeSet_eq, hc.encard_eq, h.matchingNum_eq_vertexCoverNum]

/-- In a finite bipartite simple graph, every maximum matching has the same edge-set `ncard` as
every minimum vertex cover has vertices. -/
theorem IsBipartite.ncard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover [Finite V]
    (h : G.IsBipartite) (hM : M.IsMaximumMatching) (hc : G.IsMinimumVertexCover c) :
    M.edgeSet.ncard = c.ncard :=
  congrArg ENat.toNat (h.encard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover hM hc)

/-- In a finite bipartite simple graph, a matching is maximum if and only if some vertex cover has
the same cardinality. -/
theorem IsBipartite.isMaximumMatching_iff_exists_isVertexCover_encard_eq [Finite V]
    (h : G.IsBipartite) :
    M.IsMaximumMatching ↔
      M.IsMatching ∧ ∃ c : Set V, G.IsVertexCover c ∧ M.edgeSet.encard = c.encard := by
  refine ⟨fun hM ↦ ⟨hM.isMatching, ?_⟩, fun ⟨hM, _, hc, hcard⟩ ↦
    hM.isMaximumMatching_of_encard_edgeSet_eq hc hcard⟩
  obtain ⟨c, hc⟩ := G.exists_isMinimumVertexCover
  exact ⟨c, hc.isVertexCover,
    h.encard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover hM hc⟩

/-- In a finite bipartite simple graph, a vertex cover is minimum if and only if some matching has
the same cardinality. -/
theorem IsBipartite.isMinimumVertexCover_iff_exists_isMatching_encard_eq [Finite V]
    (h : G.IsBipartite) :
    G.IsMinimumVertexCover c ↔
      G.IsVertexCover c ∧ ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = c.encard := by
  refine ⟨fun hc ↦ ⟨hc.isVertexCover, ?_⟩, fun ⟨hc, _, hM, hcard⟩ ↦
    hc.isMinimumVertexCover_of_encard_eq hM hcard⟩
  obtain ⟨M, hM⟩ := G.exists_isMaximumMatching
  exact ⟨M, hM.isMatching, h.encard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover hM hc⟩

/-- In a finite bipartite simple graph, a matching is maximum if and only if some vertex cover has
the same `ncard`. -/
theorem IsBipartite.isMaximumMatching_iff_exists_isVertexCover_ncard_eq [Finite V]
    (h : G.IsBipartite) :
    M.IsMaximumMatching ↔
      M.IsMatching ∧ ∃ c : Set V, G.IsVertexCover c ∧ M.edgeSet.ncard = c.ncard := by
  refine ⟨fun hM ↦ ⟨hM.isMatching, ?_⟩, fun ⟨hM, c, hc, hcard⟩ ↦
    hM.isMaximumMatching_of_ncard_edgeSet_eq hc c.toFinite hcard⟩
  obtain ⟨c, hc⟩ := G.exists_isMinimumVertexCover
  exact ⟨c, hc.isVertexCover,
    h.ncard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover hM hc⟩

/-- In a finite bipartite simple graph, a vertex cover is minimum if and only if some matching has
the same `ncard`. -/
theorem IsBipartite.isMinimumVertexCover_iff_exists_isMatching_ncard_eq [Finite V]
    (h : G.IsBipartite) :
    G.IsMinimumVertexCover c ↔
      G.IsVertexCover c ∧ ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = c.ncard := by
  refine ⟨fun hc ↦ ⟨hc.isVertexCover, ?_⟩, fun ⟨hc, _, hM, hcard⟩ ↦
    hc.isMinimumVertexCover_of_ncard_eq hM c.toFinite hcard⟩
  obtain ⟨M, hM⟩ := G.exists_isMaximumMatching
  exact ⟨M, hM.isMatching, h.ncard_edgeSet_eq_of_isMaximumMatching_of_isMinimumVertexCover hM hc⟩

end Extremal

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
  have hsup_eq : (⨆ S : {S : Set V // S ⊆ L}, f S.val) = ⨆ (S : Set V) (_ : S ⊆ L), f S :=
    iSup_subtype
  have hsup_lt : (⨆ S : {S : Set V // S ⊆ L}, f S.val) < ⊤ :=
    (iSup_le fun S ↦ tsub_le_self.trans (encard_le_encard S.property)).trans_lt
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
    have hf₁ : f S₁ ≤ f S₀ := hS₀eq ▸ le_iSup (fun S : {S : Set V // S ⊆ L} ↦ f S.val) ⟨S₁, hS₁⟩
    exact (tsub_le_tsub_left hf₁ L.encard).trans
      ((tsub_le_iff_right.2 hLle).trans hM.encard_edgeSet_le_matchingNum)

/-- **Hall's marriage theorem in `ℕ`.** A locally finite bipartite graph with sides `L` and `R` has
a matching saturating `L` if and only if `S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard` for every
`S ⊆ L`. The reverse implication is `SimpleGraph.exists_isMatching_of_forall_ncard_le`. -/
theorem IsBipartiteWith.exists_isMatching_verts_superset_iff_forall_ncard_le [G.LocallyFinite]
    (hLR : G.IsBipartiteWith L R) :
    (∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ S ⊆ L, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  refine ⟨fun ⟨M, hLM, hM⟩ S hS ↦ ?_, exists_isMatching_of_forall_ncard_le hLR⟩
  obtain hSfin | hSinf := S.finite_or_infinite
  · exact hM.ncard_le_ncard_biUnion_neighborSet (hS.trans hLM)
      (hSfin.biUnion fun x _ ↦ (G.neighborSet x).toFinite)
  · simp [hSinf.ncard]

/-- **Hall's marriage theorem in `ℕ∞`.** A locally finite bipartite graph with sides `L` and `R` has
a matching saturating `L` if and only if `S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard` for every
`S ⊆ L`. -/
theorem IsBipartiteWith.exists_isMatching_verts_superset_iff_forall_encard_le [G.LocallyFinite]
    (hLR : G.IsBipartiteWith L R) :
    (∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ S ⊆ L, S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard := by
  refine ⟨fun ⟨M, hLM, hM⟩ _ hS ↦ hM.encard_le_encard_biUnion_neighborSet (hS.trans hLM),
    fun hHall ↦ exists_isMatching_of_forall_ncard_le hLR fun S hS ↦ ?_⟩
  obtain hSfin | hSinf := S.finite_or_infinite
  · have hNfin : (⋃ x ∈ S, G.neighborSet x).Finite :=
      hSfin.biUnion fun x _ ↦ (G.neighborSet x).toFinite
    have h := hHall S hS
    rwa [← hSfin.cast_ncard_eq, ← hNfin.cast_ncard_eq, Nat.cast_le] at h
  · simp [hSinf.ncard]

/-- **Hall's marriage theorem for perfect matchings.** On a finite graph with covering bipartition
`L ∪ R = Set.univ`, `G` has a perfect matching if and only if `L.ncard = R.ncard` and every
`S ⊆ L` satisfies `S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem IsBipartiteWith.exists_isPerfectMatching_iff_ncard_eq_and_forall_ncard_le [Finite V]
    (hLR : G.IsBipartiteWith L R) (hcov : L ∪ R = Set.univ) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      L.ncard = R.ncard ∧ ∀ S ⊆ L, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  let _ : G.LocallyFinite := fun _ ↦ (Set.toFinite _).fintype
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
