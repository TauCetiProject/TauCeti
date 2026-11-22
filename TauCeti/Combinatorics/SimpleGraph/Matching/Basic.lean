/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import TauCeti.Combinatorics.SimpleGraph.VertexCover

import TauCeti.Combinatorics.SimpleGraph.Subgraph
import TauCeti.Data.Set.Card

/-!
# Maximal matchings, maximum matchings, the matching number, and vertex-cover duality

This file develops the basic extremal theory of matchings on a simple graph `G`, parallel to
Mathlib's `SimpleGraph.vertexCoverNum`:

* A subgraph is a maximal matching if and only if it is a matching whose vertex set covers every
  edge of `G` (`SimpleGraph.Subgraph.maximal_isMatching_iff`).
* Every matching `M` has twice as many vertices as edges in both `ℕ∞` and `ℕ`
  (`SimpleGraph.Subgraph.IsMatching.encard_verts`, `SimpleGraph.Subgraph.IsMatching.ncard_verts`),
  and at most as many edges as the vertices in any vertex cover `C`
  (`SimpleGraph.Subgraph.IsMatching.encard_edgeSet_le_encard_of_isVertexCover`).
* In a bipartite graph with sides `L` and `R`, the matched vertices in `L` are in bijection with
  the edges of `M` (`SimpleGraph.Subgraph.IsMatching.encard_verts_inter_left`,
  `SimpleGraph.Subgraph.IsMatching.ncard_verts_inter_left`), characterizing when `M` saturates a
  finite side `L` (`SimpleGraph.Subgraph.IsMatching.verts_superset_iff_encard_edgeSet_eq`,
  `SimpleGraph.Subgraph.IsMatching.verts_superset_iff_ncard_edgeSet_eq`).
* The matching number `SimpleGraph.matchingNum G : ℕ∞` is the supremum of `M.edgeSet.encard` over
  all matchings `M : G.Subgraph`. Every simple graph admits a maximal matching
  (`SimpleGraph.exists_maximal_isMatching`) and a matching attaining `G.matchingNum`
  (`SimpleGraph.matchingNum_exists`), and every simple graph satisfies
  `G.matchingNum ≤ G.vertexCoverNum` and `G.vertexCoverNum ≤ 2 * G.matchingNum`.
* A subgraph `M` is a *maximum matching* (`SimpleGraph.Subgraph.IsMaximumMatching M`) if it is a
  matching whose edge set has `encard` at least that of every matching of `G`. Unconditionally, a
  matching is maximum if and only if its edge-set `encard` equals `G.matchingNum`; every perfect
  matching is automatically maximum, even on an infinite vertex type.
* **Optimality certificates**: whenever `M.edgeSet.encard = c.encard` in `ℕ∞` for a matching `M`
  and a vertex cover `c`, `M` is a maximum matching
  (`SimpleGraph.Subgraph.IsMatching.isMaximumMatching_of_encard_edgeSet_eq`) and `c` is a minimum
  vertex cover (`SimpleGraph.IsVertexCover.isMinimumVertexCover_of_encard_eq`), with `Set.ncard`
  forms for finite covers (`c.Finite`).

## Main definitions

* `SimpleGraph.matchingNum`: the supremum of `M.edgeSet.encard` over matchings `M` of `G`.
* `SimpleGraph.Subgraph.IsMaximumMatching M`: `M` is a matching maximizing `M.edgeSet.encard`.

## Main results

* `SimpleGraph.Subgraph.maximal_isMatching_iff`: a matching is maximal precisely when its vertex
  set is a vertex cover of `G`.
* `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_le_encard_of_isVertexCover`: weak duality between
  matchings and vertex covers.
* `SimpleGraph.Subgraph.IsMatching.encard_verts_inter_left`,
  `SimpleGraph.Subgraph.IsMatching.verts_superset_iff_encard_edgeSet_eq`: matched-side edge
  counting and saturation in bipartite graphs.
* `SimpleGraph.Subgraph.IsMatching.exists_le_maximal` and `SimpleGraph.exists_maximal_isMatching`:
  every matching extends to a maximal matching, and every simple graph has a maximal matching.
* `SimpleGraph.matchingNum_exists`: every simple graph has a matching attaining `G.matchingNum`.
* `SimpleGraph.matchingNum_le_vertexCoverNum`,
  `SimpleGraph.vertexCoverNum_le_two_mul_encard_edgeSet_of_maximal`, and
  `SimpleGraph.vertexCoverNum_le_two_mul_matchingNum`: general two-sided bounds between matching
  and vertex-cover sizes.
* `SimpleGraph.Subgraph.isMaximumMatching_iff_encard_edgeSet_eq`: a matching is maximum if and only
  if its edge-set `encard` equals `G.matchingNum`.
* `SimpleGraph.Subgraph.isMaximumMatching_of_maximal_of_matchingNum_eq_top` and
  `SimpleGraph.exists_isMaximumMatching`: when `G.matchingNum = ⊤`, every maximal matching is
  maximum, and every simple graph admits a maximum matching.
* `SimpleGraph.Subgraph.IsMaximumMatching.maximal`: every finite maximum matching is maximal.
* `SimpleGraph.Subgraph.IsPerfectMatching.isMaximumMatching`: every perfect matching is maximum.
* `SimpleGraph.Iso.isMaximumMatching_map`: graph isomorphisms preserve maximum matchings.
* `SimpleGraph.Subgraph.isMaximumMatching_iff_ncard_edgeSet_le`: when `G.matchingNum ≠ ⊤`,
  being maximum is equivalently characterized by `Set.ncard`.
* `SimpleGraph.Subgraph.IsMatching.isMaximumMatching_of_encard_edgeSet_eq`,
  `SimpleGraph.IsVertexCover.isMinimumVertexCover_of_encard_eq`: matching-cover optimality
  certificates in `ℕ∞` (and `Set.ncard` forms for finite covers), together with extremal witness
  and dual-witness characterizations whenever `G.matchingNum = G.vertexCoverNum`.

## References

* [Mathlib PR #33032](https://github.com/leanprover-community/mathlib4/pull/33032) for the design
  precedent of `SimpleGraph.Subgraph.IsMaximumMatching` and the matching-cover optimality
  certificates (while `SimpleGraph.matchingNum` and its basic API precede that interface).
-/

public section

open Function Set

namespace SimpleGraph

variable {V W : Type*} {G G' : SimpleGraph V} {H : SimpleGraph W}

namespace Subgraph

variable {M M' : G.Subgraph}

/-- The empty subgraph is a matching. -/
@[simp]
theorem isMatching_bot : (⊥ : G.Subgraph).IsMatching := by
  intro v hv
  simp at hv

/-- The only matching of the empty graph is the empty subgraph. -/
@[simp]
theorem isMatching_of_bot_iff {M : (⊥ : SimpleGraph V).Subgraph} : M.IsMatching ↔ M = ⊥ := by
  refine ⟨fun hM ↦ ?_, fun h ↦ h ▸ isMatching_bot⟩
  rw [M.eq_bot_iff_verts_eq_empty]
  exact Set.eq_empty_iff_forall_notMem.mpr fun v hv ↦ by
    obtain ⟨w, hvw, -⟩ := hM hv
    exact (SimpleGraph.bot_adj v w).mp (M.adj_sub hvw)

/-- A subgraph `M` is a maximal matching if and only if it is a matching and its vertex set is a
vertex cover of `G`. -/
theorem maximal_isMatching_iff :
    Maximal IsMatching M ↔ M.IsMatching ∧ G.IsVertexCover M.verts := by
  refine ⟨fun ⟨hM, hmax⟩ ↦ ⟨hM, fun u v huv ↦ ?_⟩, fun ⟨hM, hcov⟩ ↦ ⟨hM, fun M' hM' hle ↦ ?_⟩⟩
  · by_contra! h
    have hdisj : Disjoint M.support (G.subgraphOfAdj huv).support := by
      rw [hM.support_eq_verts, IsMatching.subgraphOfAdj huv |>.support_eq_verts,
        subgraphOfAdj_verts]
      simp [h.1, h.2]
    have hsup : (M ⊔ G.subgraphOfAdj huv).IsMatching := hM.sup (.subgraphOfAdj huv) hdisj
    have hback : M ⊔ G.subgraphOfAdj huv ≤ M := hmax hsup le_sup_left
    exact h.1 <| hback.1 <| mem_union_right _ (by simp [subgraphOfAdj_verts])
  · have hadj {x y : V} (hxy : M'.Adj x y) : M.Adj x y := by
      rcases hcov (M'.adj_sub hxy) with hx | hy
      · obtain ⟨w, hxw, -⟩ := hM hx
        exact hM'.eq_of_adj_left hxy (hle.2 hxw) ▸ hxw
      · obtain ⟨w, hyw, -⟩ := hM hy
        exact (hM'.eq_of_adj_left hxy.symm (hle.2 hyw) ▸ hyw).symm
    refine ⟨fun x hx ↦ ?_, fun _ _ hxy ↦ hadj hxy⟩
    obtain ⟨y, hxy, -⟩ := hM' hx
    exact (hadj hxy).fst_mem

/-- Build a bijection `M.edgeSet × Bool ≃ M.verts` by reading the two ordered endpoints `Sym2.out`
of each matching edge. Kept `private` because its values depend on `Sym2.out`'s choice. -/
private noncomputable def vertsEquivEdgeSetProdBool (hM : M.IsMatching) :
    M.edgeSet × Bool ≃ M.verts := by
  have hout (e : M.edgeSet) : M.Adj e.val.out.1 e.val.out.2 := by
    have he := e.property
    rwa [← Sym2.mk_fst_out_snd_out e.val, Subgraph.mem_edgeSet] at he
  refine Equiv.ofBijective
    (fun eb ↦ cond eb.2 ⟨eb.1.val.out.2, (hout eb.1).snd_mem⟩ ⟨eb.1.val.out.1, (hout eb.1).fst_mem⟩)
    ⟨fun ⟨e₁, b₁⟩ ⟨e₂, b₂⟩ h ↦ ?_, fun ⟨v, hv⟩ ↦ ?_⟩
  · have hto (e : M.edgeSet) (b : Bool) :
        hM.toEdge (cond b ⟨e.val.out.2, (hout e).snd_mem⟩ ⟨e.val.out.1, (hout e).fst_mem⟩) = e := by
      have he : hM.toEdge ⟨_, (hout e).fst_mem⟩ = e := Subtype.ext <|
        (congrArg Subtype.val (hM.toEdge_eq_of_adj (hout e))).trans (Sym2.mk_fst_out_snd_out e.val)
      cases b
      · exact he
      · exact (hM.toEdge_eq_toEdge_of_adj (hout e)).symm.trans he
    have heq : e₁ = e₂ := (hto e₁ b₁).symm.trans ((congrArg hM.toEdge h).trans (hto e₂ b₂))
    subst heq
    cases b₁ <;> cases b₂
    · rfl
    · exact absurd (congrArg Subtype.val h) (M.adj_sub (hout e₁)).ne
    · exact absurd (congrArg Subtype.val h) (M.adj_sub (hout e₁)).ne.symm
    · rfl
  · let e : M.edgeSet := hM.toEdge ⟨v, hv⟩
    have hmem : v ∈ (e : Sym2 V) := hM.mem_coe_toEdge hv
    rw [← Sym2.mk_fst_out_snd_out e.val, Sym2.mem_iff] at hmem
    rcases hmem with hv₁ | hv₂
    · exact ⟨(e, false), Subtype.ext hv₁.symm⟩
    · exact ⟨(e, true), Subtype.ext hv₂.symm⟩

/-- The vertex set of a matching has extended cardinality twice that of its edge set. -/
theorem IsMatching.encard_verts (hM : M.IsMatching) :
    M.verts.encard = 2 * M.edgeSet.encard := by
  have hb : ENat.card Bool = 2 := by simp [ENat.card_eq_coe_fintype_card]
  calc
    M.verts.encard = ENat.card M.verts := ENat.card_coe_set_eq M.verts |>.symm
    _ = ENat.card (M.edgeSet × Bool) := (ENat.card_congr (vertsEquivEdgeSetProdBool hM)).symm
    _ = ENat.card M.edgeSet * ENat.card Bool := ENat.card_prod _ _
    _ = 2 * M.edgeSet.encard := by rw [hb, ENat.card_coe_set_eq, mul_comm]

/-- The vertex set of a matching has natural cardinality twice that of its edge set; when infinite,
both sides are zero. -/
theorem IsMatching.ncard_verts (hM : M.IsMatching) :
    M.verts.ncard = 2 * M.edgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    ← Nat.card_congr (vertsEquivEdgeSetProdBool hM), Nat.card_prod]
  have hb : Nat.card Bool = 2 := by simp
  rw [hb, mul_comm]

/-- Twice `Set.encard` of the edge set of a matching is at most `ENat.card V`. -/
theorem IsMatching.two_mul_encard_edgeSet_le_card (hM : M.IsMatching) :
    2 * M.edgeSet.encard ≤ ENat.card V := by
  rw [← hM.encard_verts]
  exact M.verts.encard_le_card

/-- A matching has finitely many edges if and only if it has finitely many vertices. -/
@[simp]
theorem IsMatching.finite_edgeSet_iff (hM : M.IsMatching) : M.edgeSet.Finite ↔ M.verts.Finite := by
  have hsup : M.spanningCoe.support = M.verts := by
    ext v
    simp only [SimpleGraph.mem_support, Subgraph.spanningCoe_adj, ← Subgraph.mem_support,
      hM.support_eq_verts]
  rw [← hsup, ← Subgraph.edgeSet_spanningCoe M]
  exact M.spanningCoe.finite_edgeSet_iff_finite_support

/-- Twice `Set.encard` of the edge set of a perfect matching equals `ENat.card V`. -/
theorem IsPerfectMatching.two_mul_encard_edgeSet (hM : M.IsPerfectMatching) :
    2 * M.edgeSet.encard = ENat.card V := by
  rw [← hM.1.encard_verts, hM.2.verts_eq_univ, Set.encard_univ]

/-- Twice the `ncard` of the edge set of a perfect matching equals `Nat.card V`. -/
theorem IsPerfectMatching.two_mul_ncard_edgeSet (hM : M.IsPerfectMatching) :
    2 * M.edgeSet.ncard = Nat.card V := by
  have h := congrArg ENat.toNat hM.two_mul_encard_edgeSet
  simpa [Set.ncard_def, ENat.toNat_mul] using h

/-- **Weak duality.** Every matching has at most as many edges as the vertices in any vertex cover,
without finiteness assumptions. -/
theorem IsMatching.encard_edgeSet_le_encard_of_isVertexCover {C : Set V}
    (hM : M.IsMatching) (hC : G.IsVertexCover C) :
    M.edgeSet.encard ≤ C.encard := by
  classical
  have hout (e : M.edgeSet) : M.Adj e.val.out.1 e.val.out.2 := by
    have he := e.property
    rwa [← Sym2.mk_fst_out_snd_out e.val, Subgraph.mem_edgeSet] at he
  -- Send each matching edge to whichever of its `Sym2.out` endpoints lies in the cover `C`.
  let pick (e : Sym2 V) : V := if e.out.1 ∈ C then e.out.1 else e.out.2
  have hmaps : MapsTo pick M.edgeSet C := by
    intro e he
    have hadj : G.Adj e.out.1 e.out.2 := M.adj_sub (hout ⟨e, he⟩)
    dsimp [pick]
    split_ifs with h₁
    · exact h₁
    · exact (hC hadj).resolve_left h₁
  refine encard_le_encard_of_injOn hmaps fun e₁ he₁ e₂ he₂ heq ↦ ?_
  have hmem (e : Sym2 V) (he : e ∈ M.edgeSet) : pick e ∈ M.verts := by
    dsimp [pick]
    split_ifs <;> [exact (hout ⟨e, he⟩).fst_mem; exact (hout ⟨e, he⟩).snd_mem]
  have hto (e : Sym2 V) (he : e ∈ M.edgeSet) : hM.toEdge ⟨pick e, hmem e he⟩ = ⟨e, he⟩ := by
    ext1
    have hfst : (hM.toEdge ⟨e.out.1, (hout ⟨e, he⟩).fst_mem⟩ : Sym2 V) = e :=
      (congrArg Subtype.val (hM.toEdge_eq_of_adj (hout ⟨e, he⟩))).trans (Sym2.mk_fst_out_snd_out e)
    by_cases h₁ : e.out.1 ∈ C
    · have hp : (⟨pick e, hmem e he⟩ : M.verts) = ⟨e.out.1, (hout ⟨e, he⟩).fst_mem⟩ := by
        ext1; simp [pick, h₁]
      rw [hp, hfst]
    · have hp : (⟨pick e, hmem e he⟩ : M.verts) = ⟨e.out.2, (hout ⟨e, he⟩).snd_mem⟩ := by
        ext1; simp [pick, h₁]
      rw [hp, ← hM.toEdge_eq_toEdge_of_adj (hout ⟨e, he⟩), hfst]
  have hv : (⟨pick e₁, hmem e₁ he₁⟩ : M.verts) = ⟨pick e₂, hmem e₂ he₂⟩ := Subtype.ext heq
  exact congrArg Subtype.val ((hto e₁ he₁).symm.trans ((congrArg hM.toEdge hv).trans (hto e₂ he₂)))

/-- Every matching in a graph with a finite vertex cover has finitely many edges. -/
theorem IsMatching.finite_edgeSet_of_isVertexCover {C : Set V}
    (hM : M.IsMatching) (hC : G.IsVertexCover C) (hCfin : C.Finite) :
    M.edgeSet.Finite :=
  hCfin.finite_of_encard_le (hM.encard_edgeSet_le_encard_of_isVertexCover hC)

/-- **Weak duality in `ℕ`.** Every matching has at most as many edges as any finite vertex cover. -/
theorem IsMatching.ncard_edgeSet_le_ncard_of_isVertexCover {C : Set V}
    (hM : M.IsMatching) (hC : G.IsVertexCover C) (hCfin : C.Finite) :
    M.edgeSet.ncard ≤ C.ncard := by
  have hle := hM.encard_edgeSet_le_encard_of_isVertexCover hC
  rwa [← (hM.finite_edgeSet_of_isVertexCover hC hCfin).cast_ncard_eq, ← hCfin.cast_ncard_eq,
    Nat.cast_le] at hle

/-- Every matching covering `S` maps `S` injectively into the neighbourhood of `S` in `G`, so
`S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard`. -/
theorem IsMatching.encard_le_encard_biUnion_neighborSet {S : Set V}
    (hM : M.IsMatching) (hS : S ⊆ M.verts) :
    S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard := by
  choose f hf _ using fun x : S ↦ hM (hS x.property)
  rw [← ENat.card_coe_set_eq, ← ENat.card_coe_set_eq]
  refine ENat.card_le_card_of_injective
    (f := fun x : S ↦ ⟨f x, mem_biUnion x.property (M.adj_sub (hf x))⟩) fun x₁ x₂ heq ↦ Subtype.ext
        ?_
  exact hM.eq_of_adj_left (hf x₁).symm (Subtype.mk.inj heq ▸ (hf x₂).symm)

/-- Every matching covering `S` maps `S` injectively into any finite neighbourhood of `S` in `G`, so
`S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem IsMatching.ncard_le_ncard_biUnion_neighborSet {S : Set V}
    (hM : M.IsMatching) (hS : S ⊆ M.verts) (hN : (⋃ x ∈ S, G.neighborSet x).Finite) :
    S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  have hle := hM.encard_le_encard_biUnion_neighborSet hS
  have hSfin : S.Finite := encard_lt_top_iff.1 (hle.trans_lt hN.encard_lt_top)
  rwa [← hSfin.cast_ncard_eq, ← hN.cast_ncard_eq, Nat.cast_le] at hle

/-- In a bipartite graph with sides `L` and `R`, sending each matched vertex in `L` to its incident
matching edge is a bijection `(M.verts ∩ L : Set V) ≃ M.edgeSet`. -/
private noncomputable def vertsInterLeftEquivEdgeSet {L R : Set V}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) :
    ↑(M.verts ∩ L) ≃ M.edgeSet := by
  refine Equiv.ofBijective (fun x ↦ hM.toEdge ⟨x.val, x.property.1⟩) ⟨fun x₁ x₂ hx ↦ ?_, fun e ↦ ?_⟩
  · have hm₂ : x₂.val ∈ (hM.toEdge ⟨x₁.val, x₁.property.1⟩ : Sym2 V) := by
      simpa [← hx] using hM.mem_coe_toEdge x₂.property.1
    obtain ⟨w, hw, -⟩ := hM x₁.property.1
    have heq : (hM.toEdge ⟨x₁.val, x₁.property.1⟩ : Sym2 V) = s(x₁.val, w) :=
      congrArg Subtype.val (hM.toEdge_eq_of_adj hw)
    rw [heq, Sym2.mem_iff] at hm₂
    rcases hm₂ with h₁₂ | h₂w
    · exact Subtype.ext h₁₂.symm
    · subst h₂w
      exact False.elim <| hLR.disjoint.ne_of_mem x₂.property.2
        (hLR.mem_of_mem_adj x₁.property.2 (M.adj_sub hw)) rfl
  · have hout : M.Adj e.val.out.1 e.val.out.2 := by
      have he := e.property
      rwa [← Sym2.mk_fst_out_snd_out e.val, Subgraph.mem_edgeSet] at he
    have hfst : hM.toEdge ⟨e.val.out.1, hout.fst_mem⟩ = e :=
      Subtype.ext <| (congrArg Subtype.val (hM.toEdge_eq_of_adj hout)).trans
        (Sym2.mk_fst_out_snd_out e.val)
    rcases hLR.mem_of_adj (M.adj_sub hout) with ⟨h₁, -⟩ | ⟨-, h₂⟩
    · exact ⟨⟨e.val.out.1, hout.fst_mem, h₁⟩, hfst⟩
    · exact ⟨⟨e.val.out.2, hout.snd_mem, h₂⟩,
        (hM.toEdge_eq_toEdge_of_adj hout).symm.trans hfst⟩

/-- In a bipartite graph with sides `L` and `R`, the number of matched vertices in `L` equals the
number of edges of the matching in `ℕ∞`. -/
theorem IsMatching.encard_verts_inter_left {L R : Set V}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) :
    (M.verts ∩ L).encard = M.edgeSet.encard :=
  ENat.card_congr (vertsInterLeftEquivEdgeSet hM hLR)

/-- In a bipartite graph with sides `L` and `R`, every matching has at most `L.encard` edges. -/
theorem IsMatching.encard_edgeSet_le_encard_left {L R : Set V}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) :
    M.edgeSet.encard ≤ L.encard :=
  hM.encard_verts_inter_left hLR ▸ encard_le_encard inter_subset_right

/-- In a bipartite graph with finite left side `L`, every matching has finitely many edges. -/
theorem IsMatching.finite_edgeSet_of_isBipartiteWith {L R : Set V}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) (hL : L.Finite) :
    M.edgeSet.Finite :=
  hL.finite_of_encard_le (hM.encard_edgeSet_le_encard_left hLR)

/-- In a bipartite graph with sides `L` and `R`, the number of matched vertices in `L` equals the
number of edges of the matching in `ℕ`. -/
theorem IsMatching.ncard_verts_inter_left {L R : Set V}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) :
    (M.verts ∩ L).ncard = M.edgeSet.ncard := by
  simpa only [Nat.card_coe_set_eq] using Nat.card_congr (vertsInterLeftEquivEdgeSet hM hLR)

/-- When the left side `L` is finite, a matching saturates `L` if and only if its edge set has
extended cardinality `L.encard`. -/
theorem IsMatching.verts_superset_iff_encard_edgeSet_eq {L R : Set V}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) (hL : L.Finite) :
    L ⊆ M.verts ↔ M.edgeSet.encard = L.encard := by
  rw [← hM.encard_verts_inter_left hLR]
  exact ⟨fun h ↦ by rw [inter_eq_right.2 h], fun h ↦
    (hL.subset inter_subset_right).eq_of_subset_of_encard_le inter_subset_right h.ge ▸
      inter_subset_left⟩

/-- When the left side `L` is finite, a matching saturates `L` if and only if its edge set has
natural cardinality `L.ncard`. -/
theorem IsMatching.verts_superset_iff_ncard_edgeSet_eq {L R : Set V}
    (hM : M.IsMatching) (hLR : G.IsBipartiteWith L R) (hL : L.Finite) :
    L ⊆ M.verts ↔ M.edgeSet.ncard = L.ncard := by
  rw [← hM.ncard_verts_inter_left hLR]
  exact ⟨fun h ↦ by rw [inter_eq_right.2 h],
    fun h ↦ eq_of_subset_of_ncard_le inter_subset_right h.ge hL ▸ inter_subset_left⟩

end Subgraph

/-- Every neighbour of a vertex outside a vertex cover `C` belongs to `C`. -/
theorem IsVertexCover.biUnion_neighborSet_sdiff_subset {C : Set V}
    (hC : G.IsVertexCover C) (L : Set V) :
    (⋃ x ∈ L \ C, G.neighborSet x) ⊆ C := by
  rintro y hy
  obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.1 hy
  exact (hC hxy).resolve_left hx.2

section matchingNum

/-- The matching number of `G` is the supremum of the number of edges in a matching of `G`. -/
noncomputable def matchingNum (G : SimpleGraph V) : ℕ∞ :=
  ⨆ (M : G.Subgraph) (_ : M.IsMatching), M.edgeSet.encard

/-- Unfolding lemma for `SimpleGraph.matchingNum`. -/
theorem matchingNum_def (G : SimpleGraph V) :
    G.matchingNum = ⨆ (M : G.Subgraph) (_ : M.IsMatching), M.edgeSet.encard :=
  (rfl)

/-- `G.matchingNum` is at most `n` if and only if every matching of `G` has at most `n` edges. -/
theorem matchingNum_le_iff {n : ℕ∞} :
    G.matchingNum ≤ n ↔ ∀ M : G.Subgraph, M.IsMatching → M.edgeSet.encard ≤ n := by
  simp [matchingNum_def]

/-- Every matching of `G` has extended edge cardinality at most `G.matchingNum`. -/
theorem Subgraph.IsMatching.encard_edgeSet_le_matchingNum {M : G.Subgraph} (hM : M.IsMatching) :
    M.edgeSet.encard ≤ G.matchingNum :=
  matchingNum_le_iff.mp le_rfl M hM

/-- Every matching of `G` has natural edge cardinality at most `G.matchingNum`. -/
theorem Subgraph.IsMatching.ncard_edgeSet_le_matchingNum {M : G.Subgraph} (hM : M.IsMatching) :
    (M.edgeSet.ncard : ℕ∞) ≤ G.matchingNum := by
  obtain hfin | hinf := M.edgeSet.finite_or_infinite
  · rw [hfin.cast_ncard_eq]
    exact hM.encard_edgeSet_le_matchingNum
  · simp [hinf.ncard]

/-- The matching number of any simple graph is at most its vertex cover number. -/
theorem matchingNum_le_vertexCoverNum (G : SimpleGraph V) :
    G.matchingNum ≤ G.vertexCoverNum := by
  obtain ⟨C, hCnum, hC⟩ := G.vertexCoverNum_exists
  exact matchingNum_le_iff.2 fun M hM ↦ hCnum ▸ hM.encard_edgeSet_le_encard_of_isVertexCover hC

/-- Every simple graph with finite matching number has a matching attaining `G.matchingNum`. -/
private theorem matchingNum_exists_of_ne_top (hfin : G.matchingNum ≠ ⊤) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = G.matchingNum := by
  have : Nonempty {M : G.Subgraph // M.IsMatching} := ⟨⟨⊥, Subgraph.isMatching_bot⟩⟩
  have hsup : (⨆ M : {M : G.Subgraph // M.IsMatching}, M.val.edgeSet.encard) = G.matchingNum := by
    rw [matchingNum_def, iSup_subtype]
  obtain ⟨M, hM⟩ := ENat.exists_eq_iSup_of_lt_top (hsup ▸ lt_top_iff_ne_top.2 hfin)
  exact ⟨M.val, M.property, hM.trans hsup⟩

/-- Every matching of `G` extends to a maximal matching. -/
theorem Subgraph.IsMatching.exists_le_maximal {M : G.Subgraph} (hM : M.IsMatching) :
    ∃ M' : G.Subgraph, M ≤ M' ∧ Maximal Subgraph.IsMatching M' :=
  zorn_le_nonempty₀ {M' : G.Subgraph | M'.IsMatching} (fun c hc hchain _ _ ↦ by
    refine ⟨sSup c, fun v hv ↦ ?_, fun _ hz ↦ le_sSup hz⟩
    obtain ⟨M', hMc, hvM'⟩ := by simpa [Subgraph.verts_sSup] using hv
    obtain ⟨w, hvw, -⟩ := hc hMc hvM'
    have hadj_mono {A B : G.Subgraph} (hle : A ≤ B) {x y : V} (h : A.Adj x y) : B.Adj x y :=
      (G.subgraphOfAdj_le_iff (A.adj_sub h) B).1
        (((G.subgraphOfAdj_le_iff (A.adj_sub h) A).2 h).trans hle)
    refine ⟨w, Subgraph.sSup_adj.mpr ⟨M', hMc, hvw⟩, fun y hy ↦ ?_⟩
    obtain ⟨M'', hMc'', hyM''⟩ := Subgraph.sSup_adj.mp hy
    rcases hchain.total hMc hMc'' with hle | hle
    · exact (hc hMc'').eq_of_adj_left hyM'' (hadj_mono hle hvw)
    · exact (hc hMc).eq_of_adj_left (hadj_mono hle hyM'') hvw) M hM

/-- Every simple graph has a maximal matching. -/
theorem exists_maximal_isMatching (G : SimpleGraph V) :
    ∃ M : G.Subgraph, Maximal Subgraph.IsMatching M :=
  let ⟨M, _, hMmax⟩ := (Subgraph.isMatching_bot (G := G)).exists_le_maximal
  ⟨M, hMmax⟩

/-- The vertex cover number of `G` is at most twice the edge-set cardinality of any maximal
matching. -/
theorem vertexCoverNum_le_two_mul_encard_edgeSet_of_maximal {M : G.Subgraph}
    (hM : Maximal Subgraph.IsMatching M) :
    G.vertexCoverNum ≤ 2 * M.edgeSet.encard := by
  obtain ⟨hM, hcov⟩ := Subgraph.maximal_isMatching_iff.1 hM
  exact hcov.vertexCoverNum_le.trans hM.encard_verts.le

/-- The vertex cover number of any simple graph is at most twice its matching number. -/
theorem vertexCoverNum_le_two_mul_matchingNum (G : SimpleGraph V) :
    G.vertexCoverNum ≤ 2 * G.matchingNum := by
  obtain ⟨M, hMmax⟩ := G.exists_maximal_isMatching
  exact (vertexCoverNum_le_two_mul_encard_edgeSet_of_maximal hMmax).trans
    (mul_le_mul_right hMmax.prop.encard_edgeSet_le_matchingNum 2)

/-- A matching whose edge count equals the size of some vertex cover attains `G.matchingNum`. -/
theorem Subgraph.IsMatching.encard_edgeSet_eq_matchingNum_of_isVertexCover
    {M : G.Subgraph} {C : Set V} (hM : M.IsMatching) (hC : G.IsVertexCover C)
    (heq : M.edgeSet.encard = C.encard) :
    M.edgeSet.encard = G.matchingNum :=
  le_antisymm hM.encard_edgeSet_le_matchingNum <|
    G.matchingNum_le_vertexCoverNum.trans (hC.vertexCoverNum_le.trans_eq heq.symm)

/-- A vertex cover whose size equals the edge count of some matching attains `G.vertexCoverNum`. -/
theorem IsVertexCover.encard_eq_vertexCoverNum_of_isMatching
    {C : Set V} {M : G.Subgraph} (hC : G.IsVertexCover C) (hM : M.IsMatching)
    (heq : M.edgeSet.encard = C.encard) :
    C.encard = G.vertexCoverNum :=
  le_antisymm (heq ▸ hM.encard_edgeSet_le_matchingNum.trans G.matchingNum_le_vertexCoverNum)
    hC.vertexCoverNum_le

/-- The empty graph has matching number zero. -/
@[simp]
theorem matchingNum_bot : (⊥ : SimpleGraph V).matchingNum = 0 :=
  nonpos_iff_eq_zero.1 <| (matchingNum_le_vertexCoverNum ⊥).trans_eq vertexCoverNum_bot

/-- A graph on at most one vertex has matching number zero. -/
@[simp]
theorem matchingNum_of_subsingleton [Subsingleton V] : G.matchingNum = 0 :=
  nonpos_iff_eq_zero.1 <| G.matchingNum_le_vertexCoverNum.trans_eq vertexCoverNum_of_subsingleton

/-- `G.matchingNum` vanishes if and only if `G` has no edges. -/
@[simp]
theorem matchingNum_eq_zero : G.matchingNum = 0 ↔ G = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ matchingNum_bot⟩
  rw [eq_bot_iff_forall_not_adj]
  intro u v huv
  have hle := (Subgraph.IsMatching.subgraphOfAdj huv).encard_edgeSet_le_matchingNum
  rw [h, nonpos_iff_eq_zero, encard_eq_zero] at hle
  exact Set.notMem_empty s(u, v) (hle ▸ (G.subgraphOfAdj huv).mem_edgeSet.2 (by simp))

/-- A simple graph has matching number at least one if and only if it has at least one edge. -/
@[simp]
theorem one_le_matchingNum_iff : 1 ≤ G.matchingNum ↔ G ≠ ⊥ := by
  rw [Order.one_le_iff_ne_zero, ne_eq, matchingNum_eq_zero]

/-- A simple graph has infinite matching number if and only if it has infinite vertex cover
number. -/
theorem matchingNum_eq_top_iff_vertexCoverNum_eq_top :
    G.matchingNum = ⊤ ↔ G.vertexCoverNum = ⊤ := by
  refine ⟨fun h ↦ top_unique (h ▸ G.matchingNum_le_vertexCoverNum), fun h ↦ ?_⟩
  by_contra hne
  have h2ne : 2 * G.matchingNum ≠ ⊤ := by simp [two_mul, hne]
  exact h2ne (top_unique (h ▸ G.vertexCoverNum_le_two_mul_matchingNum))

/-- Twice the matching number of `G` is at most the cardinality of the vertex type. -/
theorem two_mul_matchingNum_le_card : 2 * G.matchingNum ≤ ENat.card V := by
  simp only [matchingNum_def, ENat.mul_iSup, iSup_le_iff]
  exact fun _ hM ↦ hM.two_mul_encard_edgeSet_le_card

/-- The matching number `G.matchingNum` (defined via `Set.encard`) is at most `ENat.card V`. -/
theorem matchingNum_le_card : G.matchingNum ≤ ENat.card V :=
  (le_mul_of_one_le_left zero_le one_le_two).trans two_mul_matchingNum_le_card

/-- Every graph on a finite vertex type has finite matching number. -/
@[simp]
theorem matchingNum_ne_top_of_finite [Finite V] : G.matchingNum ≠ ⊤ :=
  ne_top_of_le_ne_top vertexCoverNum_ne_top_of_finite G.matchingNum_le_vertexCoverNum

/-- The matching number of `G` is at most the number of edges of `G`. -/
theorem matchingNum_le_encard_edgeSet : G.matchingNum ≤ G.edgeSet.encard :=
  matchingNum_le_iff.2 fun M _ ↦ encard_le_encard M.edgeSet_subset

/-- Every graph with finitely many edges has finite matching number. -/
@[simp]
theorem matchingNum_ne_top_of_finite_edgeSet (h : G.edgeSet.Finite) : G.matchingNum ≠ ⊤ :=
  ne_top_of_le_ne_top (encard_ne_top_iff.2 h) matchingNum_le_encard_edgeSet

/-- If the matching number is finite, then every matching has finitely many edges. -/
theorem Subgraph.IsMatching.finite_edgeSet_of_matchingNum_ne_top {M : G.Subgraph}
    (hM : M.IsMatching) (h : G.matchingNum ≠ ⊤) : M.edgeSet.Finite :=
  Set.encard_ne_top_iff.mp (ne_top_of_le_ne_top h hM.encard_edgeSet_le_matchingNum)

/-- Subgraph containment is monotone for `SimpleGraph.matchingNum`. -/
theorem IsContained.matchingNum_le_matchingNum (h : G ⊑ H) :
    G.matchingNum ≤ H.matchingNum := by
  obtain ⟨f⟩ := h
  refine matchingNum_le_iff.2 fun M hM ↦ ?_
  exact (Subgraph.encard_edgeSet_map f.toHom f.injective M).symm.trans_le
    (hM.map f.toHom f.injective).encard_edgeSet_le_matchingNum

/-- Edge-order monotonicity for `SimpleGraph.matchingNum`. -/
@[gcongr]
theorem matchingNum_mono (h : G ≤ G') : G.matchingNum ≤ G'.matchingNum :=
  (IsContained.of_le h).matchingNum_le_matchingNum

/-- Isomorphic simple graphs have equal matching numbers. -/
theorem matchingNum_congr (f : G ≃g H) : G.matchingNum = H.matchingNum :=
  le_antisymm f.isContained.matchingNum_le_matchingNum
    f.symm.isContained.matchingNum_le_matchingNum

/-- Every perfect matching attains the matching number, even on an infinite vertex type. -/
theorem Subgraph.IsPerfectMatching.encard_edgeSet_eq_matchingNum {M : G.Subgraph}
    (hM : M.IsPerfectMatching) : M.edgeSet.encard = G.matchingNum :=
  le_antisymm hM.1.encard_edgeSet_le_matchingNum <|
    (ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp)).mp
      (hM.two_mul_encard_edgeSet ▸ G.two_mul_matchingNum_le_card)

end matchingNum

/-! ### Maximum matchings -/

namespace Subgraph

variable {M M' : G.Subgraph}

/-- A subgraph `M` of `G` is a *maximum matching* if it is a matching whose edge set has
extended cardinality `Set.encard` in `ℕ∞` at least that of every matching of `G` (every infinite
edge set counts as `⊤`). -/
def IsMaximumMatching (M : G.Subgraph) : Prop :=
  M.IsMatching ∧ IsMaxOn (fun M : G.Subgraph ↦ M.edgeSet.encard) {M | M.IsMatching} M

theorem isMaximumMatching_def :
    M.IsMaximumMatching ↔
      M.IsMatching ∧ ∀ ⦃M' : G.Subgraph⦄, M'.IsMatching → M'.edgeSet.encard ≤ M.edgeSet.encard := by
  simp [IsMaximumMatching, isMaxOn_iff]

/-- Every maximum matching is a matching. -/
@[grind →]
theorem IsMaximumMatching.isMatching (hM : M.IsMaximumMatching) : M.IsMatching :=
  hM.1

/-- Every matching has edge-set `Set.encard` at most that of a maximum matching. -/
theorem IsMaximumMatching.le_encard_edgeSet (hM : M.IsMaximumMatching) (hM' : M'.IsMatching) :
    M'.edgeSet.encard ≤ M.edgeSet.encard :=
  (isMaximumMatching_def.mp hM).2 hM'

/-- A matching is maximum if and only if its edge-set `Set.encard` equals the matching number. -/
theorem isMaximumMatching_iff_encard_edgeSet_eq :
    M.IsMaximumMatching ↔ M.IsMatching ∧ M.edgeSet.encard = G.matchingNum := by
  refine ⟨fun ⟨hM, hmax⟩ ↦ ⟨hM, ?_⟩, fun ⟨hM, h⟩ ↦
    isMaximumMatching_def.2 ⟨hM, fun _ hM' ↦ hM'.encard_edgeSet_le_matchingNum.trans_eq h.symm⟩⟩
  exact (IsMaxOn.iSup_eq hM hmax).symm.trans iSup_subtype

/-- Every maximum matching has edge-set `Set.encard` equal to the matching number. -/
@[grind →]
theorem IsMaximumMatching.encard_edgeSet_eq (hM : M.IsMaximumMatching) :
    M.edgeSet.encard = G.matchingNum :=
  (isMaximumMatching_iff_encard_edgeSet_eq.mp hM).2

/-- A finite maximum matching is a maximal matching. -/
theorem IsMaximumMatching.maximal (hM : M.IsMaximumMatching) (hfin : M.edgeSet.Finite) :
    Maximal Subgraph.IsMatching M := by
  refine ⟨hM.isMatching, fun M' hM' hle ↦ ?_⟩
  by_contra hnot
  have hlt : M < M' := lt_of_le_not_ge hle hnot
  have hssub : M.edgeSet ⊂ M'.edgeSet :=
    Subgraph.IsMatching.strictMonoOn_edgeSet hM.isMatching hM' hlt
  have hlt_encard : M.edgeSet.encard < M'.edgeSet.encard := hfin.encard_lt_encard hssub
  exact (hlt_encard.trans_le
    (hM'.encard_edgeSet_le_matchingNum.trans_eq hM.encard_edgeSet_eq.symm)).false

/-- The edge-set `Set.encard` of a maximum matching is the greatest `Set.encard` among all
matchings. -/
theorem IsMaximumMatching.isGreatest_encard_edgeSet (hM : M.IsMaximumMatching) :
    IsGreatest {n : ℕ∞ | ∃ M' : G.Subgraph, M'.IsMatching ∧ M'.edgeSet.encard = n}
      M.edgeSet.encard :=
  ⟨⟨M, hM.isMatching, rfl⟩, fun _ ⟨_, hM', hM'n⟩ ↦ hM'n ▸ hM.le_encard_edgeSet hM'⟩

/-- Every perfect matching is a maximum matching. -/
theorem IsPerfectMatching.isMaximumMatching (hM : M.IsPerfectMatching) : M.IsMaximumMatching :=
  isMaximumMatching_iff_encard_edgeSet_eq.mpr ⟨hM.1, hM.encard_edgeSet_eq_matchingNum⟩

/-- The empty subgraph is a maximum matching if and only if the graph has no edges. -/
@[simp]
theorem isMaximumMatching_bot_iff : (⊥ : G.Subgraph).IsMaximumMatching ↔ G = ⊥ := by
  rw [isMaximumMatching_iff_encard_edgeSet_eq, edgeSet_bot, Set.encard_empty,
    eq_comm (a := (0 : ℕ∞)), matchingNum_eq_zero]
  simp

/-- The unique maximum matching of the empty graph is the empty subgraph. -/
@[simp]
theorem isMaximumMatching_of_bot_iff {M : (⊥ : SimpleGraph V).Subgraph} :
    M.IsMaximumMatching ↔ M = ⊥ := by
  rw [isMaximumMatching_iff_encard_edgeSet_eq, isMatching_of_bot_iff, matchingNum_bot]
  exact and_iff_left_of_imp fun h ↦ by rw [h, edgeSet_bot, Set.encard_empty]

/-- On a subsingleton vertex type, the unique maximum matching is the empty subgraph. -/
@[simp]
theorem isMaximumMatching_of_subsingleton_iff [Subsingleton V] :
    M.IsMaximumMatching ↔ M = ⊥ := by
  have hG : G = ⊥ := Subsingleton.elim G ⊥
  subst hG
  exact isMaximumMatching_of_bot_iff

/-- A finite maximum matching has edge-set `ncard` at least that of every matching. -/
theorem IsMaximumMatching.le_ncard_edgeSet (hM : M.IsMaximumMatching) (hM' : M'.IsMatching)
    (hfin : M.edgeSet.Finite) : M'.edgeSet.ncard ≤ M.edgeSet.ncard := by
  rw [Set.ncard_def, Set.ncard_def]
  exact ENat.toNat_le_toNat (hM.le_encard_edgeSet hM') (Set.encard_ne_top_iff.mpr hfin)

/-- Every maximum matching has edge-set `ncard` equal to `G.matchingNum.toNat`. -/
theorem IsMaximumMatching.ncard_edgeSet_eq_toNat (hM : M.IsMaximumMatching) :
    M.edgeSet.ncard = G.matchingNum.toNat := by
  rw [Set.ncard_def, hM.encard_edgeSet_eq]

/-- A finite matching is maximum if and only if its edge-set `ncard` equals the matching number. -/
theorem isMaximumMatching_iff_ncard_edgeSet_eq (hfin : M.edgeSet.Finite) :
    M.IsMaximumMatching ↔ M.IsMatching ∧ (M.edgeSet.ncard : ℕ∞) = G.matchingNum := by
  rw [isMaximumMatching_iff_encard_edgeSet_eq, hfin.cast_ncard_eq]

/-- Whenever the matching number is finite, a matching is maximum if and only if it maximizes
`M.edgeSet.ncard` among all matchings. -/
theorem isMaximumMatching_iff_ncard_edgeSet_le (h : G.matchingNum ≠ ⊤) :
    M.IsMaximumMatching ↔
      M.IsMatching ∧ ∀ ⦃M' : G.Subgraph⦄, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard := by
  rw [isMaximumMatching_def]
  refine and_congr_right fun hM ↦ ⟨fun hmax M' hM' ↦ ?_, fun hmax M' hM' ↦ ?_⟩
  · rw [Set.ncard_def, Set.ncard_def]
    exact ENat.toNat_le_toNat (hmax hM')
      (Set.encard_ne_top_iff.mpr (hM.finite_edgeSet_of_matchingNum_ne_top h))
  · rw [← (hM'.finite_edgeSet_of_matchingNum_ne_top h).cast_ncard_eq,
      ← (hM.finite_edgeSet_of_matchingNum_ne_top h).cast_ncard_eq]
    exact Nat.cast_le.mpr (hmax hM')

/-- The edge-set `ncard` of a finite maximum matching is the greatest `ncard` among all
matchings. -/
theorem IsMaximumMatching.isGreatest_ncard_edgeSet (hM : M.IsMaximumMatching)
    (hfin : M.edgeSet.Finite) :
    IsGreatest {n : ℕ | ∃ M' : G.Subgraph, M'.IsMatching ∧ M'.edgeSet.ncard = n}
      M.edgeSet.ncard :=
  ⟨⟨M, hM.1, rfl⟩, fun _ ⟨_, hM', hM'n⟩ ↦ hM'n ▸ hM.le_ncard_edgeSet hM' hfin⟩

/-- When `G.matchingNum = ⊤`, every maximal matching of `G` is a maximum matching. -/
theorem isMaximumMatching_of_maximal_of_matchingNum_eq_top
    (hM : Maximal IsMatching M) (htop : G.matchingNum = ⊤) :
    M.IsMaximumMatching := by
  refine isMaximumMatching_iff_encard_edgeSet_eq.mpr ⟨hM.prop, ?_⟩
  rw [htop]
  by_contra hne
  have h2ne : 2 * M.edgeSet.encard ≠ ⊤ := by simp [two_mul, hne]
  exact h2ne <| top_unique <|
    (htop ▸ G.matchingNum_le_vertexCoverNum).trans
      (vertexCoverNum_le_two_mul_encard_edgeSet_of_maximal hM)

end Subgraph

/-- Mapping a subgraph along a graph isomorphism preserves maximum matchings. -/
@[simp]
theorem Iso.isMaximumMatching_map (f : G ≃g H) (M : G.Subgraph) :
    (M.map f.toHom).IsMaximumMatching ↔ M.IsMaximumMatching := by
  rw [Subgraph.isMaximumMatching_iff_encard_edgeSet_eq,
    Subgraph.isMaximumMatching_iff_encard_edgeSet_eq,
    Subgraph.Iso.isMatching_map, Subgraph.encard_edgeSet_map f.toHom f.injective,
    matchingNum_congr f]

/-- Every simple graph admits a maximum matching, even when `G.matchingNum = ⊤`. -/
theorem exists_isMaximumMatching (G : SimpleGraph V) :
    ∃ M : G.Subgraph, M.IsMaximumMatching := by
  rcases eq_or_ne G.matchingNum ⊤ with htop | hfin
  · obtain ⟨M, hMmax⟩ := G.exists_maximal_isMatching
    exact ⟨M, Subgraph.isMaximumMatching_of_maximal_of_matchingNum_eq_top hMmax htop⟩
  · obtain ⟨M, hM, hMeq⟩ := matchingNum_exists_of_ne_top hfin
    exact ⟨M, Subgraph.isMaximumMatching_iff_encard_edgeSet_eq.mpr ⟨hM, hMeq⟩⟩

/-- Every simple graph has a matching attaining `G.matchingNum`, even when `G.matchingNum = ⊤`. -/
theorem matchingNum_exists (G : SimpleGraph V) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = G.matchingNum :=
  let ⟨M, hM⟩ := G.exists_isMaximumMatching
  ⟨M, hM.isMatching, hM.encard_edgeSet_eq⟩

/-- `n ≤ G.matchingNum` if and only if some matching of `G` has at least `n` edges. -/
theorem le_matchingNum_iff {n : ℕ∞} :
    n ≤ G.matchingNum ↔ ∃ M : G.Subgraph, M.IsMatching ∧ n ≤ M.edgeSet.encard :=
  ⟨fun h ↦ let ⟨M, hM, hMeq⟩ := G.matchingNum_exists; ⟨M, hM, hMeq ▸ h⟩,
   fun ⟨_, hM, hle⟩ ↦ hle.trans hM.encard_edgeSet_le_matchingNum⟩

/-! ### Weak duality and optimality certificates -/

section Certificates

variable {M : G.Subgraph} {c : Set V}

/-- The extended edge-set cardinality `M.edgeSet.encard` (in `ℕ∞`) of any matching `M` of a
simple graph is at most `G.vertexCoverNum`. -/
theorem Subgraph.IsMatching.encard_edgeSet_le_vertexCoverNum (hM : M.IsMatching) :
    M.edgeSet.encard ≤ G.vertexCoverNum :=
  hM.encard_edgeSet_le_matchingNum.trans G.matchingNum_le_vertexCoverNum

/-- The matching number `G.matchingNum` of a simple graph is at most the extended cardinality
`c.encard` (in `ℕ∞`) of any vertex cover `c`. -/
theorem IsVertexCover.matchingNum_le_encard (hc : G.IsVertexCover c) : G.matchingNum ≤ c.encard :=
  G.matchingNum_le_vertexCoverNum.trans hc.vertexCoverNum_le

/-- A matching whose edge-set `Set.encard` equals the `Set.encard` of some vertex cover (in
`ℕ∞`) is a maximum matching. -/
theorem Subgraph.IsMatching.isMaximumMatching_of_encard_edgeSet_eq (hM : M.IsMatching)
    (hc : G.IsVertexCover c) (h : M.edgeSet.encard = c.encard) : M.IsMaximumMatching :=
  Subgraph.isMaximumMatching_iff_encard_edgeSet_eq.mpr
    ⟨hM, hM.encard_edgeSet_eq_matchingNum_of_isVertexCover hc h⟩

/-- A vertex cover whose `Set.encard` equals the edge-set `Set.encard` of some matching (in `ℕ∞`)
is a minimum vertex cover. -/
theorem IsVertexCover.isMinimumVertexCover_of_encard_eq (hc : G.IsVertexCover c) (hM : M.IsMatching)
    (h : M.edgeSet.encard = c.encard) : G.IsMinimumVertexCover c :=
  isMinimumVertexCover_iff_encard_eq.mpr
    ⟨hc, hc.encard_eq_vertexCoverNum_of_isMatching hM h⟩

/-- If some matching `M` and some vertex cover `c` have equal extended counts
`M.edgeSet.encard = c.encard` (in `ℕ∞`), then `G.matchingNum = G.vertexCoverNum`. -/
theorem matchingNum_eq_vertexCoverNum_of_encard_eq (hM : M.IsMatching) (hc : G.IsVertexCover c)
    (h : M.edgeSet.encard = c.encard) : G.matchingNum = G.vertexCoverNum :=
  (hM.encard_edgeSet_eq_matchingNum_of_isVertexCover hc h).symm.trans <|
    h.trans (hc.encard_eq_vertexCoverNum_of_isMatching hM h)

/-- For a finite vertex cover `c`, equality of `encard` with a matching `M` is equivalent to
equality of `ncard`, since weak duality forces `M.edgeSet` to be finite. -/
theorem Subgraph.IsMatching.encard_edgeSet_eq_iff_ncard_edgeSet_eq (hM : M.IsMatching)
    (hc : G.IsVertexCover c) (hfin : c.Finite) :
    M.edgeSet.encard = c.encard ↔ M.edgeSet.ncard = c.ncard :=
  Set.encard_eq_encard_iff_ncard_eq_ncard (hM.finite_edgeSet_of_isVertexCover hc hfin) hfin

/-- A matching whose edge-set `ncard` equals the `ncard` of a finite vertex cover is a maximum
matching. -/
theorem Subgraph.IsMatching.isMaximumMatching_of_ncard_edgeSet_eq (hM : M.IsMatching)
    (hc : G.IsVertexCover c) (hfin : c.Finite) (h : M.edgeSet.ncard = c.ncard) :
    M.IsMaximumMatching :=
  hM.isMaximumMatching_of_encard_edgeSet_eq hc
    ((hM.encard_edgeSet_eq_iff_ncard_edgeSet_eq hc hfin).2 h)

/-- A finite vertex cover whose `ncard` equals the edge-set `ncard` of a matching is a minimum
vertex cover. -/
theorem IsVertexCover.isMinimumVertexCover_of_ncard_eq (hc : G.IsVertexCover c) (hM : M.IsMatching)
    (hfin : c.Finite) (h : M.edgeSet.ncard = c.ncard) : G.IsMinimumVertexCover c :=
  hc.isMinimumVertexCover_of_encard_eq hM
    ((hM.encard_edgeSet_eq_iff_ncard_edgeSet_eq hc hfin).2 h)

/-- Whenever `G.matchingNum = G.vertexCoverNum`, every maximum matching has the same edge-set
extended cardinality as every minimum vertex cover has vertices. -/
theorem Subgraph.IsMaximumMatching.encard_edgeSet_eq_of_isMinimumVertexCover_of_matchingNum_eq
    (hM : M.IsMaximumMatching) (hc : G.IsMinimumVertexCover c)
    (h : G.matchingNum = G.vertexCoverNum) :
    M.edgeSet.encard = c.encard := by
  rw [hM.encard_edgeSet_eq, hc.encard_eq, h]

/-- Whenever `G.matchingNum = G.vertexCoverNum`, `G` admits a maximum matching and a minimum
vertex cover of equal extended cardinality. -/
theorem exists_isMaximumMatching_isMinimumVertexCover_encard_eq_of_matchingNum_eq
    (h : G.matchingNum = G.vertexCoverNum) :
    ∃ (M : G.Subgraph) (c : Set V), M.IsMaximumMatching ∧ G.IsMinimumVertexCover c ∧
      M.edgeSet.encard = c.encard := by
  obtain ⟨M, hM⟩ := G.exists_isMaximumMatching
  obtain ⟨c, hc⟩ := G.exists_isMinimumVertexCover
  exact ⟨M, c, hM, hc,
    hM.encard_edgeSet_eq_of_isMinimumVertexCover_of_matchingNum_eq hc h⟩

/-- Whenever `G.matchingNum = G.vertexCoverNum`, a matching is maximum if and only if some vertex
cover has the same extended cardinality. -/
theorem Subgraph.isMaximumMatching_iff_exists_isVertexCover_encard_eq_of_matchingNum_eq
    (h : G.matchingNum = G.vertexCoverNum) :
    M.IsMaximumMatching ↔
      M.IsMatching ∧ ∃ c : Set V, G.IsVertexCover c ∧ M.edgeSet.encard = c.encard := by
  refine ⟨fun hM ↦ ⟨hM.isMatching, ?_⟩, fun ⟨hM, _, hc, hcard⟩ ↦
    hM.isMaximumMatching_of_encard_edgeSet_eq hc hcard⟩
  obtain ⟨c, hc⟩ := G.exists_isMinimumVertexCover
  exact ⟨c, hc.isVertexCover,
    hM.encard_edgeSet_eq_of_isMinimumVertexCover_of_matchingNum_eq hc h⟩

/-- Whenever `G.matchingNum = G.vertexCoverNum`, a vertex cover is minimum if and only if some
matching has the same extended cardinality. -/
theorem isMinimumVertexCover_iff_exists_isMatching_encard_eq_of_matchingNum_eq
    (h : G.matchingNum = G.vertexCoverNum) :
    G.IsMinimumVertexCover c ↔
      G.IsVertexCover c ∧ ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = c.encard := by
  refine ⟨fun hc ↦ ⟨hc.isVertexCover, ?_⟩, fun ⟨hc, _, hM, hcard⟩ ↦
    hc.isMinimumVertexCover_of_encard_eq hM hcard⟩
  obtain ⟨M, hM⟩ := G.exists_isMaximumMatching
  exact ⟨M, hM.isMatching,
    hM.encard_edgeSet_eq_of_isMinimumVertexCover_of_matchingNum_eq hc h⟩

/-- Whenever `G.matchingNum = G.vertexCoverNum` and `G.matchingNum ≠ ⊤`, a matching is maximum
if and only if some finite vertex cover has the same `ncard`. -/
theorem Subgraph.isMaximumMatching_iff_exists_isVertexCover_ncard_eq_of_matchingNum_eq
    (h : G.matchingNum = G.vertexCoverNum) (hfin : G.matchingNum ≠ ⊤) :
    M.IsMaximumMatching ↔
      M.IsMatching ∧ ∃ c : Set V, G.IsVertexCover c ∧ c.Finite ∧ M.edgeSet.ncard = c.ncard := by
  rw [Subgraph.isMaximumMatching_iff_exists_isVertexCover_encard_eq_of_matchingNum_eq h]
  refine and_congr_right fun hM ↦ exists_congr fun c ↦ ?_
  have hMfin : M.edgeSet.Finite := hM.finite_edgeSet_of_matchingNum_ne_top hfin
  refine ⟨fun ⟨hc, heq⟩ ↦ ?_, fun ⟨hc, hcf, heq⟩ ↦ ?_⟩
  · have hcf : c.Finite := Set.encard_lt_top_iff.1 (heq ▸ hMfin.encard_lt_top)
    exact ⟨hc, hcf, (Set.encard_eq_encard_iff_ncard_eq_ncard hMfin hcf).1 heq⟩
  · exact ⟨hc, (Set.encard_eq_encard_iff_ncard_eq_ncard hMfin hcf).2 heq⟩

/-- Whenever `G.matchingNum = G.vertexCoverNum`, a finite vertex cover is minimum if and only if
some matching has the same `ncard`. -/
theorem isMinimumVertexCover_iff_exists_isMatching_ncard_eq_of_matchingNum_eq
    (h : G.matchingNum = G.vertexCoverNum) (hfin : c.Finite) :
    G.IsMinimumVertexCover c ↔
      G.IsVertexCover c ∧ ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = c.ncard := by
  rw [isMinimumVertexCover_iff_exists_isMatching_encard_eq_of_matchingNum_eq h]
  exact and_congr_right fun hc ↦ exists_congr fun _ ↦ and_congr_right fun hM ↦
    hM.encard_edgeSet_eq_iff_ncard_edgeSet_eq hc hfin

end Certificates

end SimpleGraph
