/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.VertexCover

import Mathlib.Order.Zorn

/-!
# Maximal matchings, the matching number, and vertex-cover duality

This file develops the basic extremal theory of matchings on a simple graph `G` without finiteness
assumptions, parallel to Mathlib's `SimpleGraph.vertexCoverNum`:

* Every chain of matchings has a matching supremum, so every matching extends to a maximal matching
  (`SimpleGraph.Subgraph.IsMatching.exists_le_maximal`).
* A subgraph is a maximal matching if and only if it is a matching whose vertex set covers every
  edge of `G` (`SimpleGraph.Subgraph.maximal_isMatching_iff`).
* Every matching `M` has twice as many vertices as edges in both `ℕ∞` and `ℕ`
  (`SimpleGraph.Subgraph.IsMatching.encard_verts`, `SimpleGraph.Subgraph.IsMatching.ncard_verts`),
  and at most as many edges as the vertices in any vertex cover `C`
  (`SimpleGraph.Subgraph.IsMatching.encard_edgeSet_le_encard_of_isVertexCover`).
* The matching number `SimpleGraph.matchingNum G : ℕ∞` is the supremum of `M.edgeSet.encard` over
  all matchings `M : G.Subgraph`. It is always attained (`SimpleGraph.matchingNum_exists`) and
  satisfies `G.matchingNum ≤ G.vertexCoverNum` and `G.vertexCoverNum ≤ 2 * G.matchingNum`.

## Main definitions

* `SimpleGraph.matchingNum`: the supremum of `M.edgeSet.encard` over matchings `M` of `G`.

## Main results

* `SimpleGraph.Subgraph.maximal_isMatching_iff`: a matching is maximal precisely when its vertex
  set is a vertex cover of `G`.
* `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_le_encard_of_isVertexCover`: weak duality between
  matchings and vertex covers.
* `SimpleGraph.matchingNum_exists`: every simple graph has a matching attaining `G.matchingNum`.
* `SimpleGraph.matchingNum_le_vertexCoverNum`,
  `SimpleGraph.vertexCoverNum_le_two_mul_matchingNum`: general two-sided bounds between the
  matching number and the vertex cover number.
-/

public section

open Function Set

namespace SimpleGraph

variable {V W : Type*} {G G' : SimpleGraph V} {H : SimpleGraph W}

namespace Subgraph

variable {M : G.Subgraph}

/-- The empty subgraph is a matching. -/
@[simp]
theorem isMatching_bot : (⊥ : G.Subgraph).IsMatching := by
  intro v hv
  simp at hv

/-- The supremum of a chain of matchings is a matching. -/
theorem isMatching_sSup_of_isChain {c : Set G.Subgraph}
    (hc : ∀ N ∈ c, N.IsMatching) (hchain : IsChain (· ≤ ·) c) :
    (sSup c).IsMatching := by
  intro v hv
  rw [verts_sSup, mem_iUnion₂] at hv
  obtain ⟨N₁, hN₁, hv₁⟩ := hv
  obtain ⟨w, hvw, hwuniq⟩ := hc N₁ hN₁ hv₁
  refine ⟨w, sSup_adj.2 ⟨N₁, hN₁, hvw⟩, fun y hy ↦ ?_⟩
  obtain ⟨N₂, hN₂, hvy⟩ := sSup_adj.1 hy
  rcases hchain.total hN₁ hN₂ with h₁₂ | h₂₁
  · exact (hc N₂ hN₂ (hvy.fst_mem)).unique hvy (h₁₂.2 hvw)
  · exact hwuniq y (h₂₁.2 hvy)

/-- Every matching is contained in a maximal matching. -/
theorem IsMatching.exists_le_maximal (hM : M.IsMatching) :
    ∃ M' : G.Subgraph, M ≤ M' ∧ Maximal IsMatching M' :=
  zorn_le_nonempty₀ (Set.ofPred IsMatching)
    (fun c hc hchain _ _ ↦ ⟨sSup c, isMatching_sSup_of_isChain hc hchain, fun _ ↦ le_sSup⟩)
    M hM

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
  have hout (e : M.edgeSet) : M.Adj e.1.out.1 e.1.out.2 := by
    have he := e.2
    rwa [← Sym2.mk_fst_out_snd_out e.1, Subgraph.mem_edgeSet] at he
  refine Equiv.ofBijective
    (fun eb ↦ cond eb.2 ⟨eb.1.1.out.2, (hout eb.1).snd_mem⟩ ⟨eb.1.1.out.1, (hout eb.1).fst_mem⟩)
    ⟨fun ⟨e₁, b₁⟩ ⟨e₂, b₂⟩ h ↦ ?_, fun ⟨v, hv⟩ ↦ ?_⟩
  · have hto (e : M.edgeSet) (b : Bool) :
        hM.toEdge (cond b ⟨e.1.out.2, (hout e).snd_mem⟩ ⟨e.1.out.1, (hout e).fst_mem⟩) = e := by
      have he : hM.toEdge ⟨_, (hout e).fst_mem⟩ = e := Subtype.ext <|
        (congrArg Subtype.val (hM.toEdge_eq_of_adj (hout e))).trans (Sym2.mk_fst_out_snd_out e.1)
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
    rw [← Sym2.mk_fst_out_snd_out e.1, Sym2.mem_iff] at hmem
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

/-- **Weak duality.** Every matching has at most as many edges as the vertices in any vertex cover,
without finiteness assumptions. -/
theorem IsMatching.encard_edgeSet_le_encard_of_isVertexCover {C : Set V}
    (hM : M.IsMatching) (hC : G.IsVertexCover C) :
    M.edgeSet.encard ≤ C.encard := by
  classical
  have hout (e : M.edgeSet) : M.Adj e.1.out.1 e.1.out.2 := by
    have he := e.2
    rwa [← Sym2.mk_fst_out_snd_out e.1, Subgraph.mem_edgeSet] at he
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

/-- **Weak duality in `ℕ`.** Every matching has at most as many edges as any finite vertex cover. -/
theorem IsMatching.ncard_edgeSet_le_ncard_of_isVertexCover {C : Set V}
    (hM : M.IsMatching) (hC : G.IsVertexCover C) (hCfin : C.Finite) :
    M.edgeSet.ncard ≤ C.ncard := by
  have hle := hM.encard_edgeSet_le_encard_of_isVertexCover hC
  have hMfin : M.edgeSet.Finite :=
    encard_lt_top_iff.1 (hle.trans_lt hCfin.encard_lt_top)
  rwa [← hMfin.cast_ncard_eq, ← hCfin.cast_ncard_eq, Nat.cast_le] at hle

/-- Every matching covering `S` maps `S` injectively into the neighbourhood of `S` in `G`, so
`S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard`. -/
theorem IsMatching.encard_le_encard_biUnion_neighborSet {S : Set V}
    (hM : M.IsMatching) (hS : S ⊆ M.verts) :
    S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard := by
  choose f hf _ using fun x : S ↦ hM (hS x.2)
  rw [← ENat.card_coe_set_eq, ← ENat.card_coe_set_eq]
  refine ENat.card_le_card_of_injective
    (f := fun x : S ↦ ⟨f x, mem_biUnion x.2 (M.adj_sub (hf x))⟩) fun x₁ x₂ heq ↦ Subtype.ext ?_
  exact hM.eq_of_adj_left (hf x₁).symm (Subtype.mk.inj heq ▸ (hf x₂).symm)

/-- Every matching covering `S` maps `S` injectively into any finite neighbourhood of `S` in `G`, so
`S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem IsMatching.ncard_le_ncard_biUnion_neighborSet {S : Set V}
    (hM : M.IsMatching) (hS : S ⊆ M.verts) (hN : (⋃ x ∈ S, G.neighborSet x).Finite) :
    S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  have hle := hM.encard_le_encard_biUnion_neighborSet hS
  have hSfin : S.Finite := encard_lt_top_iff.1 (hle.trans_lt hN.encard_lt_top)
  rwa [← hSfin.cast_ncard_eq, ← hN.cast_ncard_eq, Nat.cast_le] at hle

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

/-- `n ≤ G.matchingNum` if and only if `n` bounds every upper bound on the edge counts of matchings
of `G`. -/
theorem le_matchingNum_iff {n : ℕ∞} :
    n ≤ G.matchingNum ↔
      ∀ m : ℕ∞, (∀ M : G.Subgraph, M.IsMatching → M.edgeSet.encard ≤ m) → n ≤ m := by
  simp [matchingNum_def, le_iSup_iff]

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

/-- Every simple graph has a maximal matching. -/
theorem exists_maximal_isMatching (G : SimpleGraph V) :
    ∃ M : G.Subgraph, Maximal Subgraph.IsMatching M := by
  obtain ⟨M, -, hM⟩ := Subgraph.isMatching_bot (G := G) |>.exists_le_maximal
  exact ⟨M, hM⟩

/-- The vertex cover number of any simple graph is at most twice its matching number. -/
theorem vertexCoverNum_le_two_mul_matchingNum (G : SimpleGraph V) :
    G.vertexCoverNum ≤ 2 * G.matchingNum := by
  obtain ⟨M, hMmax⟩ := G.exists_maximal_isMatching
  obtain ⟨hM, hcov⟩ := Subgraph.maximal_isMatching_iff.1 hMmax
  exact hcov.vertexCoverNum_le.trans <|
    hM.encard_verts.trans_le (mul_le_mul_right hM.encard_edgeSet_le_matchingNum 2)

/-- Every simple graph has a matching attaining `G.matchingNum`. -/
theorem matchingNum_exists (G : SimpleGraph V) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = G.matchingNum := by
  rcases eq_or_ne G.matchingNum ⊤ with htop | hfin
  · obtain ⟨M, hMmax⟩ := G.exists_maximal_isMatching
    obtain ⟨hM, hcov⟩ := Subgraph.maximal_isMatching_iff.1 hMmax
    refine ⟨M, hM, ?_⟩
    rw [htop]
    by_contra hne
    have h2ne : 2 * M.edgeSet.encard ≠ ⊤ := by simp [two_mul, hne]
    have hvc : G.vertexCoverNum ≠ ⊤ :=
      ne_top_of_le_ne_top h2ne (hcov.vertexCoverNum_le.trans_eq hM.encard_verts)
    exact hvc (top_unique (htop ▸ G.matchingNum_le_vertexCoverNum))
  · have : Nonempty {M : G.Subgraph // M.IsMatching} := ⟨⟨⊥, Subgraph.isMatching_bot⟩⟩
    have hsup : (⨆ M : {M : G.Subgraph // M.IsMatching}, M.1.edgeSet.encard) = G.matchingNum := by
      rw [matchingNum_def, iSup_subtype]
    obtain ⟨M, hM⟩ := ENat.exists_eq_iSup_of_lt_top (hsup ▸ lt_top_iff_ne_top.2 hfin)
    exact ⟨M.1, M.2, hM.trans hsup⟩

/-- A matching attaining a finite matching number is maximal. -/
theorem Subgraph.IsMatching.maximal_of_encard_edgeSet_eq_matchingNum {M : G.Subgraph}
    (hM : M.IsMatching) (hfin : G.matchingNum ≠ ⊤) (heq : M.edgeSet.encard = G.matchingNum) :
    Maximal Subgraph.IsMatching M := by
  refine ⟨hM, fun M' hM' hle ↦ ?_⟩
  by_contra hnot
  have hlt : M < M' := lt_of_le_not_ge hle hnot
  have hssub : M.edgeSet ⊂ M'.edgeSet := Subgraph.IsMatching.strictMonoOn_edgeSet hM hM' hlt
  have hMfin : M.edgeSet.Finite := encard_ne_top_iff.1 (heq.trans_ne hfin)
  have hlt_encard : M.edgeSet.encard < M'.edgeSet.encard := hMfin.encard_lt_encard hssub
  exact (hlt_encard.trans_le (hM'.encard_edgeSet_le_matchingNum.trans_eq heq.symm)).false

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
  obtain ⟨M, hM, hMcard⟩ := G.matchingNum_exists
  rw [← hMcard, ← hM.encard_verts]
  exact Set.encard_le_card

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

/-- Subgraph containment is monotone for `SimpleGraph.matchingNum`. -/
theorem IsContained.matchingNum_le_matchingNum (h : G ⊑ H) :
    G.matchingNum ≤ H.matchingNum := by
  obtain ⟨f⟩ := h
  refine matchingNum_le_iff.2 fun M hM ↦ ?_
  have hmap : (M.map f.toHom).IsMatching := hM.map f.toHom f.injective
  have hencard : M.edgeSet.encard = (M.map f.toHom).edgeSet.encard := by
    rw [Subgraph.edgeSet_map, Function.Injective.encard_image (Sym2.map.injective f.injective)]
  exact hencard.trans_le hmap.encard_edgeSet_le_matchingNum

/-- Edge-order monotonicity for `SimpleGraph.matchingNum`. -/
@[gcongr]
theorem matchingNum_mono (h : G ≤ G') : G.matchingNum ≤ G'.matchingNum :=
  (IsContained.of_le h).matchingNum_le_matchingNum

/-- Isomorphic simple graphs have equal matching numbers. -/
theorem matchingNum_congr (f : G ≃g H) : G.matchingNum = H.matchingNum :=
  le_antisymm f.isContained.matchingNum_le_matchingNum
    f.symm.isContained.matchingNum_le_matchingNum

end matchingNum

end SimpleGraph
