/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.VertexCover

import Mathlib.Order.Zorn
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Maximal matchings and the matching number of a simple graph

A matching `M : G.Subgraph` pairs its vertices into disjoint edges, so `M.verts` has twice the
cardinality of `M.edgeSet`. By Zorn's lemma, every matching extends to an inclusion-maximal
matching, and the vertices of any maximal matching form a vertex cover of `G`.

The *matching number* `SimpleGraph.matchingNum G : ℕ∞` is the supremum of `M.edgeSet.encard` over
all matchings `M : G.Subgraph`, dual to `SimpleGraph.vertexCoverNum G`. Every matching has at most
as many edges as any vertex cover has vertices, while any maximal matching covers `G` with twice
its edges, yielding the universal bounds

`G.matchingNum ≤ G.vertexCoverNum ≤ 2 * G.matchingNum`

without finiteness assumptions. In particular `G.matchingNum = ⊤` if and only if
`G.vertexCoverNum = ⊤`, and `G.matchingNum` is always attained by an actual matching subgraph: by
an optimal finite matching when `G.matchingNum < ⊤`, and by any maximal matching when
`G.matchingNum = ⊤`.

## Main definitions

* `SimpleGraph.matchingNum G`: the maximum number of edges in a matching of `G`, valued in `ℕ∞`.

## Main results

* `SimpleGraph.Subgraph.IsMatching.encard_verts`: a matching covers twice as many vertices as it
  has edges.
* `SimpleGraph.Subgraph.IsMatching.exists_le_maximal`: every matching is contained in a maximal
  matching.
* `SimpleGraph.Subgraph.isVertexCover_verts_of_maximal_isMatching`: the vertices of a maximal
  matching form a vertex cover.
* `SimpleGraph.matchingNum_exists`: there is always a matching attaining `G.matchingNum`.
* `SimpleGraph.matchingNum_le_vertexCoverNum` and
  `SimpleGraph.vertexCoverNum_le_two_mul_matchingNum`: universal inequalities between the matching
  number and the vertex cover number.
* `SimpleGraph.matchingNum_top_of_finite` and `SimpleGraph.matchingNum_top_of_infinite`: the
  matching number of a complete graph.
-/

public section

namespace SimpleGraph

variable {V W : Type*} {G G' : SimpleGraph V} {H : SimpleGraph W}

namespace Subgraph

variable {M : G.Subgraph}

/-- The empty subgraph is a matching. -/
@[simp]
theorem isMatching_bot : (⊥ : G.Subgraph).IsMatching := by
  intro v hv
  exact False.elim hv

/-- Non-canonical bijection between the two oriented endpoints of the edges of a matching and its
matched vertices, used internally to count `M.verts`. -/
private noncomputable def edgeSideEquiv (hM : M.IsMatching) : Bool × M.edgeSet ≃ M.verts := by
  classical
  refine
    { toFun := fun ⟨b, e⟩ ↦
        if b then ⟨e.1.out.1, M.mem_verts_of_mem_edge e.2 (Sym2.out_fst_mem e.1)⟩
        else ⟨e.1.out.2, M.mem_verts_of_mem_edge e.2 (Sym2.out_snd_mem e.1)⟩
      invFun := fun v ↦ (decide (v.1 = (hM.toEdge v).1.out.1), hM.toEdge v)
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨b, e⟩
    have hadj : M.Adj e.1.out.1 e.1.out.2 := by
      rw [← M.mem_edgeSet, Sym2.mk_fst_out_snd_out]
      exact e.2
    cases b
    · have hto : hM.toEdge ⟨e.1.out.2, M.mem_verts_of_mem_edge e.2 (Sym2.out_snd_mem e.1)⟩ = e :=
        Subtype.ext <|
          (congrArg Subtype.val (hM.toEdge_eq_of_adj hadj.symm)).trans
            (Sym2.eq_swap.trans (Sym2.mk_fst_out_snd_out e.1))
      have hne : e.1.out.2 ≠ e.1.out.1 := (M.adj_sub hadj).ne.symm
      simp [hto, hne]
    · have hto : hM.toEdge ⟨e.1.out.1, M.mem_verts_of_mem_edge e.2 (Sym2.out_fst_mem e.1)⟩ = e :=
        Subtype.ext <|
          (congrArg Subtype.val (hM.toEdge_eq_of_adj hadj)).trans (Sym2.mk_fst_out_snd_out e.1)
      simp [hto]
  · intro v
    have hmem : v.1 ∈ s((hM.toEdge v).1.out.1, (hM.toEdge v).1.out.2) := by
      rw [Sym2.mk_fst_out_snd_out]
      exact hM.mem_coe_toEdge v.2
    rcases Sym2.mem_iff.1 hmem with hv | hv
    · exact Subtype.ext (by simp [hv])
    · by_cases hv1 : v.1 = (hM.toEdge v).1.out.1
      · exact Subtype.ext (by simp [hv1])
      · exact Subtype.ext (by simp [hv1, ← hv])

/-- The vertex set of a matching has twice the extended cardinality of its edge set. -/
theorem IsMatching.encard_verts (hM : M.IsMatching) :
    M.verts.encard = 2 * M.edgeSet.encard := by
  simpa [ENat.card_prod] using (ENat.card_congr (edgeSideEquiv hM)).symm

/-- The vertex set of a matching has twice the `ncard` of its edge set. -/
theorem IsMatching.ncard_verts (hM : M.IsMatching) :
    M.verts.ncard = 2 * M.edgeSet.ncard := by
  simp [Set.ncard_def, hM.encard_verts, ENat.toNat_mul]

/-- A perfect matching on `G` has half as many edges as `V` has vertices, in `ℕ∞`. -/
theorem IsPerfectMatching.two_mul_encard_edgeSet (hM : M.IsPerfectMatching) :
    2 * M.edgeSet.encard = ENat.card V := by
  rw [← hM.1.encard_verts, hM.2.verts_eq_univ, Set.encard_univ]

/-- A perfect matching on `G` has half as many edges as `V` has vertices, in `ℕ`. -/
theorem IsPerfectMatching.two_mul_ncard_edgeSet (hM : M.IsPerfectMatching) :
    2 * M.edgeSet.ncard = Nat.card V := by
  rw [← hM.1.ncard_verts, hM.2.verts_eq_univ, Set.ncard_univ]

/-- Restricting a matching to any subset `E` of its edges produces a sub-matching with edge set
`E`. -/
theorem IsMatching.exists_le_isMatching_edgeSet_eq (hM : M.IsMatching) {E : Set (Sym2 V)}
    (hE : E ⊆ M.edgeSet) :
    ∃ N ≤ M, N.IsMatching ∧ N.edgeSet = E := by
  let s : Set V := ⋃ e ∈ E, (e : Set V)
  have hs : s ⊆ M.verts :=
    Set.iUnion₂_subset fun e he _ hv ↦ M.mem_verts_of_mem_edge (hE he) hv
  refine ⟨M.induce s, ⟨hs, fun _ _ h ↦ h.2.2⟩, fun v hv ↦ ?_, ?_⟩
  · obtain ⟨e, heE, hve⟩ := Set.mem_iUnion₂.1 hv
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : M.Adj x y := hE heE
      have hx : x ∈ s := Set.mem_iUnion₂.2 ⟨s(x, y), heE, Sym2.mem_mk_left x y⟩
      have hy : y ∈ s := Set.mem_iUnion₂.2 ⟨s(x, y), heE, Sym2.mem_mk_right x y⟩
      rcases Sym2.mem_iff.1 hve with hvx | hvy
      · subst hvx
        exact ⟨y, ⟨hx, hy, hxy⟩, fun z hz ↦ (hM.eq_of_adj_left hxy hz.2.2).symm⟩
      · subst hvy
        exact ⟨x, ⟨hy, hx, hxy.symm⟩, fun z hz ↦ (hM.eq_of_adj_left hxy.symm hz.2.2).symm⟩
  · ext e
    induction e using Sym2.ind with
    | _ x y =>
      rw [Subgraph.mem_edgeSet, Subgraph.induce_adj]
      refine ⟨fun ⟨hx, _, hxy⟩ ↦ ?_, fun he ↦ ?_⟩
      · obtain ⟨e', he'E, hxe'⟩ := Set.mem_iUnion₂.1 hx
        induction e' using Sym2.ind with
        | _ u w =>
          have huw : M.Adj u w := hE he'E
          rcases Sym2.mem_iff.1 hxe' with hxu | hxw
          · subst hxu
            have hyw : y = w := hM.eq_of_adj_left hxy huw
            exact hyw ▸ he'E
          · subst hxw
            have hyu : y = u := hM.eq_of_adj_left hxy huw.symm
            subst hyu
            exact Sym2.eq_swap ▸ he'E
      · exact ⟨Set.mem_iUnion₂.2 ⟨s(x, y), he, Sym2.mem_mk_left x y⟩,
          Set.mem_iUnion₂.2 ⟨s(x, y), he, Sym2.mem_mk_right x y⟩, hE he⟩

/-- The supremum of a chain of matchings is a matching. -/
theorem isMatching_sSup_of_isChain {c : Set G.Subgraph} (hc : IsChain (· ≤ ·) c)
    (hM : ∀ M ∈ c, M.IsMatching) :
    (sSup c).IsMatching := by
  intro v hv
  obtain ⟨M, hMc, hvM⟩ := Set.mem_iUnion₂.1 (verts_sSup c ▸ hv)
  obtain ⟨w, hvw, hwu⟩ := hM M hMc hvM
  refine ⟨w, sSup_adj.2 ⟨M, hMc, hvw⟩, fun y hy ↦ ?_⟩
  obtain ⟨N, hNc, hvy⟩ := sSup_adj.1 hy
  rcases hc.total hMc hNc with hMN | hNM
  · exact (hM N hNc (hMN.1 hvM)).unique hvy (hMN.2 hvw)
  · exact hwu y (hNM.2 hvy)

/-- Every matching is contained in an inclusion-maximal matching. -/
theorem IsMatching.exists_le_maximal (hM : M.IsMatching) :
    ∃ N : G.Subgraph, M ≤ N ∧ Maximal Subgraph.IsMatching N :=
  zorn_le_nonempty₀ {N : G.Subgraph | N.IsMatching}
    (fun _ hcs hc _ _ ↦ ⟨sSup _, isMatching_sSup_of_isChain hc hcs, fun _ ↦ le_sSup⟩) M hM

/-- The vertex set of an inclusion-maximal matching is a vertex cover of the ambient graph. -/
theorem isVertexCover_verts_of_maximal_isMatching (hM : Maximal Subgraph.IsMatching M) :
    G.IsVertexCover M.verts := by
  -- Any uncovered edge could be adjoined to enlarge the matching.
  intro u v huv
  by_contra! h
  have hdisj : Disjoint M.support (G.subgraphOfAdj huv).support := by
    rw [hM.prop.support_eq_verts, support_subgraphOfAdj]
    simp [Set.disjoint_insert_right, h.1, h.2]
  have hsup : (M ⊔ G.subgraphOfAdj huv).IsMatching :=
    hM.prop.sup (IsMatching.subgraphOfAdj huv) hdisj
  have hle : M ⊔ G.subgraphOfAdj huv ≤ M := hM.le_of_ge hsup le_sup_left
  exact h.1 ((le_sup_right.trans hle).1 (by simp))

/-- **Weak duality for simple-graph matchings.** The edge set of a matching has extended
cardinality at most that of any vertex cover. -/
theorem IsMatching.encard_edgeSet_le_of_isVertexCover (hM : M.IsMatching) {C : Set V}
    (hC : G.IsVertexCover C) :
    M.edgeSet.encard ≤ C.encard := by
  -- Map each edge `e` of `M` to an endpoint of `e` lying in `C`; disjointness of matching edges
  -- makes this choice injective.
  have hex (e : M.edgeSet) : ∃ v : C, v.1 ∈ (e.1 : Sym2 V) := by
    have hadj : M.Adj e.1.out.1 e.1.out.2 := by
      rw [← M.mem_edgeSet, Sym2.mk_fst_out_snd_out]
      exact e.2
    rcases hC (M.adj_sub hadj) with h1 | h2
    · exact ⟨⟨e.1.out.1, h1⟩, Sym2.out_fst_mem e.1⟩
    · exact ⟨⟨e.1.out.2, h2⟩, Sym2.out_snd_mem e.1⟩
  choose f hf using hex
  refine Function.Embedding.encard_le ⟨f, fun e₁ e₂ h ↦ Subtype.ext ?_⟩
  have h1 := hf e₁
  have h2 := h ▸ hf e₂
  have hv : (f e₁).1 ∈ M.verts := M.mem_verts_of_mem_edge e₁.2 h1
  obtain ⟨w₁, hw₁⟩ := Sym2.mem_iff_exists.1 h1
  obtain ⟨w₂, hw₂⟩ := Sym2.mem_iff_exists.1 h2
  have hadj₁ : M.Adj (f e₁).1 w₁ := M.mem_edgeSet.1 (hw₁ ▸ e₁.2)
  have hadj₂ : M.Adj (f e₁).1 w₂ := M.mem_edgeSet.1 (hw₂ ▸ e₂.2)
  exact hw₁.trans ((hM hv).unique hadj₁ hadj₂ ▸ hw₂.symm)

/-- **Weak duality for simple-graph matchings** in `Set.ncard` form, for a finite vertex cover. -/
theorem IsMatching.ncard_edgeSet_le_of_isVertexCover (hM : M.IsMatching) {C : Set V}
    (hC : G.IsVertexCover C) (hCf : C.Finite) :
    M.edgeSet.ncard ≤ C.ncard := by
  have hle := hM.encard_edgeSet_le_of_isVertexCover hC
  have hMf : M.edgeSet.Finite := hCf.finite_of_encard_le hle
  rwa [← hMf.cast_ncard_eq, ← hCf.cast_ncard_eq, Nat.cast_le] at hle

/-- Every matching has extended edge cardinality at most the vertex cover number. -/
theorem IsMatching.encard_edgeSet_le_vertexCoverNum (hM : M.IsMatching) :
    M.edgeSet.encard ≤ G.vertexCoverNum := by
  obtain ⟨C, hCnum, hC⟩ := G.vertexCoverNum_exists
  exact hCnum ▸ hM.encard_edgeSet_le_of_isVertexCover hC

end Subgraph

/-! ### The matching number -/

/-- The *matching number* of `G` is the supremum of the extended cardinalities of the edge sets of
matchings in `G`. -/
noncomputable def matchingNum (G : SimpleGraph V) : ℕ∞ :=
  ⨆ (M : G.Subgraph) (_ : M.IsMatching), M.edgeSet.encard

/-- Explicit supremum formula for `SimpleGraph.matchingNum`. -/
theorem matchingNum_def :
    G.matchingNum = ⨆ (M : G.Subgraph) (_ : M.IsMatching), M.edgeSet.encard :=
  (rfl)

/-- `G.matchingNum` is at most `n` if and only if every matching of `G` has at most `n` edges. -/
theorem matchingNum_le_iff {n : ℕ∞} :
    G.matchingNum ≤ n ↔ ∀ M : G.Subgraph, M.IsMatching → M.edgeSet.encard ≤ n := by
  simp [matchingNum]

/-- A matching has at most `G.matchingNum` edges. -/
theorem Subgraph.IsMatching.le_matchingNum {M : G.Subgraph} (hM : M.IsMatching) :
    M.edgeSet.encard ≤ G.matchingNum :=
  matchingNum_le_iff.1 le_rfl M hM

/-- **Weak duality.** The matching number of a graph is at most its vertex cover number. -/
theorem matchingNum_le_vertexCoverNum : G.matchingNum ≤ G.vertexCoverNum :=
  matchingNum_le_iff.2 fun _ hM ↦ hM.encard_edgeSet_le_vertexCoverNum

/-- The vertex cover number of a graph is at most twice its matching number. -/
theorem vertexCoverNum_le_two_mul_matchingNum : G.vertexCoverNum ≤ 2 * G.matchingNum := by
  -- Any inclusion-maximal matching covers `G` with twice as many vertices as edges.
  obtain ⟨M, -, hmax⟩ := (Subgraph.isMatching_bot (G := G)).exists_le_maximal
  calc
    G.vertexCoverNum ≤ M.verts.encard :=
      (Subgraph.isVertexCover_verts_of_maximal_isMatching hmax).vertexCoverNum_le
    _ = 2 * M.edgeSet.encard := hmax.prop.encard_verts
    _ ≤ 2 * G.matchingNum := mul_le_mul_right hmax.prop.le_matchingNum 2

/-- The matching number is infinite if and only if the vertex cover number is infinite. -/
@[simp]
theorem matchingNum_eq_top_iff : G.matchingNum = ⊤ ↔ G.vertexCoverNum = ⊤ := by
  refine ⟨fun h ↦ eq_top_iff.2 (h ▸ matchingNum_le_vertexCoverNum), fun h ↦ ?_⟩
  have htop : 2 * G.matchingNum = ⊤ :=
    eq_top_iff.2 (h ▸ vertexCoverNum_le_two_mul_matchingNum)
  simpa [two_mul] using htop

/-- There always exists a matching attaining `G.matchingNum`. -/
theorem matchingNum_exists (G : SimpleGraph V) :
    ∃ M : G.Subgraph, M.edgeSet.encard = G.matchingNum ∧ M.IsMatching := by
  by_cases htop : G.matchingNum = ⊤
  · -- Any maximal matching covers `G` with twice its edges, so its edge set must be infinite.
    obtain ⟨M, -, hmax⟩ := (Subgraph.isMatching_bot (G := G)).exists_le_maximal
    refine ⟨M, ?_, hmax.prop⟩
    rw [htop]
    have hcov : 2 * M.edgeSet.encard = ⊤ := eq_top_iff.2 <| by
      rw [← hmax.prop.encard_verts, ← matchingNum_eq_top_iff.1 htop]
      exact (Subgraph.isVertexCover_verts_of_maximal_isMatching hmax).vertexCoverNum_le
    simpa [two_mul] using hcov
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
    rcases eq_or_ne n 0 with rfl | hn0
    · exact ⟨⊥, by simp [← hn], Subgraph.isMatching_bot⟩
    · have hlt : ((n - 1 : ℕ) : ℕ∞) < G.matchingNum := by
        rw [← hn, Nat.cast_lt]
        omega
      simp only [matchingNum, lt_iSup_iff] at hlt
      obtain ⟨M, hM, hMlt⟩ := hlt
      have hle : M.edgeSet.encard ≤ n := hn ▸ hM.le_matchingNum
      have hge : (n : ℕ∞) ≤ M.edgeSet.encard := by
        have h1 : ((n - 1 : ℕ) : ℕ∞) + 1 ≤ M.edgeSet.encard := Order.add_one_le_of_lt hMlt
        rwa [← Nat.cast_add_one, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn0)] at h1
      exact ⟨M, le_antisymm (hn ▸ hle) (hn ▸ hge), hM⟩

/-- For every `k ≤ G.matchingNum`, there exists a matching of `G` with `k` edges. -/
theorem exists_of_le_matchingNum {k : ℕ∞} (hk : k ≤ G.matchingNum) :
    ∃ M : G.Subgraph, M.edgeSet.encard = k ∧ M.IsMatching := by
  obtain ⟨M, hMeq, hM⟩ := G.matchingNum_exists
  obtain ⟨E, hEM, hEk⟩ := Set.exists_subset_encard_eq (hMeq.symm ▸ hk)
  obtain ⟨N, -, hN, rfl⟩ := hM.exists_le_isMatching_edgeSet_eq hEM
  exact ⟨N, hEk, hN⟩

/-- The empty graph has matching number `0`. -/
@[simp]
theorem matchingNum_bot : matchingNum (emptyGraph V) = 0 :=
  nonpos_iff_eq_zero.1 <| matchingNum_le_vertexCoverNum.trans vertexCoverNum_bot.le

/-- A graph on at most one vertex has matching number `0`. -/
@[simp]
theorem matchingNum_of_subsingleton [Subsingleton V] : G.matchingNum = 0 :=
  nonpos_iff_eq_zero.1 <| matchingNum_le_vertexCoverNum.trans vertexCoverNum_of_subsingleton.le

/-- A graph has matching number `0` if and only if it has no edges. -/
@[simp]
theorem matchingNum_eq_zero : G.matchingNum = 0 ↔ G = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ matchingNum_bot⟩
  have hcov : G.vertexCoverNum = 0 :=
    nonpos_iff_eq_zero.1 (vertexCoverNum_le_two_mul_matchingNum.trans (by simp [h]))
  exact vertexCoverNum_eq_zero.1 hcov

/-- Twice the matching number is at most the cardinality of the vertex type. -/
theorem two_mul_matchingNum_le_card : 2 * G.matchingNum ≤ ENat.card V := by
  obtain ⟨M, hMeq, hM⟩ := G.matchingNum_exists
  rw [← hMeq, ← hM.encard_verts]
  exact Set.encard_le_card

/-- The matching number is at most the extended cardinality of the edge set. -/
theorem matchingNum_le_encard_edgeSet : G.matchingNum ≤ G.edgeSet.encard :=
  matchingNum_le_vertexCoverNum.trans vertexCoverNum_le_encard_edgeSet

/-- A graph on a finite vertex type has finite matching number. -/
theorem matchingNum_ne_top_of_finite [Finite V] : G.matchingNum ≠ ⊤ :=
  mt matchingNum_eq_top_iff.1 vertexCoverNum_ne_top_of_finite

/-- A graph with finitely many edges has finite matching number. -/
theorem matchingNum_ne_top_of_finite_edgeSet (h : G.edgeSet.Finite) : G.matchingNum ≠ ⊤ :=
  mt matchingNum_eq_top_iff.1 (vertexCoverNum_ne_top_of_finite_edgeSet h)

/-- On an infinite vertex type, the complete graph has infinite matching number. -/
@[simp]
theorem matchingNum_top_of_infinite [Infinite V] : (completeGraph V).matchingNum = ⊤ := by
  rw [matchingNum_eq_top_iff, vertexCoverNum_top, ENat.card_eq_top_of_infinite, ENat.top_sub_one]

/-- On a finite vertex type, the complete graph has matching number `Nat.card V / 2`. -/
@[simp]
theorem matchingNum_top_of_finite [Finite V] :
    (completeGraph V).matchingNum = (Nat.card V / 2 : ℕ) := by
  apply le_antisymm
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (matchingNum_ne_top_of_finite (G := completeGraph V))
    have h2 : 2 * (m : ℕ∞) ≤ ENat.card V := hm ▸ two_mul_matchingNum_le_card
    rw [ENat.card_eq_coe_natCard, ← Nat.cast_ofNat, ← Nat.cast_mul, Nat.cast_le] at h2
    rw [← hm, Nat.cast_le]
    omega
  · -- Any subset of size `2 * (Nat.card V / 2)` is an even finite clique, hence matched.
    have hle : ((2 * (Nat.card V / 2) : ℕ) : ℕ∞) ≤ (Set.univ : Set V).encard := by
      rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.cast_le]
      exact Nat.mul_div_le (Nat.card V) 2
    obtain ⟨u, -, hu⟩ := Set.exists_subset_encard_eq hle
    have hufin : u.Finite := u.toFinite
    have huncard : u.ncard = 2 * (Nat.card V / 2) := by
      rwa [← hufin.cast_ncard_eq, Nat.cast_inj] at hu
    have hclique : (completeGraph V).IsClique u := fun _ _ _ _ hne ↦ hne
    obtain ⟨M, hMverts, hM⟩ :=
      (hclique.even_iff_exists_isMatching hufin).1 ⟨Nat.card V / 2, by omega⟩
    have hMncard : M.edgeSet.ncard = Nat.card V / 2 := by
      have h2 := hM.ncard_verts.symm.trans (hMverts ▸ huncard)
      omega
    have hMedge : M.edgeSet.encard = (Nat.card V / 2 : ℕ) := by
      rw [← M.edgeSet.toFinite.cast_ncard_eq, hMncard]
    exact hMedge ▸ hM.le_matchingNum

/-- Subgraph containment is monotone with respect to `SimpleGraph.matchingNum`. -/
theorem IsContained.matchingNum_le_matchingNum (h : G ⊑ H) :
    G.matchingNum ≤ H.matchingNum := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨M, hMeq, hM⟩ := G.matchingNum_exists
  rw [← hMeq, ← (Sym2.map.injective hf).encard_image M.edgeSet, ← Subgraph.edgeSet_map]
  exact (hM.map f hf).le_matchingNum

/-- `SimpleGraph.matchingNum` is monotone with respect to the subgraph order on `SimpleGraph V`. -/
@[gcongr]
theorem matchingNum_mono (h : G ≤ G') : G.matchingNum ≤ G'.matchingNum :=
  (IsContained.of_le h).matchingNum_le_matchingNum

/-- Isomorphic simple graphs have equal matching numbers. -/
theorem matchingNum_congr (f : G ≃g H) : G.matchingNum = H.matchingNum :=
  le_antisymm f.isContained.matchingNum_le_matchingNum
    f.symm.isContained.matchingNum_le_matchingNum

/-! ### Strong-duality optimality certificates -/

/-- A matching and a vertex cover with `C.encard ≤ M.edgeSet.encard` certify that `M` is a maximum
matching. -/
theorem Subgraph.IsMatching.encard_edgeSet_eq_matchingNum_of_isVertexCover {M : G.Subgraph}
    (hM : M.IsMatching) {C : Set V} (hC : G.IsVertexCover C) (hMC : C.encard ≤ M.edgeSet.encard) :
    M.edgeSet.encard = G.matchingNum :=
  le_antisymm hM.le_matchingNum <|
    matchingNum_le_vertexCoverNum.trans (hC.vertexCoverNum_le.trans hMC)

/-- A matching and a vertex cover with `C.encard ≤ M.edgeSet.encard` certify that `C` is a minimum
vertex cover. -/
theorem IsVertexCover.encard_eq_vertexCoverNum_of_isMatching {C : Set V} (hC : G.IsVertexCover C)
    {M : G.Subgraph} (hM : M.IsMatching) (hMC : C.encard ≤ M.edgeSet.encard) :
    C.encard = G.vertexCoverNum :=
  le_antisymm (hMC.trans hM.encard_edgeSet_le_vertexCoverNum) hC.vertexCoverNum_le

/-- A matching and a vertex cover with `C.encard ≤ M.edgeSet.encard` certify strong duality
`G.matchingNum = G.vertexCoverNum`. -/
theorem matchingNum_eq_vertexCoverNum_of_isMatching_of_isVertexCover {M : G.Subgraph}
    (hM : M.IsMatching) {C : Set V} (hC : G.IsVertexCover C) (hMC : C.encard ≤ M.edgeSet.encard) :
    G.matchingNum = G.vertexCoverNum :=
  le_antisymm matchingNum_le_vertexCoverNum <|
    (hC.vertexCoverNum_le.trans hMC).trans hM.le_matchingNum

end SimpleGraph
