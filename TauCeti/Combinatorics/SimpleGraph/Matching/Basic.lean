/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.ENat.Lattice

/-!
# Matching number and maximum matchings of simple graphs

The *matching number* `SimpleGraph.matchingNum G` of a simple graph `G` is the supremum in `ℕ∞`
of the edge-set cardinalities `M.edgeSet.encard` over all matchings `M : G.Subgraph`. Using `ℕ∞`
and `Set.encard` aligns with Mathlib's `SimpleGraph.vertexCoverNum` and applies uniformly to
arbitrary vertex types, avoiding the degeneracy of `Set.ncard` on infinite edge sets.

A subgraph `M` is a *maximum matching* (`SimpleGraph.Subgraph.IsMaximumMatching M`) if it is a
matching whose edge set has `encard` at least that of every matching of `G`. Unconditionally, a
matching is maximum if and only if its edge-set `encard` equals `G.matchingNum`; whenever
`G.matchingNum ≠ ⊤` (in particular on any finite vertex type or graph with finitely many edges),
a maximum matching exists. Every matching satisfies `M.verts.encard = 2 * M.edgeSet.encard`, so
every perfect matching is automatically maximum, even on an infinite vertex type.

## Main definitions

* `SimpleGraph.matchingNum G`: the matching number of `G` in `ℕ∞`.
* `SimpleGraph.Subgraph.IsMaximumMatching M`: `M` is a matching maximizing `M.edgeSet.encard`.

## Main results

* `SimpleGraph.Subgraph.IsMatching.encard_verts_eq_two_mul_encard_edgeSet`: a matching has twice as
  many vertices as edges.
* `SimpleGraph.matchingNum_exists_of_ne_top`: whenever `G.matchingNum ≠ ⊤`, some matching attains
  the matching number.
* `SimpleGraph.IsContained.matchingNum_le_matchingNum`, `SimpleGraph.matchingNum_mono`, and
  `SimpleGraph.matchingNum_congr`: monotonicity and isomorphism invariance of `matchingNum`.
* `SimpleGraph.Subgraph.isMaximumMatching_iff_encard_edgeSet_eq`: a matching is maximum if and only
  if its edge-set `encard` equals `G.matchingNum`.
* `SimpleGraph.Subgraph.IsPerfectMatching.isMaximumMatching`: every perfect matching is maximum.
* `SimpleGraph.Subgraph.isMaximumMatching_iff_ncard_edgeSet_le`: when `G.matchingNum ≠ ⊤`,
  maximality is equivalently characterized by `Set.ncard`.
-/

public section

namespace SimpleGraph

variable {V W : Type*} {G G' : SimpleGraph V} {H : SimpleGraph W} {M M' : G.Subgraph}

/-! ### Basic matching lemmas -/

namespace Subgraph

/-- The empty subgraph is a matching. -/
@[simp]
theorem isMatching_bot : (⊥ : G.Subgraph).IsMatching :=
  fun _ h ↦ False.elim h

/-- The only matching of the empty graph is the empty subgraph. -/
@[simp]
theorem isMatching_of_bot_iff {M : (⊥ : SimpleGraph V).Subgraph} : M.IsMatching ↔ M = ⊥ := by
  refine ⟨fun hM ↦ ?_, fun h ↦ h ▸ isMatching_bot⟩
  have hverts : M.verts = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun v hv ↦ by
    obtain ⟨w, hvw, -⟩ := hM hv
    exact M.adj_sub hvw
  exact Subgraph.ext hverts (funext₂ fun v w ↦ propext ⟨fun h ↦ False.elim (M.adj_sub h),
    False.elim⟩)

/-- Mapping a subgraph along an injective graph homomorphism preserves the cardinality of its edge
set. -/
theorem encard_edgeSet_map (f : G →g H) (hf : Function.Injective f) (M : G.Subgraph) :
    (M.map f).edgeSet.encard = M.edgeSet.encard := by
  rw [Subgraph.edgeSet_map, (Sym2.map.injective hf).encard_image]

/-- A matching has twice as many vertices as edges. -/
theorem IsMatching.encard_verts_eq_two_mul_encard_edgeSet (hM : M.IsMatching) :
    M.verts.encard = 2 * M.edgeSet.encard := by
  have hout : ∀ e : Sym2 V, s(e.out.1, e.out.2) = e := fun e ↦ e.out_eq
  have hadj : ∀ e : M.edgeSet, M.Adj e.1.out.1 e.1.out.2 := fun e ↦
    M.mem_edgeSet.mp ((hout e.1).symm ▸ e.2)
  let f : M.edgeSet × Bool → M.verts := fun p ↦
    if p.2 then ⟨p.1.1.out.2, (hadj p.1).snd_mem⟩ else ⟨p.1.1.out.1, (hadj p.1).fst_mem⟩
  have htoEdge : ∀ p : M.edgeSet × Bool, hM.toEdge (f p) = p.1 := by
    rintro ⟨e, b⟩
    cases b
    · exact (hM.toEdge_eq_of_adj (hadj e)).trans (Subtype.ext (hout e.1))
    · exact (hM.toEdge_eq_of_adj (hadj e).symm).trans
        (Subtype.ext (Sym2.eq_swap.trans (hout e.1)))
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨e₁, b₁⟩ ⟨e₂, b₂⟩ h
      have he : e₁ = e₂ := (htoEdge (e₁, b₁)).symm.trans ((congrArg hM.toEdge h).trans (htoEdge _))
      subst he
      cases b₁ <;> cases b₂
      · rfl
      · exact False.elim ((hadj e₁).ne (congrArg Subtype.val h))
      · exact False.elim ((hadj e₁).ne (congrArg Subtype.val h).symm)
      · rfl
    · intro v
      let e : M.edgeSet := hM.toEdge v
      have hv : v.1 ∈ s(e.1.out.1, e.1.out.2) := by
        rw [hout]
        exact hM.mem_coe_toEdge v.2
      rcases Sym2.mem_iff.mp hv with h | h
      · exact ⟨(e, false), Subtype.ext h.symm⟩
      · exact ⟨(e, true), Subtype.ext h.symm⟩
  rw [← ENat.card_coe_set_eq, ← ENat.card_congr (Equiv.ofBijective f hbij), ENat.card_prod,
    ENat.card_coe_set_eq, ENat.card_eq_coe_fintype_card, Fintype.card_bool, Nat.cast_ofNat,
    mul_comm]

/-- Twice the number of edges of a matching is at most the number of vertices of the ambient
graph. -/
theorem IsMatching.two_mul_encard_edgeSet_le_card (hM : M.IsMatching) :
    2 * M.edgeSet.encard ≤ ENat.card V := by
  rw [← hM.encard_verts_eq_two_mul_encard_edgeSet]
  exact M.verts.encard_le_card

/-- A matching has finitely many vertices if and only if it has finitely many edges. -/
theorem IsMatching.finite_verts_iff (hM : M.IsMatching) : M.verts.Finite ↔ M.edgeSet.Finite := by
  rw [← Set.encard_lt_top_iff, ← Set.encard_lt_top_iff, hM.encard_verts_eq_two_mul_encard_edgeSet]
  simpa [ENat.mul_top] using
    (ENat.mul_right_strictMono (a := 2) (by simp) (by simp)).lt_iff_lt
      (a := M.edgeSet.encard) (b := ⊤)

/-- A matching has twice as many vertices as edges, counted by `Set.ncard`. -/
theorem IsMatching.ncard_verts_eq_two_mul_ncard_edgeSet (hM : M.IsMatching) :
    M.verts.ncard = 2 * M.edgeSet.ncard := by
  rw [Set.ncard_def, Set.ncard_def, hM.encard_verts_eq_two_mul_encard_edgeSet, ENat.toNat_mul]
  rfl

/-- Twice the number of edges of a perfect matching equals the cardinality of the vertex type. -/
theorem IsPerfectMatching.two_mul_encard_edgeSet (hM : M.IsPerfectMatching) :
    2 * M.edgeSet.encard = ENat.card V := by
  rw [← hM.1.encard_verts_eq_two_mul_encard_edgeSet, hM.2.verts_eq_univ, Set.encard_univ]

/-- Twice the `ncard` of the edge set of a perfect matching equals `Nat.card V`. -/
theorem IsPerfectMatching.two_mul_ncard_edgeSet (hM : M.IsPerfectMatching) :
    2 * M.edgeSet.ncard = Nat.card V := by
  have h := congrArg ENat.toNat hM.two_mul_encard_edgeSet
  simpa [Set.ncard_def, ENat.toNat_mul] using h

end Subgraph

/-! ### Matching number -/

section matchingNum

/-- The matching number of `G` is the supremum of the numbers of edges in matchings of `G`. -/
noncomputable def matchingNum (G : SimpleGraph V) : ℕ∞ :=
  ⨆ (M : G.Subgraph) (_ : M.IsMatching), M.edgeSet.encard

theorem matchingNum_def (G : SimpleGraph V) :
    G.matchingNum = ⨆ (M : G.Subgraph) (_ : M.IsMatching), M.edgeSet.encard :=
  (rfl)

/-- `G.matchingNum ≤ n` if and only if every matching of `G` has at most `n` edges. -/
theorem matchingNum_le_iff {n : ℕ∞} :
    G.matchingNum ≤ n ↔ ∀ M : G.Subgraph, M.IsMatching → M.edgeSet.encard ≤ n := by
  simp [matchingNum_def]

/-- `n ≤ G.matchingNum` if and only if every upper bound on the sizes of matchings of `G` is at
least `n`. -/
theorem le_matchingNum_iff {n : ℕ∞} :
    n ≤ G.matchingNum ↔
      ∀ m : ℕ∞, (∀ M : G.Subgraph, M.IsMatching → M.edgeSet.encard ≤ m) → n ≤ m := by
  simp [matchingNum_def, le_iSup_iff]

/-- Every matching of `G` has at most `G.matchingNum` edges. -/
theorem Subgraph.IsMatching.encard_edgeSet_le_matchingNum (hM : M.IsMatching) :
    M.edgeSet.encard ≤ G.matchingNum :=
  le_matchingNum_iff.mpr fun _ hm ↦ hm M hM

/-- Whenever the matching number is finite, it is attained by some matching. -/
theorem matchingNum_exists_of_ne_top (h : G.matchingNum ≠ ⊤) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = G.matchingNum := by
  have : Nonempty {M : G.Subgraph // M.IsMatching} := ⟨⟨⊥, Subgraph.isMatching_bot⟩⟩
  have hlt : (⨆ M : {M : G.Subgraph // M.IsMatching}, M.1.edgeSet.encard) < ⊤ := by
    rw [iSup_subtype]
    exact lt_top_iff_ne_top.mpr h
  obtain ⟨M, hM⟩ := ENat.exists_eq_iSup_of_lt_top hlt
  exact ⟨M.1, M.2, hM.trans iSup_subtype⟩

/-- The empty graph has matching number zero. -/
@[simp]
theorem matchingNum_bot : matchingNum (⊥ : SimpleGraph V) = 0 :=
  nonpos_iff_eq_zero.mp <| matchingNum_le_iff.mpr fun _ hM ↦ by
    rw [Subgraph.isMatching_of_bot_iff.mp hM, Subgraph.edgeSet_bot, Set.encard_empty]

/-- Every graph on a subsingleton vertex type has matching number zero. -/
@[simp]
theorem matchingNum_of_subsingleton [Subsingleton V] : G.matchingNum = 0 := by
  have hG : G = ⊥ := Subsingleton.elim G ⊥
  rw [hG, matchingNum_bot]

/-- A simple graph has matching number zero if and only if it has no edges. -/
@[simp]
theorem matchingNum_eq_zero : G.matchingNum = 0 ↔ G = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ matchingNum_bot⟩
  rw [eq_bot_iff_forall_not_adj]
  intro v w hvw
  have hle : (G.subgraphOfAdj hvw).edgeSet.encard ≤ 0 :=
    h ▸ (Subgraph.IsMatching.subgraphOfAdj hvw).encard_edgeSet_le_matchingNum
  rw [edgeSet_subgraphOfAdj, Set.encard_singleton] at hle
  exact one_ne_zero (nonpos_iff_eq_zero.mp hle)

/-- A simple graph has matching number at least one if and only if it has at least one edge. -/
theorem one_le_matchingNum_iff : 1 ≤ G.matchingNum ↔ G ≠ ⊥ := by
  rw [Order.one_le_iff_ne_zero, ne_eq, matchingNum_eq_zero]

/-- The matching number is at most the number of edges of the graph. -/
theorem matchingNum_le_encard_edgeSet : G.matchingNum ≤ G.edgeSet.encard :=
  matchingNum_le_iff.mpr fun M _ ↦ Set.encard_le_encard M.edgeSet_subset

/-- Twice the matching number is at most the cardinality of the vertex type. -/
theorem two_mul_matchingNum_le_card : 2 * G.matchingNum ≤ ENat.card V := by
  rw [matchingNum_def, ENat.mul_iSup]
  refine iSup_le fun M ↦ ?_
  rw [ENat.mul_iSup]
  exact iSup_le fun hM ↦ hM.two_mul_encard_edgeSet_le_card

/-- The matching number is at most the cardinality of the vertex type. -/
theorem matchingNum_le_card : G.matchingNum ≤ ENat.card V :=
  (le_mul_of_one_le_left zero_le one_le_two).trans two_mul_matchingNum_le_card

/-- A simple graph on a finite vertex type has finite matching number. -/
@[simp]
theorem matchingNum_ne_top_of_finite [Finite V] : G.matchingNum ≠ ⊤ :=
  ne_top_of_le_ne_top ENat.card_lt_top_of_finite.ne matchingNum_le_card

/-- A simple graph with finitely many edges has finite matching number. -/
@[simp]
theorem matchingNum_ne_top_of_finite_edgeSet (h : G.edgeSet.Finite) : G.matchingNum ≠ ⊤ :=
  ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr h) matchingNum_le_encard_edgeSet

/-- If the matching number is finite, then every matching has finitely many edges. -/
theorem Subgraph.IsMatching.finite_edgeSet_of_matchingNum_ne_top (hM : M.IsMatching)
    (h : G.matchingNum ≠ ⊤) : M.edgeSet.Finite :=
  Set.encard_ne_top_iff.mp (ne_top_of_le_ne_top h hM.encard_edgeSet_le_matchingNum)

/-- Contained graphs have at most the matching number of the ambient graph. -/
theorem IsContained.matchingNum_le_matchingNum (h : G ⊑ H) : G.matchingNum ≤ H.matchingNum := by
  obtain ⟨f, hf⟩ := h
  refine matchingNum_le_iff.mpr fun M hM ↦ ?_
  rw [← Subgraph.encard_edgeSet_map f hf M]
  exact (hM.map f hf).encard_edgeSet_le_matchingNum

/-- Adding edges cannot decrease the matching number. -/
@[gcongr]
theorem matchingNum_mono (h : G ≤ G') : G.matchingNum ≤ G'.matchingNum :=
  (IsContained.of_le h).matchingNum_le_matchingNum

/-- Isomorphic simple graphs have the same matching number. -/
theorem matchingNum_congr (f : G ≃g H) : G.matchingNum = H.matchingNum :=
  le_antisymm f.isContained.matchingNum_le_matchingNum
    f.symm.isContained.matchingNum_le_matchingNum

/-- Every perfect matching attains the matching number, even on an infinite vertex type. -/
theorem Subgraph.IsPerfectMatching.encard_edgeSet_eq_matchingNum (hM : M.IsPerfectMatching) :
    M.edgeSet.encard = G.matchingNum :=
  le_antisymm hM.1.encard_edgeSet_le_matchingNum <|
    (ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp)).mp
      (hM.two_mul_encard_edgeSet ▸ G.two_mul_matchingNum_le_card)

end matchingNum

/-! ### Maximum matchings -/

namespace Subgraph

/-- A subgraph `M` of `G` is a *maximum matching* if it is a matching whose edge set has
cardinality at least that of every matching of `G`. -/
def IsMaximumMatching (M : G.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ ⦃M' : G.Subgraph⦄, M'.IsMatching → M'.edgeSet.encard ≤ M.edgeSet.encard

theorem isMaximumMatching_def :
    M.IsMaximumMatching ↔
      M.IsMatching ∧ ∀ ⦃M' : G.Subgraph⦄, M'.IsMatching → M'.edgeSet.encard ≤ M.edgeSet.encard :=
  Iff.rfl

/-- Every maximum matching is a matching. -/
theorem IsMaximumMatching.isMatching (hM : M.IsMaximumMatching) : M.IsMatching :=
  hM.1

/-- Every matching has edge-set cardinality at most that of a maximum matching. -/
theorem IsMaximumMatching.le_encard_edgeSet (hM : M.IsMaximumMatching) (hM' : M'.IsMatching) :
    M'.edgeSet.encard ≤ M.edgeSet.encard :=
  hM.2 hM'

/-- A matching is maximum if and only if its edge-set cardinality equals the matching number. -/
theorem isMaximumMatching_iff_encard_edgeSet_eq :
    M.IsMaximumMatching ↔ M.IsMatching ∧ M.edgeSet.encard = G.matchingNum := by
  refine and_congr_right fun hM ↦ ⟨fun h ↦ ?_, fun h M' hM' ↦ ?_⟩
  · exact le_antisymm hM.encard_edgeSet_le_matchingNum (matchingNum_le_iff.mpr fun _ hM' ↦ h hM')
  · exact hM'.encard_edgeSet_le_matchingNum.trans_eq h.symm

/-- Every maximum matching has edge-set cardinality equal to the matching number. -/
theorem IsMaximumMatching.encard_edgeSet_eq (hM : M.IsMaximumMatching) :
    M.edgeSet.encard = G.matchingNum :=
  (isMaximumMatching_iff_encard_edgeSet_eq.mp hM).2

/-- Any two maximum matchings of the same graph have the same number of edges. -/
theorem IsMaximumMatching.encard_edgeSet_eq_of_isMaximumMatching (hM : M.IsMaximumMatching)
    (hM' : M'.IsMaximumMatching) : M.edgeSet.encard = M'.edgeSet.encard :=
  hM.encard_edgeSet_eq.trans hM'.encard_edgeSet_eq.symm

/-- The edge-set cardinality of a maximum matching is the greatest among all matchings. -/
theorem IsMaximumMatching.isGreatest_encard_edgeSet (hM : M.IsMaximumMatching) :
    IsGreatest {n : ℕ∞ | ∃ M' : G.Subgraph, M'.IsMatching ∧ M'.edgeSet.encard = n}
      M.edgeSet.encard :=
  ⟨⟨M, hM.1, rfl⟩, fun _ ⟨_, hM', hM'n⟩ ↦ hM'n ▸ hM.2 hM'⟩

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

/-- Mapping a subgraph along a graph isomorphism preserves maximum matchings. -/
@[simp]
theorem Iso.isMaximumMatching_map (f : G ≃g H) (M : G.Subgraph) :
    (M.map f.toHom).IsMaximumMatching ↔ M.IsMaximumMatching := by
  rw [isMaximumMatching_iff_encard_edgeSet_eq, isMaximumMatching_iff_encard_edgeSet_eq,
    Iso.isMatching_map, encard_edgeSet_map f.toHom f.injective, matchingNum_congr f]

/-- A finite maximum matching has edge-set `ncard` at least that of every matching. -/
theorem IsMaximumMatching.le_ncard_edgeSet (hM : M.IsMaximumMatching) (hM' : M'.IsMatching)
    (hfin : M.edgeSet.Finite) : M'.edgeSet.ncard ≤ M.edgeSet.ncard :=
  ENat.toNat_le_toNat (hM.le_encard_edgeSet hM') (Set.encard_ne_top_iff.mpr hfin)

/-- Every maximum matching has edge-set `ncard` equal to `G.matchingNum.toNat`. -/
theorem IsMaximumMatching.ncard_edgeSet_eq_toNat (hM : M.IsMaximumMatching) :
    M.edgeSet.ncard = G.matchingNum.toNat := by
  rw [Set.ncard_def, hM.encard_edgeSet_eq]

/-- Any two maximum matchings of the same graph have the same edge-set `ncard`. -/
theorem IsMaximumMatching.ncard_edgeSet_eq_of_isMaximumMatching (hM : M.IsMaximumMatching)
    (hM' : M'.IsMaximumMatching) : M.edgeSet.ncard = M'.edgeSet.ncard := by
  rw [hM.ncard_edgeSet_eq_toNat, hM'.ncard_edgeSet_eq_toNat]

/-- A finite matching is maximum if and only if its edge-set `ncard` equals the matching number. -/
theorem isMaximumMatching_iff_ncard_edgeSet_eq (hfin : M.edgeSet.Finite) :
    M.IsMaximumMatching ↔ M.IsMatching ∧ (M.edgeSet.ncard : ℕ∞) = G.matchingNum := by
  rw [isMaximumMatching_iff_encard_edgeSet_eq, hfin.cast_ncard_eq]

/-- Whenever the matching number is finite, a matching is maximum if and only if it maximizes
`M.edgeSet.ncard` among all matchings. -/
theorem isMaximumMatching_iff_ncard_edgeSet_le (h : G.matchingNum ≠ ⊤) :
    M.IsMaximumMatching ↔
      M.IsMatching ∧ ∀ ⦃M' : G.Subgraph⦄, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard := by
  refine and_congr_right fun hM ↦ ⟨fun hmax M' hM' ↦ ?_, fun hmax M' hM' ↦ ?_⟩
  · exact ENat.toNat_le_toNat (hmax hM')
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

end Subgraph

/-- Whenever the matching number is finite, the graph admits a maximum matching. -/
theorem exists_isMaximumMatching_of_matchingNum_ne_top (h : G.matchingNum ≠ ⊤) :
    ∃ M : G.Subgraph, M.IsMaximumMatching := by
  obtain ⟨M, hM, hMeq⟩ := matchingNum_exists_of_ne_top h
  exact ⟨M, Subgraph.isMaximumMatching_iff_encard_edgeSet_eq.mpr ⟨hM, hMeq⟩⟩

/-- Every simple graph on a finite vertex type admits a maximum matching. -/
theorem exists_isMaximumMatching [Finite V] (G : SimpleGraph V) :
    ∃ M : G.Subgraph, M.IsMaximumMatching :=
  exists_isMaximumMatching_of_matchingNum_ne_top matchingNum_ne_top_of_finite

end SimpleGraph
