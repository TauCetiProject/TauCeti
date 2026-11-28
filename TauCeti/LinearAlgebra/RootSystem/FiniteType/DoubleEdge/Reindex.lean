/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.SimpleGraph.PathGraph.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.Basic
import TauCeti.LinearAlgebra.RootSystem.FiniteType.TwoDoubleEdges

/-!
# Reindexing path-shaped diagrams with a double edge

The classification of the model matrices `TauCeti.doubleEdgeCartanMatrix p q` is already known:
when both chains are nonempty, finite type leaves precisely the families `B_n`, `C_n`, and the
exceptional type `F_4`. To apply that result to an arbitrary Cartan matrix, its diagram must first
be reindexed onto the model.

This file performs that reindexing for the branchless case. A preconnected finite-type diagram in
which every vertex has degree at most two is a path. After orienting the path so that a chosen
double edge points from `-1` to `-2`, cutting at that edge gives two nonempty chains. No other edge
of the path is multiple: applying the affine-diagram exclusion
`TauCeti.IsFiniteType.apply_mul_apply_le_one_of_chain_of_two_le` inductively along the path rules
out a second one. Hence every other edge is simple, and the matrix itself -- not merely its
underlying graph -- is `TauCeti.doubleEdgeCartanMatrix p q` after one simultaneous relabelling.

## Main result

* `TauCeti.IsFiniteType.exists_equiv_forall_eq_doubleEdgeCartanMatrix`: a preconnected finite-type
  matrix of maximum degree two containing one oriented double edge reindexes to a nonempty
  `TauCeti.doubleEdgeCartanMatrix p q`.

This is the reindexing bridge in the double-edge branch of the classification of finite-type
Cartan matrices under the degree-at-most-two hypothesis. Excluding branch vertices in a general
connected diagram containing a double edge is a separate result. See J. E. Humphreys,
*Introduction to Lie Algebras and Representation Theory*, section 11.4, and Bourbaki,
*Lie Groups and Lie Algebras, Chapters 4--6*, Chapter VI, section 4.
-/

public section

namespace TauCeti

open SimpleGraph

variable {B : Type*} {A : Matrix B B ℤ} {n : ℕ}

/-! ## Reindexing a path-shaped diagram -/

/-- The reindexing theorem with the uniqueness of the multiple edge assumed. The hypothesis
`hsimple` on off-diagonal entries is the matrix form of saying that the chosen edge is the only
multiple edge; in particular it already forces the opposite entry `A u v` to be `-1`. The path
argument below discharges it. -/
private theorem IsFiniteType.exists_equiv_forall_eq_doubleEdgeCartanMatrix_of_simple
    [Fintype B] [DecidableEq B] (h : IsFiniteType A)
    (hconn : (diagramGraph A).Connected) (hdeg : ∀ i, (diagramGraph A).degree i ≤ 2)
    {u v : B} (hvu : A v u = -2)
    (hsimple : ∀ {i j}, i ≠ j → A i j ≠ 0 → (i = v ∧ j = u) ∨ A i j = -1) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ ∃ e : B ≃ Fin p ⊕ Fin q,
      ∀ i j, A i j = doubleEdgeCartanMatrix p q (e i) (e j) := by
  obtain ⟨iso⟩ := (h.isTree_diagramGraph hconn).nonempty_iso_pathGraph_of_degree_le_two hdeg
  exact exists_equiv_forall_eq_doubleEdgeCartanMatrix_of_pathEquiv h.isGeneralizedCartan
    iso.toEquiv iso.adj_iff_of_pathGraph hvu hsimple

/-! ## A path carries at most one multiple edge -/

/-- Starting from a multiple edge at position `a` in a path numbering, every later edge is
single. -/
private theorem apply_mul_apply_eq_one_of_isoPathGraph_of_lt (h : IsFiniteType A)
    (k : diagramGraph A ≃g pathGraph n)
    {a : ℕ} (ha : a + 1 < n)
    (hfirst : 2 ≤ A (k.symm ⟨a, by omega⟩) (k.symm ⟨a + 1, ha⟩) *
      A (k.symm ⟨a + 1, ha⟩) (k.symm ⟨a, by omega⟩))
    {r : ℕ} (hr : r + 1 < n) (har : a < r) :
    A (k.symm ⟨r, by omega⟩) (k.symm ⟨r + 1, hr⟩) *
      A (k.symm ⟨r + 1, hr⟩) (k.symm ⟨r, by omega⟩) = 1 := by
  have hk := k.adj_iff_of_pathGraph
  -- Strong induction on the distance from `a`: the intervening edges are single by induction.
  -- Thus the two-multiple-edge exclusion applies to the subpath from `a` through `r + 1`.
  induction r using Nat.strong_induction_on with
  | ind r ih =>
      let m := r - a - 1
      have hn : 0 < n := by omega
      -- Read the interval from vertex `a` through vertex `r + 1` as a chain of length `m + 3`.
      let v : ℕ → B := fun s =>
        if hs : a + s < n then k.symm ⟨a + s, hs⟩ else k.symm ⟨0, hn⟩
      have hv_apply {s : ℕ} (hs : s < m + 3) : k (v s) = ⟨a + s, by omega⟩ := by
        have hs' : a + s < n := by omega
        simp [v, hs']
      have hv_val (s : ℕ) (hs : s < m + 3) : (k (v s) : ℕ) = a + s := by
        simpa using congrArg Fin.val (hv_apply hs)
      -- The same fact read backwards, naming the vertex of the interval at each position.
      have hv_eq {s : ℕ} (hs : s < m + 3) {t : ℕ} (ht : t < n) (hst : a + s = t) :
          v s = k.symm ⟨t, ht⟩ := by
        apply k.injective
        rw [hv_apply hs, k.apply_symm_apply]
        exact Fin.ext hst
      have hv : Set.InjOn v (Set.Iio (m + 3)) := by
        intro s hs t ht hst
        have := congrArg (fun x : B => (k x : ℕ)) hst
        rw [hv_val s (Set.mem_Iio.mp hs), hv_val t (Set.mem_Iio.mp ht)] at this
        omega
      -- Nonconsecutive vertices of the interval are not adjacent in the path.
      have hzero : ∀ s t, s + 1 < t → t < m + 3 → A (v s) (v t) = 0 := by
        intro s t hst ht
        by_contra hne
        have hvne : v s ≠ v t := fun heq => by
          have := congrArg (fun x : B => (k x : ℕ)) heq
          rw [hv_val s (by omega), hv_val t ht] at this
          omega
        have hadj := h.isGeneralizedCartan.diagramGraph_adj_iff.mpr ⟨hvne, hne⟩
        rw [hk, hv_val s (by omega), hv_val t ht] at hadj
        omega
      -- Every interior edge is closer to `a` than the target edge, hence single by induction.
      have hsimple : ∀ s, 0 < s → s < m + 1 →
          A (v s) (v (s + 1)) * A (v (s + 1)) (v s) = 1 := by
        intro s hs hsm
        rw [hv_eq (t := a + s) (by omega) (by omega) rfl,
          hv_eq (t := a + s + 1) (by omega) (by omega) (by omega)]
        exact ih (a + s) (by omega) (by omega) (by omega)
      -- The two-multiple-edge exclusion applied to this interval makes its last edge single.
      have hle := h.apply_mul_apply_le_one_of_chain_of_two_le hv hzero hsimple (m := m) (by
        rw [hv_eq (t := a) (by omega) (by omega) (by omega),
          hv_eq (t := a + 1) (by omega) ha rfl]
        exact hfirst)
      rw [hv_eq (t := r) (by omega) (by omega) (by omega),
        hv_eq (t := r + 1) (by omega) hr (by omega)] at hle
      have hne : A (k.symm ⟨r, by omega⟩) (k.symm ⟨r + 1, hr⟩) ≠ 0 := by
        apply (h.isGeneralizedCartan.diagramGraph_adj_iff.mp ?_).2
        rw [hk, k.apply_symm_apply, k.apply_symm_apply]
        exact Or.inl rfl
      have hone := h.isGeneralizedCartan.one_le_apply_mul_apply hne
      omega

/-- In a path numbering, an edge lying strictly beyond a fixed multiple edge has Cartan product
one. -/
private theorem apply_mul_apply_eq_one_of_isoPathGraph_of_lt_min (h : IsFiniteType A)
    (k : diagramGraph A ≃g pathGraph n) {u v : B} (huv : (k u : ℕ) + 1 = (k v : ℕ))
    (hfirst : 2 ≤ A u v * A v u) {i j : B}
    (hpath : (k i : ℕ) + 1 = (k j : ℕ) ∨ (k j : ℕ) + 1 = (k i : ℕ))
    (hlt : (k u : ℕ) < min (k i : ℕ) (k j : ℕ)) : A i j * A j i = 1 := by
  let a := (k u : ℕ)
  let r := min (k i : ℕ) (k j : ℕ)
  have har : a < r := hlt
  have ha : a + 1 < n := by rw [huv]; exact (k v).isLt
  have hr : r + 1 < n := by rcases hpath with hp | hp <;> simp only [r] <;> omega
  -- The multiple edge is the edge from position `a` to position `a + 1`.
  have hbase : 2 ≤ A (k.symm ⟨a, by omega⟩) (k.symm ⟨a + 1, ha⟩) *
      A (k.symm ⟨a + 1, ha⟩) (k.symm ⟨a, by omega⟩) := by
    have hku : k.symm ⟨a, by omega⟩ = u := k.symm_apply_eq.mpr (Fin.ext (by simp only [a]))
    have hkv : k.symm ⟨a + 1, ha⟩ = v := k.symm_apply_eq.mpr (Fin.ext (by simp only [a]; omega))
    simpa only [hku, hkv] using hfirst
  -- The target edge is the edge from position `r` to position `r + 1`, in one of the two
  -- orientations.
  have hone := apply_mul_apply_eq_one_of_isoPathGraph_of_lt h k ha hbase hr har
  rcases hpath with hp | hp
  · have hi : k.symm ⟨r, by omega⟩ = i := k.symm_apply_eq.mpr (Fin.ext (by simp only [r]; omega))
    have hj : k.symm ⟨r + 1, hr⟩ = j := k.symm_apply_eq.mpr (Fin.ext (by simp only [r]; omega))
    simpa only [hi, hj] using hone
  · have hj : k.symm ⟨r, by omega⟩ = j := k.symm_apply_eq.mpr (Fin.ext (by simp only [r]; omega))
    have hi : k.symm ⟨r + 1, hr⟩ = i := k.symm_apply_eq.mpr (Fin.ext (by simp only [r]; omega))
    simpa only [hi, hj, mul_comm] using hone

/-- In a path numbering, every edge other than a fixed multiple edge has Cartan product one. -/
private theorem apply_mul_apply_eq_one_of_isoPathGraph (h : IsFiniteType A)
    (k : diagramGraph A ≃g pathGraph n) {u v : B} (huv : (k u : ℕ) + 1 = (k v : ℕ))
    (hfirst : 2 ≤ A u v * A v u) {i j : B} (hij : (diagramGraph A).Adj i j)
    (hne : ¬ ((i = u ∧ j = v) ∨ (i = v ∧ j = u))) : A i j * A j i = 1 := by
  -- The multiple edge occupies the positions `k u` and `k u + 1`, and the edge `i -- j` the
  -- positions `min (k i) (k j)` and `min (k i) (k j) + 1`. Trichotomy on the two positions: the
  -- previous lemma settles the edges beyond the multiple edge, the reversed numbering turns the
  -- edges before it into that case, and the remaining case is the excluded coincidence.
  have hpath := (k.adj_iff_of_pathGraph i j).mp hij
  rcases lt_trichotomy (k u : ℕ) (min (k i : ℕ) (k j : ℕ)) with hlt | heq | hgt
  · exact apply_mul_apply_eq_one_of_isoPathGraph_of_lt_min h k huv hfirst hpath hlt
  · exfalso
    rcases hpath with hp | hp
    · exact hne (Or.inl ⟨k.injective (Fin.ext (by omega)), k.injective (Fin.ext (by omega))⟩)
    · exact hne (Or.inr ⟨k.injective (Fin.ext (by omega)), k.injective (Fin.ext (by omega))⟩)
  · let k' : diagramGraph A ≃g pathGraph n := k.trans (pathGraphRevIso n)
    have hk' : ∀ x : B, (k' x : ℕ) = n - 1 - (k x : ℕ) := fun x => by
      simp only [k', RelIso.trans_apply, pathGraphRevIso_apply, Fin.val_rev]
      omega
    -- Reversing the numbering exchanges the two endpoints of the multiple edge and reverses the
    -- order of the positions, so the edge `i -- j` now lies beyond it.
    have huv' : (k' v : ℕ) + 1 = (k' u : ℕ) := by
      simp only [hk']
      have := (k v).isLt
      omega
    have hlt' : (k' v : ℕ) < min (k' i : ℕ) (k' j : ℕ) := by
      simp only [hk']
      have := (k i).isLt
      have := (k j).isLt
      omega
    refine apply_mul_apply_eq_one_of_isoPathGraph_of_lt_min h k' huv' ?_
      ((k'.adj_iff_of_pathGraph i j).mp hij) hlt'
    rw [mul_comm]
    exact hfirst

/-- **A path-shaped finite-type matrix containing an oriented double edge is a double-edge model.**
Suppose the diagram is preconnected, every vertex has degree at most two, and the edge `u -- v`
carries `A v u = -2`. Then there are nonempty chains of lengths `p` and `q` and a simultaneous
relabelling under which `A` is `TauCeti.doubleEdgeCartanMatrix p q`.

Nothing is assumed about the other edges: the path argument above proves that the chosen edge is
the only multiple edge, and the finite-type sign conditions then determine every remaining nonzero
entry. -/
-- `degree` needs finite neighbour sets while the theorem type is elaborated, so this decidability
-- instance cannot be confined to the proof.
theorem IsFiniteType.exists_equiv_forall_eq_doubleEdgeCartanMatrix [Fintype B] [DecidableEq B]
    (h : IsFiniteType A)
    (hconn : (diagramGraph A).Preconnected) (hdeg : ∀ i, (diagramGraph A).degree i ≤ 2)
    {u v : B} (hvu : A v u = -2) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ ∃ e : B ≃ Fin p ⊕ Fin q,
      ∀ i j, A i j = doubleEdgeCartanMatrix p q (e i) (e j) := by
  have : Nonempty B := ⟨u⟩
  have hconn' : (diagramGraph A).Connected := ⟨hconn⟩
  have hvu_ne : v ≠ u := by
    rintro rfl
    rw [h.isGeneralizedCartan.diag] at hvu
    omega
  have hAuv : A u v ≠ 0 := fun hz => by
    have := (h.isGeneralizedCartan.zero_comm _ _).mp hz
    rw [hvu] at this
    omega
  have hadj : (diagramGraph A).Adj u v :=
    h.isGeneralizedCartan.diagramGraph_adj_iff.mpr ⟨hvu_ne.symm, hAuv⟩
  -- The Cartan product of the double edge is `2`, so its other entry is `-1`.
  have hAuv_eq : A u v = -1 := by
    have hmem := h.apply_mul_apply_mem_of_ne hvu_ne.symm
    rw [hvu] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hc | hc | hc | hc <;> omega
  have hprod : A u v * A v u = 2 := by rw [hAuv_eq, hvu]; norm_num
  have hprod' : A v u * A u v = 2 := by rw [mul_comm]; exact hprod
  obtain ⟨k⟩ := (h.isTree_diagramGraph hconn').nonempty_iso_pathGraph_of_degree_le_two hdeg
  have hpath := (k.adj_iff_of_pathGraph u v).mp hadj
  -- Every edge other than `u -- v` is single.
  have hsingle : ∀ {i j : B}, (diagramGraph A).Adj i j →
      ¬ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) → A i j * A j i = 1 := by
    intro i j hij hne
    rcases hpath with huv | huv
    · exact apply_mul_apply_eq_one_of_isoPathGraph h k huv (by omega) hij hne
    · exact apply_mul_apply_eq_one_of_isoPathGraph h k huv (by omega) hij (by tauto)
  refine h.exists_equiv_forall_eq_doubleEdgeCartanMatrix_of_simple hconn' hdeg hvu ?_
  intro i j hij hAij
  by_cases hforward : i = v ∧ j = u
  · exact Or.inl hforward
  right
  by_cases hreverse : i = u ∧ j = v
  · rcases hreverse with ⟨rfl, rfl⟩
    exact hAuv_eq
  have hadj' := h.isGeneralizedCartan.diagramGraph_adj_iff.mpr ⟨hij, hAij⟩
  have hone := hsingle hadj' (by tauto)
  have hnonpos := h.isGeneralizedCartan.offDiag_nonpos i j hij
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hone with hpos | hneg
  · exact absurd hpos.1 (by omega)
  · exact hneg.1

end TauCeti
