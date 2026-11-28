/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Invariance
import TauCeti.Order.Hom.PowersetCard

/-!
# Single-edge cochain evaluations

Cost, defect, and gauge-distance formulas for `TauCeti.Cochain.singleEdge`:

* `TauCeti.Cochain.cost_singleEdge_one`, `TauCeti.Cochain.cost_singleEdge_complete_one`: under the
  trivial gauge `1`, the cost of `singleEdge X u₀ v₀ g` along an edge `h : X.Adj u₀ v₀` (and in
  particular on `complete V` for `u₀ ≠ v₀`) equals `ℓ g`.
* `TauCeti.Cochain.defect_singleEdge`, `TauCeti.Cochain.defect_singleEdge_complete`: for any group
  norm `ℓ`, the defect of `singleEdge X u₀ v₀ g` along `h : X.Adj u₀ v₀` equals
  `#(X.triangles.filter fun t => {u₀, v₀} ⊆ t) * ℓ g`; on `complete V` (`u₀ ≠ v₀`) this
  evaluates to `((Fintype.card V - 2 : ℕ) : ℝ) * ℓ g`.
* `TauCeti.Cochain.gaugeDist_singleEdge`, `TauCeti.Cochain.gaugeDist_singleEdge_of_three_le_card`:
  under a conjugation-invariant group norm `ℓ`, the gauge distance of `singleEdge X u₀ v₀ g`
  equals `ℓ g` whenever `(u₀, v₀)` belongs to a filled triangle `(u₀, v₀, w)` of `X`, and in
  particular on `complete V` whenever `3 ≤ Fintype.card V` and `u₀ ≠ v₀`.
-/

public section

open Finset

namespace TauCeti

open TwoComplex

namespace Cochain

section SingleEdge

variable {V G : Type*} [Fintype V] [LinearOrder V] [Group G]

/-- Under the trivial gauge `1`, the cost of `singleEdge X u₀ v₀ g` along an edge `h : X.Adj u₀ v₀`
equals `ℓ g` for any group norm `ℓ`. -/
theorem cost_singleEdge_one {X : TwoComplex V} (ℓ : GroupNorm G) {u₀ v₀ : V}
    (h : X.Adj u₀ v₀) (g : G) :
    (singleEdge X u₀ v₀ g).cost ℓ 1 = ℓ g := by
  classical
  have huv : u₀ ≠ v₀ := h.ne
  let a := min u₀ v₀
  let b := max u₀ v₀
  have hab : a < b := min_lt_max.mpr huv
  have hedge : ({a, b} : Finset V) ∈ X.edges := by
    have hpair : ({a, b} : Finset V) = {u₀, v₀} := by
      rcases lt_or_gt_of_ne huv with hlt | hlt
      · simp [a, b, min_eq_left hlt.le, max_eq_right hlt.le]
      · simp [a, b, min_eq_right hlt.le, max_eq_left hlt.le, pair_comm]
    rw [hpair]
    exact (X.adj_iff_pair_mem_edges u₀ v₀).mp h
  have hmem : (a, b) ∈ univ.filter fun p : V × V =>
      p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges := by
    simp [hab, hedge]
  rw [cost_def, sum_eq_single_of_mem (a, b) hmem fun ⟨u, v⟩ hp hne => ?_]
  · simp only [Pi.one_apply, inv_one, one_mul, mul_one]
    rcases lt_or_gt_of_ne huv with hlt | hlt
    · have ha : a = u₀ := min_eq_left hlt.le
      have hb : b = v₀ := max_eq_right hlt.le
      rw [ha, hb, singleEdge_apply_self h]
    · have ha : a = v₀ := min_eq_right hlt.le
      have hb : b = u₀ := max_eq_left hlt.le
      rw [ha, hb, singleEdge_apply_swap h, map_inv_eq_map]
  · have hlt : u < v := (mem_filter.mp hp).2.1
    have h₁ : ¬ (u = u₀ ∧ v = v₀) := by
      rintro ⟨rfl, rfl⟩; exact hne (Prod.ext (min_eq_left hlt.le).symm (max_eq_right hlt.le).symm)
    have h₂ : ¬ (u = v₀ ∧ v = u₀) := by
      rintro ⟨rfl, rfl⟩; exact hne (Prod.ext (min_eq_right hlt.le).symm (max_eq_left hlt.le).symm)
    simp [h₁, h₂]

/-- Under the trivial gauge `1`, the cost of `singleEdge (complete V) u₀ v₀ g` (`u₀ ≠ v₀`)
equals `ℓ g` for any group norm `ℓ`. -/
theorem cost_singleEdge_complete_one (ℓ : GroupNorm G) {u₀ v₀ : V} (huv : u₀ ≠ v₀) (g : G) :
    (singleEdge (complete V) u₀ v₀ g).cost ℓ 1 = ℓ g :=
  cost_singleEdge_one ℓ ((adj_complete u₀ v₀).mpr huv) g

omit [Fintype V] in
private theorem holonomy_singleEdge_norm_eq {X : TwoComplex V} {u₀ v₀ a b c : V}
    (h : X.Adj u₀ v₀) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ℓ : GroupNorm G) (g : G) :
    ℓ ((singleEdge X u₀ v₀ g).holonomy a b c) =
      if ({u₀, v₀} : Finset V) ⊆ {a, b, c} then ℓ g else 0 := by
  split_ifs with hsub
  · have hmatch {x y : V} (hxy : (x = u₀ ∧ y = v₀) ∨ (x = v₀ ∧ y = u₀)) :
        ℓ (singleEdge X u₀ v₀ g x y) = ℓ g := by
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [singleEdge_apply_self h]
      · rw [singleEdge_apply_swap h, map_inv_eq_map]
    have hother {x y z : V} (hzx : z ≠ x) (hzy : z ≠ y)
        (hxy : (x = u₀ ∧ y = v₀) ∨ (x = v₀ ∧ y = u₀)) :
        singleEdge X u₀ v₀ g y z = 1 ∧ singleEdge X u₀ v₀ g z x = 1 := by
      have hz : z ≠ u₀ ∧ z ≠ v₀ := by
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hzx, hzy⟩
        · exact ⟨hzy, hzx⟩
      exact ⟨singleEdge_apply_of_ne g (fun ⟨_, h2⟩ => hz.2 h2) (fun ⟨_, h2⟩ => hz.1 h2),
        singleEdge_apply_of_ne g (fun ⟨h1, _⟩ => hz.1 h1) (fun ⟨h1, _⟩ => hz.2 h1)⟩
    have hu : u₀ = a ∨ u₀ = b ∨ u₀ = c := by simpa using hsub (by simp)
    have hv : v₀ = a ∨ v₀ = b ∨ v₀ = c := by simpa using hsub (by simp)
    have hcases :
        ((a = u₀ ∧ b = v₀) ∨ (a = v₀ ∧ b = u₀)) ∨
        ((b = u₀ ∧ c = v₀) ∨ (b = v₀ ∧ c = u₀)) ∨
        ((c = u₀ ∧ a = v₀) ∨ (c = v₀ ∧ a = u₀)) := by
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        first | exact (h.ne rfl).elim | tauto
    rcases hcases with hm | hm | hm
    · obtain ⟨hbc1, hca1⟩ := hother hac.symm hbc.symm hm
      rw [holonomy_def, hbc1, hca1, mul_one, mul_one, hmatch hm]
    · obtain ⟨hca1, hab1⟩ := hother hab hac hm
      rw [holonomy_def, hab1, hca1, one_mul, mul_one, hmatch hm]
    · obtain ⟨hab1, hbc1⟩ := hother hbc hab.symm hm
      rw [holonomy_def, hab1, hbc1, one_mul, one_mul, hmatch hm]
  · have hside {x y : V} (hx : x ∈ ({a, b, c} : Finset V)) (hy : y ∈ ({a, b, c} : Finset V)) :
        singleEdge X u₀ v₀ g x y = 1 :=
      singleEdge_apply_of_ne g
        (fun ⟨h1, h2⟩ => hsub (insert_subset_iff.mpr ⟨h1 ▸ hx, singleton_subset_iff.mpr (h2 ▸ hy)⟩))
        (fun ⟨h1, h2⟩ => hsub (insert_subset_iff.mpr ⟨h2 ▸ hy, singleton_subset_iff.mpr (h1 ▸ hx)⟩))
    rw [holonomy_def, hside (by simp) (by simp), hside (by simp) (by simp),
      hside (by simp) (by simp), mul_one, mul_one, map_one_eq_zero]

/-- For any group norm `ℓ` (even without conjugation invariance) and any edge `h : X.Adj u₀ v₀`,
the defect of `singleEdge X u₀ v₀ g` equals `#(X.triangles.filter fun t => {u₀, v₀} ⊆ t) * ℓ g`. -/
theorem defect_singleEdge {X : TwoComplex V} (ℓ : GroupNorm G) {u₀ v₀ : V}
    (h : X.Adj u₀ v₀) (g : G) :
    (singleEdge X u₀ v₀ g).defect ℓ =
      (#(X.triangles.filter fun t => ({u₀, v₀} : Finset V) ⊆ t) : ℝ) * ℓ g := by
  rw [defect_def]
  have hterm :
      ∑ p ∈ univ.filter (fun p : V × V × V =>
          p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1, p.2.1, p.2.2} : Finset V) ∈ X.triangles),
        ℓ ((singleEdge X u₀ v₀ g).holonomy p.1 p.2.1 p.2.2) =
      ∑ p ∈ univ.filter (fun p : V × V × V =>
          p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1, p.2.1, p.2.2} : Finset V) ∈ X.triangles),
        if ({u₀, v₀} : Finset V) ⊆ {p.1, p.2.1, p.2.2} then ℓ g else 0 := by
    refine sum_congr rfl fun p hp => ?_
    obtain ⟨h1, h2, _⟩ := (mem_filter.mp hp).2
    exact holonomy_singleEdge_norm_eq h h1.ne (h1.trans h2).ne h2.ne ℓ g
  rw [hterm, ← sum_filter, filter_filter, sum_const, nsmul_eq_mul]
  congr 1
  norm_cast
  let s : Finset (Finset V) := X.triangles.filter fun t => ({u₀, v₀} : Finset V) ⊆ t
  have hflt :
      univ.filter (fun p : V × V × V =>
          (p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ ({p.1, p.2.1, p.2.2} : Finset V) ∈ X.triangles) ∧
            ({u₀, v₀} : Finset V) ⊆ {p.1, p.2.1, p.2.2}) =
        univ.filter (fun p : V × V × V => p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
          ({p.1, p.2.1, p.2.2} : Finset V) ∈ s) := by
    ext ⟨a, b, c⟩
    simp only [s, mem_filter, mem_univ, true_and]
    tauto
  rw [hflt]
  exact Set.powersetCard.card_filter_lt_triple_eq_card_of_card_eq_three s
    fun t ht => X.triangle_card t (mem_filter.mp ht).1

/-- For any group norm `ℓ` (even without conjugation invariance), the defect of
`singleEdge (complete V) u₀ v₀ g` (`u₀ ≠ v₀`) equals `((Fintype.card V - 2 : ℕ) : ℝ) * ℓ g`. -/
theorem defect_singleEdge_complete (ℓ : GroupNorm G) {u₀ v₀ : V} (huv : u₀ ≠ v₀) (g : G) :
    (singleEdge (complete V) u₀ v₀ g).defect ℓ = ((Fintype.card V - 2 : ℕ) : ℝ) * ℓ g := by
  rw [defect_singleEdge ℓ ((adj_complete u₀ v₀).mpr huv) g]
  congr 1
  norm_cast
  have hsub : (complete V).triangles.filter (fun t => ({u₀, v₀} : Finset V) ⊆ t) =
      {t ∈ (univ : Finset V).powersetCard 3 | ({u₀, v₀} : Finset V) ⊆ t} := by
    ext t
    simp [mem_triangles_complete, mem_powersetCard]
  rw [hsub, card_filter_powersetCard_subset {u₀, v₀} univ 3 (subset_univ _)
    (by rw [card_pair huv]; decide), card_pair huv, card_univ, Nat.choose_one_right]

/-- Under a conjugation-invariant group norm `ℓ`, the gauge distance of `singleEdge X u₀ v₀ g`
equals `ℓ g` whenever `(u₀, v₀)` belongs to a filled triangle `(u₀, v₀, w)` of `X`. -/
theorem gaugeDist_singleEdge {X : TwoComplex V} {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) {u₀ v₀ w : V}
    (huv : X.Adj u₀ v₀) (hvw : X.Adj v₀ w) (hwu : X.Adj w u₀) (g : G) :
    (singleEdge X u₀ v₀ g).gaugeDist ℓ = ℓ g := by
  have hlo : ℓ g ≤ (singleEdge X u₀ v₀ g).gaugeDist ℓ := by
    simpa [holonomy_singleEdge huv hwu.ne hvw.ne.symm g] using
      (singleEdge X u₀ v₀ g).norm_holonomy_le_gaugeDist hℓ huv hvw hwu
  have hhi : (singleEdge X u₀ v₀ g).gaugeDist ℓ ≤ ℓ g :=
    ((singleEdge X u₀ v₀ g).gaugeDist_le_cost ℓ 1).trans_eq (cost_singleEdge_one ℓ huv g)
  exact le_antisymm hhi hlo

/-- On `complete V` with `3 ≤ Fintype.card V` and a conjugation-invariant group norm `ℓ`, the
gauge distance of `singleEdge (complete V) u₀ v₀ g` (`u₀ ≠ v₀`) equals `ℓ g`. -/
theorem gaugeDist_singleEdge_of_three_le_card {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (hV : 3 ≤ Fintype.card V)
    {u₀ v₀ : V} (huv : u₀ ≠ v₀) (g : G) :
    (singleEdge (complete V) u₀ v₀ g).gaugeDist ℓ = ℓ g := by
  obtain ⟨w, hwu, hwv⟩ := ENat.exists_ne_ne_of_three_le
    (by rw [ENat.card_eq_coe_fintype_card]; exact_mod_cast hV) u₀ v₀
  exact gaugeDist_singleEdge hℓ ((adj_complete u₀ v₀).mpr huv)
    ((adj_complete v₀ w).mpr hwv.symm) ((adj_complete w u₀).mpr hwu) g

end SingleEdge

end Cochain

end TauCeti
