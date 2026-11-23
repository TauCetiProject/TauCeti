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
* `TauCeti.Cochain.defect_singleEdge`: on `complete V`, for any group norm `ℓ`, the defect of
  `singleEdge (complete V) u₀ v₀ g` (`u₀ ≠ v₀`) equals `((Fintype.card V - 2 : ℕ) : ℝ) * ℓ g`.
* `TauCeti.Cochain.gaugeDist_singleEdge`, `TauCeti.Cochain.gaugeDist_singleEdge_of_three_le_card`:
  under a conjugation-invariant group norm `ℓ`, the gauge distance of `singleEdge X u₀ v₀ g` equals
  `ℓ g` whenever `(u₀, v₀)` belongs to a filled triangle `(u₀, v₀, w)` of `X`, and in particular on
  `complete V` whenever `3 ≤ Fintype.card V` and `u₀ ≠ v₀`.
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
  rw [cost_def, ← sum_erase_add _ _ hmem]
  have hzero :
      ∑ p ∈ (univ.filter fun p : V × V =>
          p.1 < p.2 ∧ ({p.1, p.2} : Finset V) ∈ X.edges).erase (a, b),
        ℓ (((1 : V → G) p.1)⁻¹ * singleEdge X u₀ v₀ g p.1 p.2 * (1 : V → G) p.2) =
        0 := by
    refine sum_eq_zero fun ⟨u, v⟩ hp => ?_
    obtain ⟨hne, hflt⟩ := mem_erase.mp hp
    have hlt : u < v := (mem_filter.mp hflt).2.1
    have h₁ : ¬ (u = u₀ ∧ v = v₀) := by
      rintro ⟨rfl, rfl⟩; exact hne (Prod.ext (min_eq_left hlt.le).symm (max_eq_right hlt.le).symm)
    have h₂ : ¬ (u = v₀ ∧ v = u₀) := by
      rintro ⟨rfl, rfl⟩; exact hne (Prod.ext (min_eq_right hlt.le).symm (max_eq_left hlt.le).symm)
    simp [h₁, h₂]
  have hterm :
      ℓ (((1 : V → G) a)⁻¹ * singleEdge X u₀ v₀ g a b * (1 : V → G) b) = ℓ g := by
    simp only [Pi.one_apply, inv_one, one_mul, mul_one]
    rcases lt_or_gt_of_ne huv with hlt | hlt
    · have ha : a = u₀ := min_eq_left hlt.le
      have hb : b = v₀ := max_eq_right hlt.le
      rw [ha, hb, singleEdge_apply_self h]
    · have ha : a = v₀ := min_eq_right hlt.le
      have hb : b = u₀ := max_eq_left hlt.le
      rw [ha, hb, singleEdge_apply_swap h, map_inv_eq_map]
  rw [hzero, zero_add, hterm]

/-- Under the trivial gauge `1`, the cost of `singleEdge (complete V) u₀ v₀ g` (`u₀ ≠ v₀`)
equals `ℓ g` for any group norm `ℓ`. -/
theorem cost_singleEdge_complete_one (ℓ : GroupNorm G) {u₀ v₀ : V} (huv : u₀ ≠ v₀) (g : G) :
    (singleEdge (complete V) u₀ v₀ g).cost ℓ 1 = ℓ g :=
  cost_singleEdge_one ℓ ((adj_complete u₀ v₀).mpr huv) g

private theorem holonomy_singleEdge_norm_eq {u₀ v₀ a b c : V} (huv : u₀ ≠ v₀)
    (hab : a < b) (hbc : b < c) (ℓ : GroupNorm G) (g : G) :
    ℓ ((singleEdge (complete V) u₀ v₀ g).holonomy a b c) =
      if ({u₀, v₀} : Finset V) ⊆ {a, b, c} then ℓ g else 0 := by
  classical
  have hadj := (adj_complete u₀ v₀).mpr huv
  split_ifs with hsub
  · have hu : u₀ = a ∨ u₀ = b ∨ u₀ = c := by simpa using hsub (by simp)
    have hv : v₀ = a ∨ v₀ = b ∨ v₀ = c := by simpa using hsub (by simp)
    have hac : a < c := hab.trans hbc
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    all_goals try exact (huv rfl).elim
    all_goals simp [holonomy_def, hadj, hab.ne, hab.ne', hbc.ne, hbc.ne', hac.ne, hac.ne',
      map_inv_eq_map]
  · rw [insert_subset_iff, singleton_subset_iff, not_and_or] at hsub
    have h1 : singleEdge (complete V) u₀ v₀ g a b = 1 :=
      singleEdge_apply_of_ne g (by rintro ⟨rfl, rfl⟩; simp at hsub)
        (by rintro ⟨rfl, rfl⟩; simp at hsub)
    have h2 : singleEdge (complete V) u₀ v₀ g b c = 1 :=
      singleEdge_apply_of_ne g (by rintro ⟨rfl, rfl⟩; simp at hsub)
        (by rintro ⟨rfl, rfl⟩; simp at hsub)
    have h3 : singleEdge (complete V) u₀ v₀ g c a = 1 :=
      singleEdge_apply_of_ne g (by rintro ⟨rfl, rfl⟩; simp at hsub)
        (by rintro ⟨rfl, rfl⟩; simp at hsub)
    simp [holonomy_def, h1, h2, h3]

/-- For any group norm `ℓ` (even without conjugation invariance), the defect of
`singleEdge (complete V) u₀ v₀ g` (`u₀ ≠ v₀`) equals `((Fintype.card V - 2 : ℕ) : ℝ) * ℓ g`. -/
theorem defect_singleEdge (ℓ : GroupNorm G) {u₀ v₀ : V} (huv : u₀ ≠ v₀) (g : G) :
    (singleEdge (complete V) u₀ v₀ g).defect ℓ = ((Fintype.card V - 2 : ℕ) : ℝ) * ℓ g := by
  classical
  rw [defect_complete]
  have hterm :
      ∑ p ∈ univ.filter (fun p : V × V × V => p.1 < p.2.1 ∧ p.2.1 < p.2.2),
        ℓ ((singleEdge (complete V) u₀ v₀ g).holonomy p.1 p.2.1 p.2.2) =
      ∑ p ∈ univ.filter (fun p : V × V × V => p.1 < p.2.1 ∧ p.2.1 < p.2.2),
        if ({u₀, v₀} : Finset V) ⊆ {p.1, p.2.1, p.2.2} then ℓ g else 0 := by
    refine sum_congr rfl fun p hp => ?_
    obtain ⟨h1, h2⟩ := (mem_filter.mp hp).2
    exact holonomy_singleEdge_norm_eq huv h1 h2 ℓ g
  rw [hterm, ← sum_filter, filter_filter, sum_const, nsmul_eq_mul]
  congr 1
  let s : Finset (Finset V) := {t ∈ (univ : Finset V).powersetCard 3 | ({u₀, v₀} : Finset V) ⊆ t}
  have hcard :
      #{p : V × V × V | (p.1 < p.2.1 ∧ p.2.1 < p.2.2) ∧
          ({u₀, v₀} : Finset V) ⊆ {p.1, p.2.1, p.2.2}} = #s := by
    have hflt :
        univ.filter (fun p : V × V × V => (p.1 < p.2.1 ∧ p.2.1 < p.2.2) ∧
            ({u₀, v₀} : Finset V) ⊆ {p.1, p.2.1, p.2.2}) =
          univ.filter (fun p : V × V × V => p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
            ({p.1, p.2.1, p.2.2} : Finset V) ∈ s) := by
      ext ⟨a, b, c⟩
      simp only [s, mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ]
      exact ⟨fun ⟨⟨hab, hbc⟩, hsub⟩ ↦ ⟨hab, hbc,
          ⟨card_eq_three.mpr ⟨a, b, c, hab.ne, (hab.trans hbc).ne, hbc.ne, rfl⟩, hsub⟩⟩,
        fun ⟨hab, hbc, _, hsub⟩ ↦ ⟨⟨hab, hbc⟩, hsub⟩⟩
    rw [hflt]
    exact Set.powersetCard.card_filter_lt_triple_eq_card_of_card_eq_three s
      fun _ ht ↦ (mem_powersetCard.mp (mem_filter.mp ht).1).2
  rw [hcard, card_filter_powersetCard_subset {u₀, v₀} univ 3 (subset_univ _)
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
