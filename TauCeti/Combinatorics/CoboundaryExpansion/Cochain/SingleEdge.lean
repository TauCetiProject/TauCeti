/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Basic
import TauCeti.Order.Hom.PowersetCard

/-!
# Single-edge cochain evaluations on the complete complex

Trivial-gauge cost and defect formulas for `TauCeti.Cochain.singleEdge` on
`TauCeti.TwoComplex.complete V`:

* `TauCeti.Cochain.cost_singleEdge_complete_one`: under the trivial gauge `1`, the cost of
  `singleEdge (complete V) u₀ v₀ g` (`u₀ ≠ v₀`) equals `ℓ g`.
* `TauCeti.Cochain.defect_singleEdge`: for any group norm `ℓ`, the defect of
  `singleEdge (complete V) u₀ v₀ g` (`u₀ ≠ v₀`) equals `((Fintype.card V - 2 : ℕ) : ℝ) * ℓ g`.
-/

public section

open Finset

namespace TauCeti

open TwoComplex

namespace Cochain

section SingleEdge

variable {V G : Type*} [Fintype V] [LinearOrder V] [Group G]

/-- Under the trivial gauge `1`, the cost of `singleEdge (complete V) u₀ v₀ g` (`u₀ ≠ v₀`)
equals `ℓ g` for any group norm `ℓ`. -/
theorem cost_singleEdge_complete_one (ℓ : GroupNorm G) {u₀ v₀ : V} (huv : u₀ ≠ v₀) (g : G) :
    (singleEdge (complete V) u₀ v₀ g).cost ℓ 1 = ℓ g := by
  classical
  let a := min u₀ v₀
  let b := max u₀ v₀
  have hab : a < b := min_lt_max.mpr huv
  have hmem : (a, b) ∈ univ.filter fun p : V × V => p.1 < p.2 := by simp [a, b, hab]
  rw [cost_complete, ← sum_erase_add _ _ hmem]
  have hzero :
      ∑ p ∈ (univ.filter fun p : V × V => p.1 < p.2).erase (a, b),
        ℓ (((1 : V → G) p.1)⁻¹ * singleEdge (complete V) u₀ v₀ g p.1 p.2 * (1 : V → G) p.2) =
        0 := by
    refine sum_eq_zero fun ⟨u, v⟩ hp => ?_
    obtain ⟨hne, hflt⟩ := mem_erase.mp hp
    have hlt : u < v := (mem_filter.mp hflt).2
    have h₁ : ¬ (u = u₀ ∧ v = v₀) := by
      rintro ⟨rfl, rfl⟩; exact hne (Prod.ext (min_eq_left hlt.le).symm (max_eq_right hlt.le).symm)
    have h₂ : ¬ (u = v₀ ∧ v = u₀) := by
      rintro ⟨rfl, rfl⟩; exact hne (Prod.ext (min_eq_right hlt.le).symm (max_eq_left hlt.le).symm)
    simp [h₁, h₂]
  have hterm :
      ℓ (((1 : V → G) a)⁻¹ * singleEdge (complete V) u₀ v₀ g a b * (1 : V → G) b) = ℓ g := by
    simp only [Pi.one_apply, inv_one, one_mul, mul_one]
    rcases lt_or_gt_of_ne huv with h | h
    · have ha : a = u₀ := min_eq_left h.le
      have hb : b = v₀ := max_eq_right h.le
      rw [ha, hb, singleEdge_apply_self ((adj_complete u₀ v₀).mpr huv)]
    · have ha : a = v₀ := min_eq_right h.le
      have hb : b = u₀ := max_eq_left h.le
      rw [ha, hb, singleEdge_apply_swap ((adj_complete u₀ v₀).mpr huv), map_inv_eq_map]
  rw [hzero, zero_add, hterm]

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

end SingleEdge

end Cochain

end TauCeti
