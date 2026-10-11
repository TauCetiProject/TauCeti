/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.Order.Preorder.Chain
import Mathlib.Data.Finset.Max

/-!
# Existence of staircase couplings

Two nonnegative finitely supported functions on linear orders with equal total mass admit
nonnegative joint weights supported on a chain in the coordinatewise product order. This is
the barycentric existence argument for the staircase triangulation of a product of simplices.
The index orders are arbitrary, and the coefficients may lie in an ordered additive group
or a monoid with truncated subtraction, such as `ℕ` or `ℝ≥0`. Normalization to mass one is
unnecessary.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2
  (triangulating products of polyhedra).
-/

public section

namespace Finsupp

open Finset

variable {α β R : Type*} [LinearOrder α] [LinearOrder β]
  [AddCommMonoid R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
  [Sub R] [OrderedSub R] [ExistsAddOfLE R]

/-- Nonnegative finite weights of equal total mass have a nonnegative coupling supported
on a staircase. The two `mapDomain` equations specify its marginals. -/
theorem exists_nonneg_isChain_mapDomain (f : α →₀ R) (g : β →₀ R)
    (hf : 0 ≤ f) (hg : 0 ≤ g) (hmass : f.sum (fun _ r => r) = g.sum (fun _ r => r)) :
    ∃ w : (α × β) →₀ R, 0 ≤ w ∧ IsChain (· ≤ ·) (w.support : Set (α × β)) ∧
      mapDomain Prod.fst w = f ∧ mapDomain Prod.snd w = g := by
  classical
  -- Match the least remaining indices, removing the smaller weight. At least one support
  -- shrinks at each step, so induction on the sum of the support cardinalities terminates.
  have aux : ∀ n : ℕ, ∀ (f : α →₀ R) (g : β →₀ R),
      f.support.card + g.support.card = n → 0 ≤ f → 0 ≤ g →
      f.sum (fun _ r => r) = g.sum (fun _ r => r) →
      ∃ w : (α × β) →₀ R, 0 ≤ w ∧ IsChain (· ≤ ·) (w.support : Set (α × β)) ∧
        mapDomain Prod.fst w = f ∧ mapDomain Prod.snd w = g := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f g hn hf hg hmass
      -- Zero mass forces both nonnegative marginals to vanish.
      by_cases hf0 : f = 0
      · have hg0 : g = 0 := by
          by_contra hne
          have hpos := g.sum_pos (g := fun _ r => r) (fun i hi => lt_of_le_of_ne (hg i)
            (mem_support_iff.mp hi).symm) hne
          simp only [hf0, sum_zero_index] at hmass
          exact (ne_of_gt hpos) hmass.symm
        subst f; subst g
        exact ⟨0, le_rfl, by simp, by simp, by simp⟩
      by_cases hg0 : g = 0
      · have hpos := f.sum_pos (g := fun _ r => r) (fun i hi => lt_of_le_of_ne (hf i)
          (mem_support_iff.mp hi).symm) hf0
        simp only [hg0, sum_zero_index] at hmass
        exact False.elim ((ne_of_gt hpos) hmass)
      -- Match the least indices; the residual weights remain nonnegative.
      let a := f.support.min' (support_nonempty_iff.mpr hf0)
      let b := g.support.min' (support_nonempty_iff.mpr hg0)
      have ha : a ∈ f.support := min'_mem _ _
      have hb : b ∈ g.support := min'_mem _ _
      let c := min (f a) (g b)
      let f' := f.update a (f a - c)
      let g' := g.update b (g b - c)
      have hf' : 0 ≤ f' := by
        intro i
        by_cases hi : i = a
        · subst i
          simpa [f'] using (le_tsub_iff_right (min_le_left (f a) (g b))).mpr
            (by simp)
        · simpa [f', update_apply, hi] using hf i
      have hg' : 0 ≤ g' := by
        intro i
        by_cases hi : i = b
        · subst i
          simpa [g'] using (le_tsub_iff_right (min_le_right (f a) (g b))).mpr
            (by simp)
        · simpa [g', update_apply, hi] using hg i
      have hfs : f'.support ⊆ f.support :=
        by simpa [ha] using support_update_subset f a (b := f a - c)
      have hgs : g'.support ⊆ g.support :=
        by simpa [hb] using support_update_subset g b (b := g b - c)
      -- One of the least weights is exhausted, making the induction measure smaller.
      have hcard : f'.support.card + g'.support.card < n := by
        have hfcard := card_le_card hfs
        have hgcard := card_le_card hgs
        rcases le_total (f a) (g b) with hle | hle
        · have hna : a ∉ f'.support := by
            simp [f', c, min_eq_left hle, tsub_eq_of_eq_add (zero_add (f a)).symm]
          have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨hfs, fun h => hna (h.symm ▸ ha)⟩)
          omega
        · have hnb : b ∉ g'.support := by
            simp [g', c, min_eq_right hle, tsub_eq_of_eq_add (zero_add (g b)).symm]
          have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨hgs, fun h => hnb (h.symm ▸ hb)⟩)
          omega
      have hfr : single a c + f' = f := by
        ext i
        by_cases hi : i = a
        · subst i; simp [f', c]
        · simp [f', hi]
      have hgr : single b c + g' = g := by
        ext i
        by_cases hi : i = b
        · subst i; simp [g', c]
        · simp [g', hi]
      have hmass' : f'.sum (fun _ r => r) = g'.sum (fun _ r => r) := by
        rw [← hfr, ← hgr] at hmass
        simpa [sum_add_index] using hmass
      obtain ⟨w, hw, hchain, hwf, hwg⟩ := ih _ hcard f' g' rfl hf' hg' hmass'
      have hws : w.support ⊆ f.support.product g.support := by
        intro p hp
        have hpf : p.1 ∈ f'.support := by
          rw [← hwf, support_mapDomain_of_nonneg hw]
          exact mem_image_of_mem Prod.fst hp
        have hpg : p.2 ∈ g'.support := by
          rw [← hwg, support_mapDomain_of_nonneg hw]
          exact mem_image_of_mem Prod.snd hp
        exact mem_product.mpr ⟨hfs hpf, hgs hpg⟩
      refine ⟨single (a, b) c + w, add_nonneg (single_nonneg.mpr (le_min (hf a) (hg b))) hw,
        ?_, ?_, ?_⟩
      · have hsub : ((single (a, b) c + w).support : Set (α × β)) ⊆
            insert (a, b) (w.support : Set (α × β)) := by
          intro p hp
          rcases mem_union.mp (support_add hp) with hp | hp
          · exact Or.inl (by simpa using support_single_subset hp)
          · exact Or.inr hp
        apply (hchain.insert ?_).mono hsub
        intro p hp _
        have hp' := mem_product.mp (hws hp)
        exact Or.inl ⟨min'_le _ _ hp'.1, min'_le _ _ hp'.2⟩
      · simpa [mapDomain_add, hwf] using hfr
      · simpa [mapDomain_add, hwg] using hgr
  exact aux _ f g rfl hf hg hmass

end Finsupp
