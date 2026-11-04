/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod

/-!
# Counting subsets by intersection size

`Finset.card_filter_powersetCard_card_inter` counts the subsets of a fixed size meeting a
marked set in exactly a prescribed number of points. Splitting a subset into its marked and
unmarked parts gives the product of binomial coefficients used in sampling without replacement.
-/

public section

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- The number of `n`-element subsets of `s` having exactly `k` elements in `t` is the product
of the numbers of choices for the marked and unmarked parts, provided `k ≤ n`. The marked set
need not be contained in the population. -/
theorem card_filter_powersetCard_card_inter (s t : Finset α) {n k : ℕ} (hkn : k ≤ n) :
    #((s.powersetCard n).filter fun u ↦ #(u ∩ t) = k) =
      (#(s ∩ t)).choose k * (#(s \ t)).choose (n - k) := by
  have hcard : #((s.powersetCard n).filter fun u ↦ #(u ∩ t) = k) =
      #((s ∩ t).powersetCard k ×ˢ (s \ t).powersetCard (n - k)) := by
    refine card_nbij' (fun u ↦ (u ∩ t, u \ t)) (fun p ↦ p.1 ∪ p.2) ?_ ?_ ?_ ?_
    · intro u hu
      obtain ⟨⟨hus, hun⟩, hut⟩ := (mem_filter.mp hu).imp_left mem_powersetCard.mp
      apply mem_product.mpr
      simp only [mem_powersetCard]
      refine ⟨⟨inter_subset_inter hus Subset.rfl, hut⟩, ⟨sdiff_subset_sdiff_left t hus, ?_⟩⟩
      have := card_sdiff_add_card_inter u t
      omega
    · rintro ⟨a, b⟩ hp
      obtain ⟨⟨has, hak⟩, ⟨hbs, hbn⟩⟩ :=
        (mem_product.mp hp).imp mem_powersetCard.mp mem_powersetCard.mp
      have hat : a ⊆ t := has.trans inter_subset_right
      have hbt : Disjoint b t := disjoint_of_subset_left hbs sdiff_disjoint
      have hab : Disjoint a b := hbt.symm.mono_left hat
      have hinter : (a ∪ b) ∩ t = a := by
        ext x
        simp only [mem_inter, mem_union]
        grind [disjoint_left.mp hbt]
      apply mem_filter.mpr
      simp only [mem_powersetCard, hinter]
      refine ⟨⟨union_subset (has.trans inter_subset_left) (hbs.trans sdiff_subset), ?_⟩, hak⟩
      rw [card_union_of_disjoint hab, hak, hbn, Nat.add_sub_of_le hkn]
    · intro u _
      simpa only [union_comm] using sdiff_union_inter u t
    · rintro ⟨a, b⟩ hp
      obtain ⟨⟨has, _⟩, ⟨hbs, _⟩⟩ :=
        (mem_product.mp hp).imp mem_powersetCard.mp mem_powersetCard.mp
      have hat : a ⊆ t := has.trans inter_subset_right
      have hbt : Disjoint b t := disjoint_of_subset_left hbs sdiff_disjoint
      apply Prod.ext <;> ext x <;> simp only [mem_inter, mem_union, mem_sdiff] <;>
        grind [disjoint_left.mp hbt]
  simpa only [card_product, card_powersetCard] using hcard

end Finset
