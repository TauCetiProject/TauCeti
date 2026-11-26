/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Minimizers on finite sets

A function on a nonempty finite linearly ordered set has a last minimizer: its value is minimal
on the set and strictly smaller than its value at every later point of the set
(`Finset.exists_last_min_image`). This is the choice of the last vertex of minimal height in the
two-cut construction of Littelmann root operators, used in
`TauCeti.exists_strictly_rising_of_isAChain`.

More generally, any number `n ≤ #s` of points of a finite set `s` can be taken among the smallest
values of a function: some `t ⊆ s` with `n` elements has no value above a value outside it
(`Finset.exists_subset_card_eq_forall_le`).

A point `t` outside a finite set `Z` lies strictly between its neighbours in `Z`, taken in
`WithBot` and `WithTop` so that a missing neighbour is `⊥` or `⊤`; no point of `Z` lies between
`t` and any point of that gap (`Finset.exists_lt_lt_forall_notMem_uIcc`).
-/

public section

namespace Finset

/-- A function on a nonempty finite linearly ordered set attains its minimum at a last point.
Every later point of the set has strictly larger value. -/
theorem exists_last_min_image {α β : Type*} [LinearOrder α] [LinearOrder β]
    (s : Finset α) (f : α → β) (hs : s.Nonempty) :
    ∃ a ∈ s, (∀ b ∈ s, f a ≤ f b) ∧ ∀ b ∈ s, a < b → f a < f b := by
  classical
  obtain ⟨a, ha, hmin⟩ := s.exists_min_image f hs
  let t := s.filter fun b ↦ f b = f a
  have ht : t.Nonempty := ⟨a, mem_filter.mpr ⟨ha, rfl⟩⟩
  have hlast := mem_filter.mp (t.max'_mem ht)
  refine ⟨t.max' ht, hlast.1, ?_, ?_⟩
  · intro b hb
    rw [hlast.2]
    exact hmin b hb
  · intro b hb hab
    rw [hlast.2]
    refine lt_of_le_of_ne (hmin b hb) fun h ↦ ?_
    exact hab.not_ge (t.le_max' b (mem_filter.mpr ⟨hb, h.symm⟩))

/-- Any number `n ≤ #s` of points of `s` can be chosen among the smallest values of `f`: some
`t ⊆ s` with `n` elements has `f a ≤ f b` for every `a ∈ t` and every `b ∈ s` outside `t`. -/
theorem exists_subset_card_eq_forall_le {α β : Type*} [LinearOrder β] (s : Finset α) (f : α → β)
    {n : ℕ} (hn : n ≤ #s) : ∃ t ⊆ s, #t = n ∧ ∀ a ∈ t, ∀ b ∈ s, b ∉ t → f a ≤ f b := by
  classical
  induction n with
  | zero => exact ⟨∅, empty_subset s, card_empty, by simp⟩
  | succ n ih =>
    obtain ⟨t, hts, htn, ht⟩ := ih (Nat.le_of_succ_le hn)
    have hne : (s \ t).Nonempty :=
      sdiff_nonempty.mpr fun h ↦ by have := card_le_card h; omega
    obtain ⟨a, ha, hmin⟩ := (s \ t).exists_min_image f hne
    rw [mem_sdiff] at ha
    refine ⟨insert a t, insert_subset ha.1 hts, by rw [card_insert_of_notMem ha.2, htn], ?_⟩
    intro c hc b hb hbt
    have hbt' : b ∉ t := fun h ↦ hbt (mem_insert_of_mem h)
    rcases mem_insert.mp hc with rfl | hc
    · exact hmin b (mem_sdiff.mpr ⟨hb, hbt'⟩)
    · exact ht c hc b hb hbt'

/-- A point `t` outside a finite set `Z` lies strictly between neighbours `a` and `b` taken from
`Z` together with `⊥` and `⊤` respectively. No point of `Z` lies in `uIcc t u` for any `u`
strictly between `a` and `b`. -/
theorem exists_lt_lt_forall_notMem_uIcc {α : Type*} [LinearOrder α] {Z : Finset α} {t : α}
    (ht : t ∉ Z) :
    ∃ a ∈ insert ⊥ (Z.image (↑)), ∃ b ∈ insert ⊤ (Z.image (↑)),
      a < (t : WithBot α) ∧ (t : WithTop α) < b ∧
        ∀ u : α, a < u → (u : WithTop α) < b → ∀ z ∈ Z, z ∉ Set.uIcc t u := by
  classical
  refine ⟨(Z.filter (· < t)).max, ?_, (Z.filter (t < ·)).min, ?_, ?_, ?_, ?_⟩
  · exact insert_subset_insert _ (image_subset_image (filter_subset _ _))
      (max_mem_insert_bot_image_coe _)
  · exact insert_subset_insert _ (image_subset_image (filter_subset _ _))
      (min_mem_insert_top_image_coe _)
  · rw [max_eq_sup_coe, Finset.sup_lt_iff (WithBot.bot_lt_coe t)]
    simp
  · rw [min_eq_inf_withTop, Finset.lt_inf_iff (WithTop.coe_lt_top t)]
    simp
  · rintro u hau hub z hz
    rcases lt_trichotomy z t with hzt | rfl | hzt
    · exact Set.notMem_uIcc_of_lt hzt
        (WithBot.coe_lt_coe.1 ((le_max (mem_filter.2 ⟨hz, hzt⟩)).trans_lt hau))
    · exact (ht hz).elim
    · exact Set.notMem_uIcc_of_gt hzt
        (WithTop.coe_lt_coe.1 (hub.trans_le (min_le (mem_filter.2 ⟨hz, hzt⟩))))

end Finset
