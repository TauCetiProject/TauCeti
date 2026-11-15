/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Max

/-!
# Last minimizers on finite sets

A function on a nonempty finite linearly ordered set has a last minimizer: its value is minimal
on the set and strictly smaller than its value at every later point of the set.

This is the choice of the last vertex of minimal height in the two-cut construction of
Littelmann root operators, used in `TauCeti.exists_strictly_rising_of_isAChain`.
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

end Finset
