/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Projection to a closed interval away from its endpoints

The projection `Set.projIcc a b h` of a linear order onto `[a, b]` sends every point outside
`[a, b]` to an endpoint. So a point whose projection lies in the open interval `(a, b)` is its own
projection (`Set.eq_of_coe_projIcc_eq`), half-open intervals of projections intersect `[a, b]`
when the left endpoint is at most `b` (`Set.Ioc_projIcc_eq_Ioc_inter`), and taking a minimum with
an upper bound `T ≥ a` commutes with clamping (`Set.min_coe_projIcc_eq`).
-/

public section

namespace Set

variable {α : Type*} [LinearOrder α] {a b s t : α} {h : a ≤ b}

/-- A point whose projection to `[a, b]` is a point `s` of the open interval `(a, b)` is `s`. -/
theorem eq_of_coe_projIcc_eq (hst : (projIcc a b h t : α) = s) (hs : s ∈ Ioo a b) : t = s := by
  have ht : t ∈ Icc a b := by
    refine ⟨not_lt.1 fun ht ↦ hs.1.ne ?_, not_lt.1 fun ht ↦ hs.2.ne' ?_⟩
    · rwa [projIcc_of_le_left _ ht.le] at hst
    · rwa [projIcc_of_right_le _ ht.le] at hst
  rwa [projIcc_of_mem _ ht] at hst

/-- Projecting the endpoints of `(l, r]` onto `[s, t]` produces `(s, t] ∩ (l, r]` when `l ≤ t`. -/
theorem Ioc_projIcc_eq_Ioc_inter {l r : α} (hst : s ≤ t) (hlt : l ≤ t) :
    Ioc (projIcc s t hst l : α) (projIcc s t hst r : α) = Ioc s t ∩ Ioc l r := by
  ext u
  simp only [mem_Ioc, mem_inter_iff, coe_projIcc, min_eq_right hlt, max_lt_iff,
    le_max_iff, le_min_iff]
  constructor
  · rintro ⟨⟨hsu, hlu⟩, h1 | ⟨hut, hur⟩⟩
    · exact absurd h1 hsu.not_ge
    · exact ⟨⟨hsu, hut⟩, ⟨hlu, hur⟩⟩
  · rintro ⟨⟨hsu, hut⟩, ⟨hlu, hur⟩⟩
    exact ⟨⟨hsu, hlu⟩, Or.inr ⟨hut, hur⟩⟩

/-- Truncating the projection onto `[s, t]` at `T ≥ s` equals clamping `min r (min T t)` below at
`s`. -/
theorem min_coe_projIcc_eq {T : α} (hst : s ≤ t) (hsT : s ≤ T) (r : α) :
    min (projIcc s t hst r : α) T = max s (min r (min T t)) := by
  rw [coe_projIcc, min_max_distrib_right, min_eq_left hsT]
  ac_rfl

end Set
