/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.WellFoundedSet

/-!
# Partially well-ordered sets from finiteness below each element

In a linear order, a set which has only finitely many elements below each of its elements is
partially well-ordered. This is how supports of series which are finite below every cutoff, such
as Novikov series, become supports of Hahn series.

## Main results

* `Set.IsPWO.of_finite_inter_Iic`: a set of a linear order meeting each `Iic a`, for `a` in the
  set, in a finite set is partially well-ordered.
-/

public section

namespace Set

variable {α : Type*} [LinearOrder α] {s : Set α}

/-- In a linear order, a set with only finitely many elements below each of its elements is
partially well-ordered. -/
theorem IsPWO.of_finite_inter_Iic (hs : ∀ a ∈ s, (s ∩ Iic a).Finite) : s.IsPWO := by
  rw [IsPWO, partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  by_cases h : ∃ n, 0 < n ∧ f 0 ≤ f n
  · obtain ⟨n, hn, h⟩ := h
    exact ⟨0, n, hn, h⟩
  push Not at h
  -- Otherwise the whole sequence stays below `f 0`, in a finite set, so it repeats a value.
  have hmem (n : ℕ) : f n ∈ s ∩ Iic (f 0) := by
    refine ⟨hf n, ?_⟩
    rcases n.eq_zero_or_pos with rfl | hn
    · exact le_rfl
    · exact (h n hn).le
  obtain ⟨m, n, hmn, hfmn⟩ := (hs (f 0) (hf 0)).exists_lt_map_eq_of_forall_mem hmem
  exact ⟨m, n, hmn, hfmn.le⟩

end Set
