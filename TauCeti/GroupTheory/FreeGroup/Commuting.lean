/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Center
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Commuting elements of a free group

Mathlib characterizes commuting pairs in a free group as integer powers of a common element.
This file derives a parity consequence used in group algebraic geometry: for two commuting
elements, one of the two elements or their product is a square.
-/

public section

namespace IsFreeGroup

variable {G : Type*} [Group G] [IsFreeGroup G]

/-- For commuting elements `x` and `y` of a free group, one of `x`, `y` and `x * y` is a
square. -/
theorem exists_eq_sq_of_commute {x y : G} (h : Commute x y) :
    ∃ z : G, x = z ^ 2 ∨ y = z ^ 2 ∨ x * y = z ^ 2 := by
  obtain ⟨r, m, n, rfl, rfl⟩ := commute_iff_exists_zpow.1 h
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Int.even_or_odd m
  · exact ⟨r ^ k, .inl (by rw [pow_two, ← zpow_add])⟩
  obtain ⟨l, rfl⟩ | ⟨l, rfl⟩ := Int.even_or_odd n
  · exact ⟨r ^ l, .inr (.inl (by rw [pow_two, ← zpow_add]))⟩
  · refine ⟨r ^ (k + l + 1), .inr (.inr ?_)⟩
    rw [pow_two, ← zpow_add, ← zpow_add]
    congr 1
    omega

end IsFreeGroup
