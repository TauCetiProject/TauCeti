/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Basic

/-!
# Splitting a list at matches of a Boolean predicate

A list with at least one entry satisfying a Boolean predicate `p` splits at the first such entry
(`List.exists_split_of_countP_pos`), and a list with at least two such entries splits at its first
two matches (`List.exists_two_split_of_two_le_countP`).
-/

public section

namespace List

/-- A list in which at least one entry satisfies `p` splits at its first matching entry. -/
theorem exists_split_of_countP_pos {α : Type*} {p : α → Bool} {l : List α} (h : 0 < l.countP p) :
    ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ p a = true ∧ l₁.countP p = 0 := by
  have ⟨x, hx, hpx⟩ := List.countP_pos_iff.1 h
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (List.find?_eq_none.not.2 fun h => h x hx hpx)
  obtain ⟨hpa, l₁, l₂, rfl, hl₁⟩ := List.find?_eq_some_iff_append.1 ha
  exact ⟨l₁, a, l₂, rfl, hpa, List.countP_eq_zero.2 fun y hy => by simpa using hl₁ y hy⟩

/-- A list in which at least two entries satisfy `p` splits at its first two matching entries. -/
theorem exists_two_split_of_two_le_countP {α : Type*} {p : α → Bool} {l : List α}
    (h : 2 ≤ l.countP p) :
    ∃ l₁ a₁ l₂ a₂ l₃, l = l₁ ++ a₁ :: (l₂ ++ a₂ :: l₃) ∧
      p a₁ = true ∧ p a₂ = true ∧ l₁.countP p = 0 ∧ l₂.countP p = 0 := by
  obtain ⟨l₁, a₁, rest, rfl, ha₁, h₁⟩ := exists_split_of_countP_pos (by omega : 0 < l.countP p)
  have hrest : 0 < rest.countP p := by
    rw [countP_append, countP_cons, h₁, ha₁] at h
    simp only [ite_true] at h
    omega
  obtain ⟨l₂, a₂, l₃, rfl, ha₂, h₂⟩ := exists_split_of_countP_pos hrest
  exact ⟨l₁, a₁, l₂, a₂, l₃, rfl, ha₁, ha₂, h₁, h₂⟩

end List
