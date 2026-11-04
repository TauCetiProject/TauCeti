/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Basic

/-!
# Replacing three consecutive entries of a list

The lists `u ++ a :: b :: c :: v` and `u ++ a' :: b' :: c' :: v` differ at most in the three
positions `u.length`, `u.length + 1` and `u.length + 2`, and agree at every other position.
-/

public section

namespace List

variable {α : Type*}

/-- Two lists which differ only in the three entries following `u` have the same entry at every
other position. -/
theorem getElem?_append_cons_cons_cons_of_ne (u v : List α) (a b c a' b' c' : α) {k : ℕ}
    (h₀ : k ≠ u.length) (h₁ : k ≠ u.length + 1) (h₂ : k ≠ u.length + 2) :
    (u ++ a :: b :: c :: v)[k]? = (u ++ a' :: b' :: c' :: v)[k]? := by
  rcases Nat.lt_or_ge k u.length with hk | hk
  · rw [getElem?_append_left hk, getElem?_append_left hk]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [getElem?_append_right hk, getElem?_append_right hk, Nat.add_sub_cancel_left]
    match m, h₀, h₁, h₂ with
    | m + 3, _, _, _ => simp

end List
