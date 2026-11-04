/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Lex

/-!
# Lexicographic comparison from partial sums

If every partial sum of a list of positive natural numbers is at most the corresponding partial
sum of a different list, then the first list is lexicographically smaller than the second.
-/

public section

namespace List

/-- If every partial sum of `l₂` is at most the corresponding partial sum of `l₁`, the entries
of `l₂` are positive and the lists differ, then `l₂` is lexicographically smaller than `l₁`. -/
theorem lex_lt_of_sum_take_le {l₁ l₂ : List ℕ} (hpos : ∀ i ∈ l₂, 0 < i)
    (hle : ∀ k : ℕ, (l₂.take k).sum ≤ (l₁.take k).sum) (hne : l₁ ≠ l₂) : l₂ < l₁ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => exact absurd rfl hne
      | cons b l₂ =>
          have hb := hpos b (by simp)
          have := hle 1
          simp only [take_succ_cons, take_zero, sum_cons, sum_nil, take_nil] at this
          omega
  | cons a l₁ ih =>
      cases l₂ with
      | nil => exact Lex.nil
      | cons b l₂ =>
          have hba : b ≤ a := by simpa using hle 1
          rcases hba.eq_or_lt with rfl | hba
          · exact Lex.cons <| ih (fun i hi => hpos i (by simp [hi]))
              (fun k => by simpa using hle (k + 1)) (by simpa using hne)
          · exact Lex.rel hba

end List
