/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Infix

/-!
# The length of the longest common prefix of two lists

`List.commonPrefixLength l₁ l₂` is the length of the longest list that is a prefix of both `l₁`
and `l₂`. It is characterized by `List.le_commonPrefixLength_iff`: a number `n` is at most the
common prefix length exactly when the first `n` entries of the two lists exist and agree.

Common prefix lengths satisfy the ultrametric inequality
`min (commonPrefixLength l₁ l₂) (commonPrefixLength l₂ l₃) ≤ commonPrefixLength l₁ l₃`.
For reduced words in a free group, the common prefix length is the Gromov product of word
length, and this inequality is what makes word length a Lyndon length function.
-/

public section

namespace List

variable {α : Type*} [DecidableEq α]

/-- The length of the longest common prefix of two lists. -/
def commonPrefixLength : List α → List α → ℕ
  | a :: l₁, b :: l₂ => if a = b then commonPrefixLength l₁ l₂ + 1 else 0
  | _, _ => 0

@[simp]
theorem commonPrefixLength_nil_left (l : List α) : commonPrefixLength [] l = 0 := by
  cases l <;> rfl

@[simp]
theorem commonPrefixLength_nil_right (l : List α) : commonPrefixLength l [] = 0 := by
  cases l <;> rfl

@[simp]
theorem commonPrefixLength_cons_cons (a b : α) (l₁ l₂ : List α) :
    commonPrefixLength (a :: l₁) (b :: l₂) =
      if a = b then commonPrefixLength l₁ l₂ + 1 else 0 := by
  rw [commonPrefixLength]

/-- A number `n` is at most the common prefix length of two lists exactly when both lists have at
least `n` entries and their first `n` entries agree. -/
theorem le_commonPrefixLength_iff {l₁ l₂ : List α} {n : ℕ} :
    n ≤ commonPrefixLength l₁ l₂ ↔
      n ≤ l₁.length ∧ n ≤ l₂.length ∧ l₁.take n = l₂.take n := by
  induction l₁ generalizing l₂ n with
  | nil =>
    refine ⟨fun h => ?_, fun h => h.1.trans_eq length_nil⟩
    obtain rfl : n = 0 := by simpa using h
    simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil =>
      refine ⟨fun h => ?_, fun h => h.2.1.trans_eq length_nil⟩
      obtain rfl : n = 0 := by simpa using h
      simp
    | cons b l₂ =>
      cases n with
      | zero => simp
      | succ n =>
        by_cases hab : a = b
        · simp [hab, ih]
        · simp [hab]

theorem commonPrefixLength_comm (l₁ l₂ : List α) :
    commonPrefixLength l₁ l₂ = commonPrefixLength l₂ l₁ :=
  le_antisymm (le_commonPrefixLength_iff.2 <| by
      obtain ⟨h₁, h₂, h⟩ := le_commonPrefixLength_iff.1 (le_refl (commonPrefixLength l₁ l₂))
      exact ⟨h₂, h₁, h.symm⟩)
    (le_commonPrefixLength_iff.2 <| by
      obtain ⟨h₁, h₂, h⟩ := le_commonPrefixLength_iff.1 (le_refl (commonPrefixLength l₂ l₁))
      exact ⟨h₂, h₁, h.symm⟩)

@[simp]
theorem commonPrefixLength_self (l : List α) : commonPrefixLength l l = l.length :=
  le_antisymm (le_commonPrefixLength_iff.1 le_rfl).1
    (le_commonPrefixLength_iff.2 ⟨le_rfl, le_rfl, rfl⟩)

theorem commonPrefixLength_le_length_left (l₁ l₂ : List α) :
    commonPrefixLength l₁ l₂ ≤ l₁.length :=
  (le_commonPrefixLength_iff.1 le_rfl).1

theorem commonPrefixLength_le_length_right (l₁ l₂ : List α) :
    commonPrefixLength l₁ l₂ ≤ l₂.length :=
  (le_commonPrefixLength_iff.1 le_rfl).2.1

/-- The two lists agree up to their common prefix length. -/
theorem take_commonPrefixLength_eq (l₁ l₂ : List α) :
    l₁.take (commonPrefixLength l₁ l₂) = l₂.take (commonPrefixLength l₁ l₂) :=
  (le_commonPrefixLength_iff.1 le_rfl).2.2

/-- The ultrametric inequality for common prefix lengths. -/
theorem min_commonPrefixLength_le (l₁ l₂ l₃ : List α) :
    min (commonPrefixLength l₁ l₂) (commonPrefixLength l₂ l₃) ≤ commonPrefixLength l₁ l₃ := by
  obtain ⟨h₁, -, h₁₂⟩ := le_commonPrefixLength_iff.1 (min_le_left (commonPrefixLength l₁ l₂)
    (commonPrefixLength l₂ l₃))
  obtain ⟨-, h₃, h₂₃⟩ := le_commonPrefixLength_iff.1 (min_le_right (commonPrefixLength l₁ l₂)
    (commonPrefixLength l₂ l₃))
  exact le_commonPrefixLength_iff.2 ⟨h₁, h₃, h₁₂.trans h₂₃⟩

end List
