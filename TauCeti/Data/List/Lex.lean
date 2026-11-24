/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Lex
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Max

/-!
# Lexicographic order on lists

If every partial sum of a list of positive natural numbers is at most the corresponding partial
sum of a different list, then the first list is lexicographically smaller than the second.

For a linear order `α`, the lexicographic order on `List α` has least element `[]`
(`List.instOrderBot`), and it is dense as soon as `α` has no least element
(`List.instDenselyOrdered`); in particular `(List ℚ, <)` is a dense linear order with least
element `[]`. The parent `l.dropLast` of a nonempty list `l` is definable from the order and the
lengths: it is the unique list `p` of length `l.length - 1` with `p < l` such that every `z` with
`p < z < l` has length at least `l.length` (`List.eq_dropLast_iff`).

## References

* A. Montalbán, *Computable structure theory: within the arithmetic*, author's draft of Part 1
  (2019), Lemma VI.18.
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

/-- Extending the smaller of two lists that is not a prefix of the larger one keeps it smaller. -/
theorem append_lt_of_lt_of_not_prefix {α : Type*} [LT α] {l₁ l₂ l₃ : List α} (h₁ : l₁ < l₂)
    (h₂ : ¬ l₁ <+: l₂) : l₁ ++ l₃ < l₂ := by
  simpa using append_lt_append_of_lt_of_not_prefix (l₃ := l₃) (l₄ := []) h₁ h₂

/-- A list is lexicographically smaller than each of its proper extensions. -/
theorem lt_append_of_ne_nil {α : Type*} [LT α] (l : List α) {m : List α} (hm : m ≠ []) :
    l < l ++ m := by
  simpa using append_left_lt (l₁ := l) (l₂ := []) (nil_lt_iff.2 hm)

/-- A nonempty list is lexicographically larger than its parent `l.dropLast`. -/
theorem dropLast_lt {α : Type*} [LT α] {l : List α} (hl : l ≠ []) : l.dropLast < l := by
  conv_rhs => rw [← dropLast_append_getLast hl]
  exact lt_append_of_ne_nil _ (by simp)

section LinearOrder

variable {α : Type*} [LinearOrder α]

/-- The empty list is the least element of the lexicographic order. -/
instance instOrderBot : OrderBot (List α) where
  bot := []
  bot_le
    | [] => le_rfl
    | _ :: _ => (nil_lt_cons _ _).le

/-- The least element `⊥` of the lexicographic order is the empty list. -/
@[simp]
theorem bot_eq_nil : (⊥ : List α) = [] := rfl

/-- The lexicographic order on lists over a linear order without least element is dense. -/
instance instDenselyOrdered [NoMinOrder α] : DenselyOrdered (List α) where
  dense x y hxy := by
    by_cases hp : x <+: y
    · obtain ⟨t, rfl⟩ := hp
      match t, hxy with
      | [], h => simp at h
      | [b], _ =>
          obtain ⟨c, hc⟩ := exists_lt b
          exact ⟨x ++ [c], lt_append_of_ne_nil x (by simp),
            (append_left_lt_iff x).2 (by simpa [cons_lt_cons_iff] using hc)⟩
      | b :: b' :: t, _ =>
          exact ⟨x ++ [b], lt_append_of_ne_nil x (by simp),
            (append_left_lt_iff x).2 (by simp)⟩
    · obtain ⟨a, x', rfl⟩ : ∃ a x', x = a :: x' :=
        exists_cons_of_ne_nil (by rintro rfl; exact hp nil_prefix)
      exact ⟨a :: x' ++ [a], lt_append_of_ne_nil _ (by simp),
        append_lt_of_lt_of_not_prefix hxy hp⟩

/-- Every list strictly between a nonempty list `l` and its parent `l.dropLast` is at least as
long as `l`. -/
theorem length_le_of_dropLast_lt_of_lt {l z : List α} (h₁ : l.dropLast < z) (h₂ : z < l) :
    l.length ≤ z.length := by
  have hl : l ≠ [] := by rintro rfl; exact List.not_lt.2 (nil_le z) h₂
  by_cases hp : l.dropLast <+: z
  · obtain ⟨t, rfl⟩ := hp
    have ht : t ≠ [] := by rintro rfl; simp at h₁
    have := length_pos_iff.2 ht
    have := length_pos_iff.2 hl
    rw [length_append, length_dropLast]
    omega
  · have := append_lt_of_lt_of_not_prefix (l₃ := [l.getLast hl]) h₁ hp
    rw [dropLast_append_getLast hl] at this
    exact absurd (this.trans h₂) (lt_irrefl l)

/-- The parent `l.dropLast` of a nonempty list `l` is definable from the lexicographic order
and the lengths: it is the unique list `p` of length `l.length - 1` with `p < l` such that every
`z` with `p < z < l` has length at least `l.length`. -/
theorem eq_dropLast_iff {l p : List α} (hl : l ≠ []) :
    p = l.dropLast ↔
      p.length + 1 = l.length ∧ p < l ∧ ∀ z, p < z → z < l → l.length ≤ z.length := by
  have hlen := length_pos_iff.2 hl
  refine ⟨?_, fun ⟨hp, hpl, hz⟩ => ?_⟩
  · rintro rfl
    exact ⟨by rw [length_dropLast]; omega, dropLast_lt hl, fun z => length_le_of_dropLast_lt_of_lt⟩
  · have hlp : p.length = l.dropLast.length := by rw [length_dropLast, ← hp]; omega
    have h := hpl
    rw [← dropLast_append_getLast hl, ← append_nil p,
      append_lt_append_iff_of_length_eq hlp] at h
    rcases h with h | ⟨h, -⟩
    · have := hz _ h (dropLast_lt hl)
      rw [length_dropLast] at this
      omega
    · exact h

end LinearOrder

end List
