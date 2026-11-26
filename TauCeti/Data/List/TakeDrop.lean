/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TakeDrop

/-!
# Prefixes and suffixes of lists

For `m ≤ n`, the suffix `l.drop m` splits at the position `n` of `l` into the window
`(l.take n).drop m` of the entries `m, …, n - 1` and the suffix `l.drop n`. This is
`List.drop_take_append_drop` with the window written as a suffix of a prefix.

If a predicate `p` holds of an entry whenever it holds of a later one (for instance `· ≤ x` on a
weakly increasing list), the entries satisfying `p` form a prefix of the list: the first
`l.countP p` entries are `l.filter p` (`List.take_countP_eq_filter`), and the remaining ones are
those failing `p` (`List.drop_countP_eq_filter`).
-/

public section

namespace List

variable {α : Type*}

/-- For `m ≤ n`, the suffix `l.drop m` is the window `(l.take n).drop m` followed by the suffix
`l.drop n`. -/
theorem drop_take_append_drop_of_le (l : List α) {m n : ℕ} (h : m ≤ n) :
    (l.take n).drop m ++ l.drop n = l.drop m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp [drop_take]

/-- If `p` holds of an entry whenever it holds of a later one, the entries satisfying `p` are the
first `l.countP p` entries. -/
theorem take_countP_eq_filter {l : List α} {p : α → Bool}
    (h : l.Pairwise fun a b ↦ p b → p a) : l.take (l.countP p) = l.filter p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [pairwise_cons] at h
    by_cases ha : p a
    · simp [ha, ih h.2]
    · have hl : ∀ b ∈ l, ¬p b := fun b hb hpb ↦ ha (h.1 b hb hpb)
      simp [ha, countP_eq_zero.2 hl, filter_eq_nil_iff.2 hl]

/-- If `p` holds of an entry whenever it holds of a later one, the entries after the first
`l.countP p` are the entries failing `p`. -/
theorem drop_countP_eq_filter {l : List α} {p : α → Bool}
    (h : l.Pairwise fun a b ↦ p b → p a) : l.drop (l.countP p) = l.filter (!p ·) := by
  -- The prefix is `l.filter p`, so it carries every entry satisfying `p` and the suffix none.
  have hl := take_append_drop (l.countP p) l
  have hdrop : (l.drop (l.countP p)).countP p = 0 := by
    simpa [countP_filter, take_countP_eq_filter h] using congrArg (countP p) hl
  conv_rhs => rw [← hl, take_countP_eq_filter h, filter_append, filter_filter]
  rw [filter_eq_nil_iff.2 fun _ _ ↦ by simp, nil_append,
    filter_eq_self.2 fun b hb ↦ by simpa using countP_eq_zero.1 hdrop b hb]

end List
