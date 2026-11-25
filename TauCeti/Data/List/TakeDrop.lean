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

For every function `f` from lists to entries and every length `n` there is a list of length `n`
whose entries are the values of `f` at the lists of the earlier entries
(`List.exists_length_eq_forall_getElem_eq`). Given an order on the entries, a property that holds
for all lists `k :: q` with `k` large and `q` dominating, entry by entry, a bound depending on `k`
holds for all lists dominating one bound along their prefixes (`List.exists_bound_of_forall_cons`).

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

/-- For every function `f` from lists to entries and every length `n` there is a list of length
`n` in which each entry is the value of `f` at the list of the earlier entries. -/
theorem exists_length_eq_forall_getElem_eq (f : List α → α) (n : ℕ) :
    ∃ p : List α, p.length = n ∧ ∀ i (hi : i < p.length), p[i] = f (p.take i) := by
  induction n with
  | zero => exact ⟨[], rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨p, hp, hf⟩ := ih
    refine ⟨p ++ [f p], by simp [hp], fun i hi => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 (by simpa using hi)) with hi' | rfl
    · simpa [take_append_of_le_length (Nat.le_of_lt hi'), getElem_append_left hi'] using hf i hi'
    · simp

/-- A property of the lists of length `L + 1` holds for all lists dominating some bound function
`N` along their prefixes (each entry at least `N` of the list of the earlier entries) if, for every
first entry `k ≥ K`, it holds for the lists `k :: q` with `q` dominating some bound function
depending on `k`. -/
theorem exists_bound_of_forall_cons [LE α] {P : List α → Prop} {L : ℕ} (K : α)
    (h : ∀ k, K ≤ k → ∃ N : List α → α, ∀ q : List α, q.length = L →
      (∀ i (hi : i < q.length), N (q.take i) ≤ q[i]) → P (k :: q)) :
    ∃ N : List α → α, ∀ p : List α, p.length = L + 1 →
      (∀ i (hi : i < p.length), N (p.take i) ≤ p[i]) → P p := by
  have h' (k : α) : ∃ N : List α → α, K ≤ k → ∀ q : List α, q.length = L →
      (∀ i (hi : i < q.length), N (q.take i) ≤ q[i]) → P (k :: q) := by
    by_cases hk : K ≤ k
    · obtain ⟨N, hN⟩ := h k hk
      exact ⟨N, fun _ => hN⟩
    · exact ⟨fun _ => K, fun h => absurd h hk⟩
  choose N hN using h'
  refine ⟨fun | [] => K | k :: q => N k q, ?_⟩
  rintro (_ | ⟨k, q⟩) hp hdom
  · simp at hp
  · exact hN k (hdom 0 (by simp)) q (by simpa using hp) fun i hi => hdom (i + 1) (by simpa)

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
