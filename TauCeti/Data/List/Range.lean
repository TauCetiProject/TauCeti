/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Range
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Mapping along a range

Lists of the form `[f (b - 1), …, f 0]`, that is `(List.range b).reverse.map f`, record
coefficient sequences from the top index down. This file peels off the top entry and collapses a
run of vanishing entries at the top into a block of zeros. It also counts the occurrences of a
value in the list `[f s, …, f (s + n - 1)]`, splits the prefixes of a concatenation
`f 0 ++ ⋯ ++ f (n - 1)` of lists, and splits `[f 0, …, f (k + n)]` at its entry `f k`. Finally it
reindexes a list `[g 0, …, g (s - 1)]` cut into three pieces, with a function applied to the
middle piece and an entry inserted after it, as a single list `[g' 0, …, g' s]`.

## Main results

* `List.map_reverse_range_succ`: the list `[f k, …, f 0]` begins with `f k`.
* `List.map_reverse_range_eq_replicate_append`: if `f` vanishes on `[a, b)`, then
  `[f (b - 1), …, f 0]` is `b - a` zeros followed by `[f (a - 1), …, f 0]`.
* `List.count_map_range'`: the list `[f s, …, f (s + n - 1)]` contains `c` once for each
  `j ∈ [s, s + n)` with `f j = c`.
* `List.exists_eq_flatMap_range_append`: a prefix of `f 0 ++ ⋯ ++ f (n - 1)` is
  `f 0 ++ ⋯ ++ f (x - 1)` followed by a prefix of `f x`.
* `List.take_append_map_append_cons_drop_map_range`: cutting `[g 0, …, g (s - 1)]` at `k₀` and
  `k₁`, mapping the middle piece and inserting an entry after it gives `[g' 0, …, g' s]`.
-/

public section

namespace TauCeti

/-- The list `[f k, …, f 0]` begins with `f k`. -/
theorem _root_.List.map_reverse_range_succ {α : Type*} (f : ℕ → α) (k : ℕ) :
    (List.range (k + 1)).reverse.map f = f k :: (List.range k).reverse.map f := by
  simp [List.range_succ]

/-- Mapping a function along the reversed range `[b - 1, …, 0]`, where it vanishes on
`[a, b)`, gives `b - a` zeros followed by the map along `[a - 1, …, 0]`. -/
theorem _root_.List.map_reverse_range_eq_replicate_append {α : Type*} [Zero α] (f : ℕ → α)
    {a b : ℕ} (hab : a ≤ b) (h : ∀ j, a ≤ j → j < b → f j = 0) :
    (List.range b).reverse.map f = List.replicate (b - a) 0 ++ (List.range a).reverse.map f := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hlen : b + 1 - a = (b - a) + 1 := by omega
    rw [List.map_reverse_range_succ, h b hab (by omega), ih fun j h1 h2 => h j h1 (by omega),
      hlen, List.replicate_succ, List.cons_append]

/-- The list `[f s, …, f (s + n - 1)]` contains `c` once for each `j ∈ [s, s + n)` with
`f j = c`. -/
theorem _root_.List.count_map_range' {α : Type*} [DecidableEq α] (f : ℕ → α) (s n : ℕ) (c : α) :
    ((List.range' s n).map f).count c = ((Finset.Ico s (s + n)).filter fun j => f j = c).card := by
  rw [List.count, List.countP_map, List.countP_eq_length_filter, Nat.Ico_eq_range']
  simp [Finset.card, Finset.filter_val, Function.comp_def, beq_eq_decide]

/-- A prefix of the concatenation `f 0 ++ ⋯ ++ f (n - 1)` is `f 0 ++ ⋯ ++ f (x - 1)` followed by
a prefix of `f x`, for some `x`. -/
theorem _root_.List.exists_eq_flatMap_range_append {α : Type*} {f : ℕ → List α} {n : ℕ}
    {p : List α} (hp : p <+: (List.range n).flatMap f) :
    ∃ x q, q <+: f x ∧ p = (List.range x).flatMap f ++ q := by
  induction n generalizing p with
  | zero => exact ⟨0, [], List.nil_prefix, by simpa using hp⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton] at hp
    obtain ⟨t, ht⟩ := hp
    rcases List.append_eq_append_iff.mp ht with ⟨a, ha, -⟩ | ⟨c, hc, hn⟩
    · exact ih ⟨a, ha.symm⟩
    · exact ⟨n, c, ⟨t, hn.symm⟩, hc⟩

/-- The list `[f 0, …, f (k + n)]` is `[f 0, …, f (k - 1)]`, then `f k`, then
`[f (k + 1), …, f (k + n)]`. -/
theorem _root_.List.map_range_add_one_add {α : Type*} (f : ℕ → α) (k n : ℕ) :
    (List.range (k + 1 + n)).map f =
      (List.range k).map f ++ f k :: (List.range n).map fun m ↦ f (k + 1 + m) := by
  rw [List.range_add, List.range_succ, List.map_append, List.map_append, List.map_map]
  simp [Function.comp_def]

/-- Cut `[g 0, …, g (s - 1)]` into `[g 0, …, g (k₀ - 1)]`, `[g k₀, …, g (k₁ - 2)]` and
`[g k₁, …, g (s - 1)]`, replace the entry `g (k₁ - 1)` between the last two pieces by `a`, apply
`r` to the middle piece `[g k₀, …, g (k₁ - 2), a]` and insert `b` after it. The result is
`[g' 0, …, g' s]` for any `g'` listing these entries in order. -/
theorem _root_.List.take_append_map_append_cons_drop_map_range {α : Type*} {g g' : ℕ → α}
    (r : α → α) (a b : α) {s k₀ k₁ : ℕ} (hk₀₁ : k₀ < k₁) (hk₁ : k₁ ≤ s)
    (h₁ : ∀ n < k₀, g' n = g n) (h₂ : ∀ n, k₀ ≤ n → n + 1 < k₁ → g' n = r (g n))
    (h₃ : g' (k₁ - 1) = r a) (h₄ : g' k₁ = b) (h₅ : ∀ n, k₁ < n → n ≤ s → g' n = g (n - 1)) :
    ((List.range s).map g).take k₀ ++
        ((((List.range s).map g).take (k₁ - 1)).drop k₀ ++ [a]).map r ++
        b :: ((List.range s).map g).drop k₁ =
      (List.range (s + 1)).map g' := by
  refine List.ext_getElem (by simp; omega) fun n h h' ↦ ?_
  simp only [List.getElem_append, List.getElem_cons, List.getElem_map, List.getElem_take,
    List.getElem_drop, List.getElem_range, List.length_append, List.length_map, List.length_take,
    List.length_drop, List.length_range, List.length_cons, List.length_nil,
    min_eq_left (by omega : k₀ ≤ s), min_eq_left (by omega : k₁ - 1 ≤ s)]
  split_ifs
  · exact (h₁ n (by omega)).symm
  · rw [h₂ n (by omega) (by omega)]
    congr 2
    omega
  · rw [show n = k₁ - 1 by omega, h₃]
  · exfalso
    omega
  · rw [show n = k₁ by omega, h₄]
  · rw [h₅ n (by omega) (by simp at h'; omega)]
    congr 1
    omega

end TauCeti
