/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.SuccPred.Basic
public import Mathlib.Order.Iterate

/-!
# Comparing iterated successors

In a successor order, `succ^[n] a` is the element `n` steps above `a`. This file compares such
iterates and characterizes membership in the iterated successor orbit
`Set.range (fun n => succ^[n] a)`. Without a maximal element, applying the same number of further
steps preserves and reflects the order, and an element at least `n` steps above `a` lies strictly
above every iterate `succ^[m] a` with `m < n`. An element `b ≥ a` that is none of
`a, succ a, …, succ^[n - 1] a` lies at least `n` steps above `a`; consequently the iterated
successor orbit of `a` is downward closed above `a` and closed under taking predecessors above `a`.

These comparisons measure how far apart two elements of a discrete order are, up to a bound, as in
the Ehrenfeucht–Fraïssé analysis of discrete linear orders.
-/

public section

namespace Order

variable {α : Type*}

section NoMax

variable [Preorder α] [SuccOrder α] [NoMaxOrder α]

/-- If `b` lies at least `n` successor steps above `a`, then fewer than `n` steps above `a` lies
strictly below any number of steps above `b`. -/
theorem succ_iterate_lt_succ_iterate_of_succ_iterate_le {a b : α} {n m : ℕ}
    (h : succ^[n] a ≤ b) (hm : m < n) (k : ℕ) : succ^[m] a < succ^[k] b :=
  ((succ_strictMono.strictMono_iterate_of_lt_map (lt_succ a) hm).trans_le h).trans_le
    (le_succ_iterate k b)

end NoMax

/-- In a linear order without a maximal element, taking `k` further successor steps on both sides
preserves and reflects the order. -/
theorem succ_iterate_add_le_succ_iterate_add_iff [LinearOrder α] [SuccOrder α] [NoMaxOrder α]
    {a b : α} (m n k : ℕ) :
    succ^[m + k] a ≤ succ^[n + k] b ↔ succ^[m] a ≤ succ^[n] b := by
  rw [Nat.add_comm m k, Nat.add_comm n k, Function.iterate_add_apply, Function.iterate_add_apply]
  exact (succ_strictMono.iterate k).le_iff_le

/-- An element `b ≥ a` that is none of `a, succ a, …, succ^[n - 1] a` lies at least `n` successor
steps above `a`. -/
theorem succ_iterate_le_of_forall_ne [PartialOrder α] [SuccOrder α] {a b : α} (hab : a ≤ b)
    {n : ℕ} (hne : ∀ k < n, succ^[k] a ≠ b) : succ^[n] a ≤ b := by
  induction n with
  | zero => exact hab
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact succ_le_of_lt ((ih fun k hk => hne k (by omega)).lt_of_ne (hne n n.lt_succ_self))

/-- For `b ≥ a`, `succ b` lies in the iterated successor range of `a` if and only if `b` does. -/
theorem succ_mem_range_succ_iterate_iff [PartialOrder α] [SuccOrder α] {a b : α}
    (hab : a ≤ b) :
    succ b ∈ Set.range (fun n : ℕ => succ^[n] a) ↔
      b ∈ Set.range (fun n : ℕ => succ^[n] a) := by
  refine ⟨fun ⟨n, hn⟩ => ?_, ?_⟩
  · dsimp only at hn
    by_cases hmax : IsMax b
    · rw [succ_eq_iff_isMax.2 hmax] at hn
      exact ⟨n, hn⟩
    · have hlt : b < succ^[n] a := hn ▸ lt_succ_of_not_isMax hmax
      by_contra hmem
      exact hlt.not_ge (succ_iterate_le_of_forall_ne hab fun k _ hk => hmem ⟨k, hk⟩)
  · rintro ⟨n, rfl⟩
    exact ⟨n + 1, Function.iterate_succ_apply' _ _ _⟩

/-- Every element between `a` and an iterate `succ^[n] a` lies in the iterated successor range
of `a`. -/
theorem mem_range_succ_iterate_of_le [PartialOrder α] [SuccOrder α] {a b : α} {n : ℕ}
    (hab : a ≤ b) (hbn : b ≤ succ^[n] a) :
    b ∈ Set.range (fun k : ℕ => succ^[k] a) := by
  rcases eq_or_lt_of_le hbn with rfl | hlt
  · exact ⟨n, rfl⟩
  · by_contra hmem
    exact hlt.not_ge (succ_iterate_le_of_forall_ne hab fun k _ hk => hmem ⟨k, hk⟩)

/-- The iterated successor range of `a` is downward closed above `a`: if `a ≤ b ≤ c` and `c` lies
in the iterated successor range of `a`, then so does `b`. -/
theorem mem_range_succ_iterate_of_le_of_mem [PartialOrder α] [SuccOrder α] {a b c : α}
    (hab : a ≤ b) (hbc : b ≤ c) (hc : c ∈ Set.range (fun n : ℕ => succ^[n] a)) :
    b ∈ Set.range (fun n : ℕ => succ^[n] a) :=
  let ⟨_, hn⟩ := hc
  mem_range_succ_iterate_of_le hab (hn ▸ hbc)

end Order
