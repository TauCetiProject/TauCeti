/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Fin.Basic

/-!
# Steps of a tuple across a value

Read a tuple `f : Fin (k + 1) → α` in a linear order as the path `f 0 → f 1 → ⋯ → f k`. If the
path starts at or below `c` and ends above `c`, one of its steps crosses `c`: some `l : Fin k`
has `f l.castSucc ≤ c < f l.succ` (`Fin.exists_castSucc_le_and_lt_succ`). Along a monotone path
at most one step crosses `c` (`Monotone.eq_of_castSucc_le_and_lt_succ`). So such a path either has
a decreasing step or crosses `c` in exactly one step
(`Fin.exists_succ_lt_castSucc_or_existsUnique_castSucc_le_and_lt_succ`).

A nondecreasing path `0 = x₀ ≤ x₁ ≤ ⋯ ≤ xₖ = n` cuts a tuple `a₁, …, aₙ` into the consecutive,
possibly empty, blocks between the `xⱼ`; these two statements say that each input lies in
exactly one block.
-/

public section

namespace Fin

/-- **A path across `c` has a step across `c`.** A tuple `f : Fin (k + 1) → α` with
`f 0 ≤ c < f (last k)` has a step `l` with `f l.castSucc ≤ c < f l.succ`. -/
theorem exists_castSucc_le_and_lt_succ {α : Type*} [LinearOrder α] {k : ℕ}
    (f : Fin (k + 1) → α) {c : α} (h0 : f 0 ≤ c) (hk : c < f (last k)) :
    ∃ l : Fin k, f l.castSucc ≤ c ∧ c < f l.succ := by
  induction k with
  | zero => exact absurd (h0.trans_lt hk) (lt_irrefl _)
  | succ k ih =>
    by_cases h : c < f (last k).castSucc
    · obtain ⟨l, hl⟩ := ih (f ∘ castSucc) h0 h
      exact ⟨l.castSucc, by rw [succ_castSucc]; exact hl⟩
    · exact ⟨last k, not_lt.mp h, by simpa using hk⟩

end Fin

/-- **Along a monotone path at most one step crosses `c`.** -/
theorem Monotone.eq_of_castSucc_le_and_lt_succ {α : Type*} [Preorder α] {k : ℕ}
    {f : Fin (k + 1) → α} (hf : Monotone f) {c : α} {l l' : Fin k}
    (h : f l.castSucc ≤ c ∧ c < f l.succ) (h' : f l'.castSucc ≤ c ∧ c < f l'.succ) : l = l' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact lt_irrefl c ((h.2.trans_le (hf (Fin.succ_le_castSucc_iff.mpr hlt))).trans_le h'.1)
  · exact lt_irrefl c ((h'.2.trans_le (hf (Fin.succ_le_castSucc_iff.mpr hlt))).trans_le h.1)

namespace Fin

/-- **A path across `c` either has a decreasing step or crosses `c` in exactly one step.** A
tuple `f : Fin (k + 1) → α` with `f 0 ≤ c < f (last k)` either has a step `l` with
`f l.succ < f l.castSucc`, or has exactly one step `l` with `f l.castSucc ≤ c < f l.succ`. -/
theorem exists_succ_lt_castSucc_or_existsUnique_castSucc_le_and_lt_succ {α : Type*}
    [LinearOrder α] {k : ℕ} (f : Fin (k + 1) → α) {c : α} (h0 : f 0 ≤ c) (hk : c < f (last k)) :
    (∃ l : Fin k, f l.succ < f l.castSucc) ∨ ∃! l : Fin k, f l.castSucc ≤ c ∧ c < f l.succ := by
  by_cases hdec : ∃ l : Fin k, f l.succ < f l.castSucc
  · exact Or.inl hdec
  · push Not at hdec
    obtain ⟨l, hl⟩ := exists_castSucc_le_and_lt_succ f h0 hk
    exact Or.inr ⟨l, hl, fun l' hl' =>
      (monotone_iff_le_succ.mpr hdec).eq_of_castSucc_le_and_lt_succ hl' hl⟩

end Fin
