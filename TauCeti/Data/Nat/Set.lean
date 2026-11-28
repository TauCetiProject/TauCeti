/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Set

/-!
# Sets of natural numbers

The successor function misses exactly `0`: `(Set.range Nat.succ)ᶜ = {0}`
(`Nat.compl_range_succ`), the complement form of Mathlib's `Nat.zero_union_range_succ`.
The lemma `Nat.forall_ge_succ_iff` shifts a universal quantifier over a tail of the naturals
using `Nat.and_forall_add_one`.
-/

public section

namespace Nat

/-- The successor function misses exactly `0`. -/
theorem compl_range_succ : (Set.range succ)ᶜ = {0} := by
  ext n
  cases n <;> simp

/-- A predicate holds from `n + 1` onward if its successor shift holds from `n` onward. -/
theorem forall_ge_succ_iff (n : ℕ) (p : ℕ → Prop) :
    (∀ i, n + 1 ≤ i → p i) ↔ ∀ i, n ≤ i → p (i + 1) := by
  rw [← Nat.and_forall_add_one (p := fun i ↦ n + 1 ≤ i → p i)]
  have hn : ¬ n + 1 ≤ 0 := by omega
  simp only [hn, false_implies, true_and, Nat.succ_le_succ_iff]

end Nat
