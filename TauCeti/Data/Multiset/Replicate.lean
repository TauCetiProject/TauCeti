/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Finite sums of replicated multisets

Given a finite set `s : Finset α` and a multiplicity function `f : α → ℕ`, the finite sum
`∑ a ∈ s, Multiset.replicate (f a) a` builds the multiset with support contained in `s` in which
each `a ∈ s` occurs with multiplicity `f a`. This arises whenever a divisor, zero multiset, or
weighted collection of points is specified on a finite set with prescribed multiplicities.

## Main results

* `Multiset.mem_sum_replicate`: an element `b` belongs to `∑ a ∈ s, replicate (f a) a` if and only
  if `b ∈ s` and `f b ≠ 0`.
* `Multiset.count_sum_replicate`: the multiplicity of `b` in `∑ a ∈ s, replicate (f a) a` is
  `f b` when `b ∈ s` and `0` otherwise.
-/

public section

namespace Multiset

variable {α : Type*}

-- Not `@[simp]`: `Multiset.mem_sum` already simplifies the LHS, so `simpNF` rejects it.
/-- An element `b` belongs to `∑ a ∈ s, replicate (f a) a` if and only if `b ∈ s` and
`f b ≠ 0`. -/
theorem mem_sum_replicate {s : Finset α} {f : α → ℕ} {b : α} :
    b ∈ ∑ a ∈ s, replicate (f a) a ↔ b ∈ s ∧ f b ≠ 0 := by
  simp [mem_replicate]

/-- The multiplicity of `b` in `∑ a ∈ s, replicate (f a) a` is `f b` when `b ∈ s` and `0`
otherwise. -/
@[simp]
theorem count_sum_replicate [DecidableEq α] (s : Finset α) (f : α → ℕ) (b : α) :
    (∑ a ∈ s, replicate (f a) a).count b = if b ∈ s then f b else 0 := by
  simp [count_sum', count_replicate]

end Multiset
