/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Northcott
public import Mathlib.Data.Set.Finite.Basic

/-!
# Sequences of rapidly growing value for a Northcott function

If `h` is Northcott, an infinite set contains elements of arbitrarily large `h`-value, because
each sublevel set `{a | h a ≤ b}` is finite. Iterating this, one chooses a sequence in the set
whose values exceed a given bound and grow at least as fast as any prescribed rule
`b ↦ f b`.

For a height on a number field, such as `Height.logHeight₁` on `ℚ`, this is how the proof of
Roth's theorem selects good rational approximations of rapidly increasing heights from an
infinite set of them: one takes `f b = M * b`.

## Main results

* `Northcott.exists_mem_lt`: an infinite set contains elements of arbitrarily large `h`-value.
* `Northcott.exists_seq_mem_lt`: an infinite set contains a sequence with
  `b < h (x 0)` and `f (h (x k)) < h (x (k + 1))` for every `k`.

## References

* L. Pottmeyer, [*Diophantine Approximation*](https://esaga.uni-due.de/f/lukas.pottmeyer/DioApp.pdf)
  (2022), §3.5.
-/

public section

namespace Northcott

variable {α β : Type*} [LinearOrder β] (h : α → β) [Northcott h]

/-- An infinite set contains elements of arbitrarily large value under a Northcott function. -/
theorem exists_mem_lt {s : Set α} (hs : s.Infinite) (b : β) : ∃ a ∈ s, b < h a := by
  obtain ⟨a, has, hab⟩ := (hs.sdiff (finite_le (h := h) b)).nonempty
  exact ⟨a, has, lt_of_not_ge hab⟩

/-- An infinite set contains a sequence whose first value under a Northcott function `h`
exceeds `b`, and each of whose values exceeds `f` applied to the previous one. -/
theorem exists_seq_mem_lt (f : β → β) {s : Set α} (hs : s.Infinite) (b : β) :
    ∃ x : ℕ → α, (∀ k, x k ∈ s) ∧ b < h (x 0) ∧ ∀ k, f (h (x k)) < h (x (k + 1)) := by
  choose g hgs hg using exists_mem_lt h hs
  let x : ℕ → α := fun k ↦ Nat.rec (g b) (fun _ a ↦ g (f (h a))) k
  refine ⟨x, fun k ↦ ?_, hg b, fun k ↦ hg _⟩
  cases k <;> exact hgs _

end Northcott
