/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.WithTop
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Bounding individual excesses by their total

For finite families in an ordered additive monoid with a top element, termwise lower bounds
with finite sum let one bound each individual excess by the total excess.

## Main results

* `Finset.le_add_of_sum_le_sum_add`: a total excess bound controls each individual excess.

## Provenance

`Finset.le_add_of_sum_le_sum_add` adapts `New.Selmer.le_add_of_sum_le_sum_add` in
`src/New/Congruences/Selmer/RootsOfUnity.lean` in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC), generalizing from extended nonnegative reals to `WithTop Γ`
and from a whole finite type to a finite set.

## References

The argument uses cancellation of finite sums in an ordered additive monoid; no separate
literature source is used.
-/

public section

namespace Finset

/-- If every term of `a` is at least its counterpart in `b`, and the sum of `a` exceeds the
finite sum of `b` by at most `c`, then each individual excess is at most `c`. -/
theorem le_add_of_sum_le_sum_add {ι Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] [AddLeftReflectLE Γ] (s : Finset ι) {a b : ι → WithTop Γ}
    {c : WithTop Γ} (hba : ∀ i ∈ s, b i ≤ a i) (hb : ∑ i ∈ s, b i ≠ ⊤)
    (hsum : ∑ i ∈ s, a i ≤ ∑ i ∈ s, b i + c) (i : ι) (hi : i ∈ s) : a i ≤ b i + c := by
  classical
  have hfin : ∑ k ∈ s.erase i, b k ≠ ⊤ :=
    WithTop.sum_ne_top.2 fun k hk ↦ WithTop.sum_ne_top.1 hb k (mem_erase.1 hk).2
  rw [← sum_erase_add _ _ hi, ← sum_erase_add _ _ hi] at hsum
  have H := (add_le_add (sum_le_sum fun k hk ↦ hba k (mem_erase.1 hk).2) (le_refl (a i))).trans
    hsum
  rw [add_assoc, WithTop.add_le_add_iff_left hfin] at H
  exact H

end Finset
