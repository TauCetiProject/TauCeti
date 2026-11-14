/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Absolute-value bounds for multiset sums

For a multiset in a linearly ordered additive commutative group, bounding each element in absolute
value by `B` bounds the absolute value of the sum by `s.card • B`. These are the `Multiset`
counterparts of `Finset.abs_sum_le_card_nsmul`
(`TauCeti/Algebra/Order/BigOperators/Sum/UnitWeights.lean`).

## Main results

* `Multiset.abs_sum_le_card_nsmul`: `|s.sum| ≤ s.card • B` when `∀ x ∈ s, |x| ≤ B`.
* `Multiset.abs_sum_map_le_card_nsmul`: mapped variant `|(s.map f).sum| ≤ s.card • B`.
-/

public section

namespace Multiset

variable {ι R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]

/-- If every element of `s` has absolute value at most `B`, then `|s.sum| ≤ s.card • B`. -/
theorem abs_sum_le_card_nsmul (s : Multiset R) {B : R} (h : ∀ x ∈ s, |x| ≤ B) :
    |s.sum| ≤ s.card • B :=
  abs_sum_le_sum_abs.trans <| by
    simpa using sum_le_card_nsmul (s.map abs) B (by simpa using h)

/-- Mapped form of `Multiset.abs_sum_le_card_nsmul`: if `|f x| ≤ B` for every `x ∈ s`, then
`|(s.map f).sum| ≤ s.card • B`. -/
theorem abs_sum_map_le_card_nsmul (s : Multiset ι) (f : ι → R) {B : R}
    (h : ∀ x ∈ s, |f x| ≤ B) : |(s.map f).sum| ≤ s.card • B := by
  simpa using abs_sum_le_card_nsmul (s.map f) (by simpa using h)

end Multiset
