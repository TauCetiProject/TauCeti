/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Absolute-value bounds for finset sums

In a lattice-ordered additive commutative group, a sum of `#s` terms, each bounded by `B` in
absolute value, is bounded by `#s • B` in absolute value. This is the crude estimate used when a
bound on each term of a finite average or a counting sum is summed over the index set.

## Main results

* `Finset.abs_sum_le_card_nsmul`: `|∑ i ∈ s, f i| ≤ #s • B` when `|f i| ≤ B` for every `i ∈ s`.
-/

public section

namespace Finset

variable {ι R : Type*} [AddCommGroup R] [Lattice R] [IsOrderedAddMonoid R]

/-- A sum of terms with absolute value at most `B` has absolute value at most `#s • B`. -/
theorem abs_sum_le_card_nsmul {s : Finset ι} {f : ι → R} {B : R} (h : ∀ i ∈ s, |f i| ≤ B) :
    |∑ i ∈ s, f i| ≤ #s • B :=
  -- the triangle inequality `|∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i|`, valid in any lattice-ordered group
  (le_sum_of_subadditive _ abs_zero.le abs_add_le s f).trans <| sum_le_card_nsmul s _ B h

end Finset
