/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Multiset

/-!
# Multisets of exponent vectors with unit steps

Mathlib's `Finsupp.toMultiset` sends an exponent vector `e : α →₀ ℕ` to the multiset in which
each `a` occurs `e a` times. This file computes it on exponent vectors built from unit steps
`Finsupp.single a 1`: adding one unit step conses its index, and a sum of unit steps along a
finite family is the multiset of values of the family.

## Main results

* `Finsupp.toMultiset_add_single_one`: `toMultiset (e + single a 1) = a ::ₘ toMultiset e`.
* `Finsupp.toMultiset_sum_single_one`: `toMultiset (∑ i ∈ s, single (p i) 1) = s.val.map p`.
-/

public section

namespace Finsupp

/-- Adding one unit step at `a` to an exponent vector conses `a` onto its multiset. -/
theorem toMultiset_add_single_one {α : Type*} (e : α →₀ ℕ) (a : α) :
    toMultiset (e + single a 1) = a ::ₘ toMultiset e := by
  simp [toMultiset_add, add_comm, one_nsmul]

/-- The multiset of a sum of unit steps along a family `p` indexed by a finset `s` is the
multiset of the values of `p` on `s`. -/
theorem toMultiset_sum_single_one {α ι : Type*} (s : Finset ι) (p : ι → α) :
    toMultiset (∑ i ∈ s, single (p i) 1) = s.val.map p := by
  simpa [toMultiset_sum, one_nsmul, Finset.sum_map_val] using
    Multiset.sum_map_singleton (s.val.map p)

end Finsupp
