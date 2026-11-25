/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Gaps between prefix products

In a canonically ordered monoid, prefix products `(L.take k).prod` grow with `k`
(`List.monotone_prod_take`). If every entry of `L` is at least `c`, then a later prefix product
exceeds an earlier one by a factor of at least `c`, as long as the earlier prefix stops before
the end of the list: `List.prod_take_mul_le_prod_take`, and additively
`List.sum_take_add_le_sum_take`.
-/

public section

namespace List

variable {M : Type*} [Monoid M] [Preorder M] [MulLeftMono M] [CanonicallyOrderedMul M]

/-- If every entry of `L` is at least `c`, then for `j < k` with `j < L.length` the prefix
product `(L.take k).prod` is at least `(L.take j).prod * c`. -/
@[to_additive /-- If every entry of `L` is at least `c`, then for `j < k` with `j < L.length`
the prefix sum `(L.take k).sum` is at least `(L.take j).sum + c`. -/]
theorem prod_take_mul_le_prod_take {L : List M} {c : M} (h : ∀ a ∈ L, c ≤ a) {j k : ℕ}
    (hjk : j < k) (hj : j < L.length) : (L.take j).prod * c ≤ (L.take k).prod :=
  calc (L.take j).prod * c ≤ (L.take j).prod * L[j] := by
        gcongr
        exact h _ (getElem_mem hj)
    _ = (L.take (j + 1)).prod := (prod_take_succ L j hj).symm
    _ ≤ (L.take k).prod := monotone_prod_take L hjk

end List
