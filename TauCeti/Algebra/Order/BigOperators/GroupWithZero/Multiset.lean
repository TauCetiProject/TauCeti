/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset

/-!
# Products over a multiset of elements of `[0, 1]`

`Multiset.prod_map_le_one₀` is the multiset analogue of `Finset.prod_le_one₀`: a product of
factors in `[0, 1]` is at most `1`.
-/

public section

namespace Multiset

/-- If `0 ≤ f i ≤ 1` for every `i ∈ s`, then `∏_{i ∈ s} f i ≤ 1`. This is the multiset analogue
of `Finset.prod_le_one₀`. -/
theorem prod_map_le_one₀ {R ι : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R]
    [PosMulMono R] {s : Multiset ι} {f : ι → R} (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ 1) : (s.map f).prod ≤ 1 :=
  (prod_map_le_prod_map₀ f (fun _ ↦ 1) h0 h1).trans_eq (by simp)

end Multiset
