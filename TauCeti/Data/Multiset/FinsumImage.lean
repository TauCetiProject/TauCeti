/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Multiset.Basic

/-!
# Sums of singletons over the image of a multiset

For a duplicate-free multiset `M` and a map `g` which is injective on the elements of `M`, summing
the singleton multisets over the image of `M` under `g` gives back `M.map g`.

## Main statements

* `Multiset.finsum_mem_image_singleton_eq_map`: the sum of the singletons over `g '' M` is
  `M.map g`.
-/

public section

namespace Multiset

variable {X α : Type*}

/-- **Sums of singletons over the image of a multiset.** If `M` has no duplicates and `g` is
injective on the elements of `M`, the sum of the singleton multisets over the image of `M` under
`g` is `M.map g`. -/
theorem finsum_mem_image_singleton_eq_map {g : α → X} {M : Multiset α} (hM : M.Nodup)
    (hg : Set.InjOn g {w | w ∈ M}) :
    ∑ᶠ x ∈ g '' {w | w ∈ M}, ({x} : Multiset X) = M.map g := by
  classical
  have hfin : (g '' {w | w ∈ M}).Finite := M.finite_toSet.image g
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_eq_multiset_sum,
    Multiset.sum_map_singleton]
  refine (Multiset.Nodup.ext hfin.toFinset.nodup (hM.map_on fun w hw w' hw' h ↦ hg hw hw' h)).2
    fun x ↦ ?_
  rw [Finset.mem_val, hfin.mem_toFinset, Multiset.mem_map]
  simp only [Set.mem_image, Set.mem_ofPred_eq]

end Multiset
