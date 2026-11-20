/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.Range

/-!
# Reflection invariance of `Multiset.range`

Reversing the order of indices `{0, …, n - 1}` via `k ↦ n - 1 - k` does not change the image
multiset of a function `f : ℕ → α` over `Multiset.range n` (`Multiset.map_range_reflect`), the
multiset analogue of `Finset.sum_range_reflect` and `Finset.prod_range_reflect`.

## Main results

* `Multiset.map_range_reflect`:
  `(Multiset.range n).map (fun k => f (n - 1 - k)) = (Multiset.range n).map f`.
-/

public section

namespace Multiset

/-- Reflecting the indices of `Multiset.range n` via `k ↦ n - 1 - k` preserves the image multiset
of any function `f : ℕ → α`. -/
theorem map_range_reflect {α : Type*} (f : ℕ → α) (n : ℕ) :
    (range n).map (fun k => f (n - 1 - k)) = (range n).map f := by
  have hlist : (List.range n).map (fun k => n - 1 - k) = (List.range n).reverse :=
    List.ext_getElem (by simp) fun i hi _ => by
      simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_range]
  have hrev : (range n).map (fun k => n - 1 - k) = range n := by
    rw [← coe_range, map_coe, hlist, coe_reverse]
  simpa only [map_map, Function.comp_def] using congrArg (map f) hrev

end Multiset

end
