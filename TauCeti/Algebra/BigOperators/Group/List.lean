/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.GroupTheory.Submonoid.Center

/-!
# Products along lists in a noncommutative monoid

`List.prod_map_mul` splits the product of a list of pairwise products `f i * g i` into the product
of the `f i` times the product of the `g i`, in a commutative monoid. The same splitting holds in
any monoid as soon as the second factors are central, since each `g i` can then be moved past the
remaining first factors. Erasing an entry whose image is `1` does not change the product of the
images, in any monoid.

## Main results

* `List.prod_map_mul_of_mem_center`: `∏ (f i * g i) = (∏ f i) * (∏ g i)` along a list, when
  `g i` lies in the center for every entry `i` of the list.
* `List.prod_map_erase_of_eq_one`: `∏_{i ∈ l.erase a} f i = ∏_{i ∈ l} f i` when `f a = 1`.
-/

public section

namespace List

variable {ι M : Type*} [Monoid M]

/-- **Splitting a product of pairwise products with central second factors.** Along a list, the
product of the `f i * g i` is the product of the `f i` times the product of the `g i`, provided
`g i` is central for every entry `i` of the list. -/
theorem prod_map_mul_of_mem_center (l : List ι) (f g : ι → M)
    (hg : ∀ i ∈ l, g i ∈ Submonoid.center M) :
    (l.map fun i ↦ f i * g i).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => rw [map_nil, prod_nil, map_nil, prod_nil, map_nil, prod_nil, one_mul]
  | cons a l ih =>
    rw [map_cons, prod_cons, ih fun i hi ↦ hg i (mem_cons_of_mem a hi), map_cons, prod_cons,
      map_cons, prod_cons, mul_assoc, mul_assoc, ← mul_assoc (g a),
      ← Submonoid.mem_center_iff.mp (hg a mem_cons_self), mul_assoc]

/-- Erasing an entry `a` with `f a = 1` from a list does not change the product of the images
under `f`. -/
theorem prod_map_erase_of_eq_one [DecidableEq ι] (l : List ι) (f : ι → M) {a : ι}
    (ha : f a = 1) : ((l.erase a).map f).prod = (l.map f).prod := by
  by_cases h : a ∈ l
  · obtain ⟨l₁, l₂, -, rfl, he⟩ := exists_erase_eq h
    rw [he, map_append, map_append, map_cons, prod_append, prod_append, prod_cons, ha, one_mul]
  · rw [erase_of_not_mem h]

end List
