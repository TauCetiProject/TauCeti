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
images, in any monoid. Two orderings of a list have the same product of images when every pair of
entries whose relative order differs has commuting images.

## Main results

* `List.prod_map_mul_of_mem_center`: `∏ (f i * g i) = (∏ f i) * (∏ g i)` along a list, when
  `g i` lies in the center for every entry `i` of the list.
* `List.prod_map_erase_of_eq_one`: `∏_{i ∈ l.erase a} f i = ∏_{i ∈ l} f i` when `f a = 1`.
* `List.prod_map_eq_of_perm`: two orderings of the same entries have the same product of images if
  the images of every inverted pair commute.
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
    simp [he, ha]
  · rw [erase_of_not_mem h]

/-- Two orderings of the same entries have the same product of images if every pair of entries whose
relative order differs has commuting images. -/
theorem prod_map_eq_of_perm (f : ι → M) {l l' : List ι} (hp : l.Perm l')
    (h : ∀ x y, [x, y].Sublist l → [y, x].Sublist l' → Commute (f x) (f y)) :
    (l.map f).prod = (l'.map f).prod := by
  induction l generalizing l' with
  | nil => rw [nil_perm.1 hp]
  | cons a t ih =>
    obtain ⟨u, v, rfl⟩ := append_of_mem (hp.subset mem_cons_self)
    have hp' : t.Perm (u ++ v) := (hp.trans perm_middle).cons_inv
    have hcomm : ∀ x ∈ u.map f, Commute (f a) x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
      have hyt : y ∈ t := hp'.symm.subset (mem_append_left v hy)
      refine h a y (cons_sublist_cons.2 (singleton_sublist.2 hyt)) ?_
      exact (singleton_sublist.2 hy).append (singleton_sublist.2 mem_cons_self)
    have key : ((u ++ a :: v).map f).prod = f a * ((u ++ v).map f).prod := by
      simp only [map_append, map_cons, prod_append, prod_cons]
      rw [← mul_assoc, ← (Commute.list_prod_right _ _ hcomm).eq, mul_assoc]
    rw [map_cons, prod_cons, key,
      ih hp' fun x y hxy hyx => h x y (hxy.trans (sublist_cons_self a t))
        (hyx.trans ((sublist_cons_self a v).append_left u))]

end List
