/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.GroupTheory.Submonoid.Center
import Mathlib.Data.List.OfFn
import TauCeti.Data.Fin.Basic

/-!
# Products along lists in a noncommutative monoid

Along a nonempty list `x :: l` forming a chain for a relation `r`, attach a set `V y` to each
entry `y`. If every entry `y` has `f y ∈ V y`, and multiplying `f y` onto `V z` lands in `V y`
whenever `z` is an entry of `l` with `r y z`, then the product of the `f y` along the list lies in
the set `V x` attached to its first entry.

`List.prod_map_mul` splits the product of a list of pairwise products `f i * g i` into the product
of the `f i` times the product of the `g i`, in a commutative monoid. The same splitting holds in
any monoid as soon as the second factors are central, since each `g i` can then be moved past the
remaining first factors. Erasing an entry whose image is `1` does not change the product of the
images, in any monoid. Two orderings of a list have the same product of images when every pair of
entries whose relative order differs has commuting images.

In a commutative monoid (and additively in an `AddCommMonoid`), products indexed by the positions
`i : Fin l.length` of a list split across concatenation (`List.prod_get_append`), reduce on a
replicated list to a `Finset.range` product (`List.prod_get_replicate`), and decompose a `flatMap`
of replicated blocks along `List.range n` by block offsets
(`List.prod_get_flatMap_replicate_range`).

The ordered product `b₀ ⋯ bₙ₋₁` of a tuple (`List.prod (List.ofFn b)`) is the product of the
ordered products of its first `k` and its last `n - k` entries, and is unchanged when two adjacent
entries are multiplied together first (`Fin.contractNth`), by associativity.

## Main results

* `List.prod_map_mem_of_isChain`: along a nonempty `r`-chain `x :: l`, the product of the `f y`
  lies in `V x`, when each `f y` lies in `V y` and `f y * V z ⊆ V y` for entries with `r y z`.
* `List.prod_map_mul_of_mem_center`: `∏ (f i * g i) = (∏ f i) * (∏ g i)` along a list, when
  `g i` lies in the center for every entry `i` of the list.
* `List.prod_map_erase_of_eq_one`: `∏_{i ∈ l.erase a} f i = ∏_{i ∈ l} f i` when `f a = 1`.
* `List.prod_map_eq_of_perm`: two orderings of the same entries have the same product of images if
  the images of every inverted pair commute.
* `List.prod_get_append`, `List.prod_get_replicate`, `List.prod_get_flatMap_replicate_range` (and
  their additive counterparts): position-indexed products over appended, replicated, and
  block-replicated lists.
* `List.prod_ofFn_mul_prod_ofFn`: the ordered product of a tuple splits after its first `k`
  entries.
* `List.prod_ofFn_contractNth`: contracting two adjacent entries of a tuple by multiplication does
  not change its ordered product.
-/

public section

namespace List

section IsChain

variable {ι M : Type*} [MulOneClass M]

/-- **Induction along a chain.** Let `x :: l` be a chain for a relation `r`, and attach a set
`V y` to each entry `y`. If every entry `y` has `f y ∈ V y`, and multiplying `f y` onto an element
of `V z` lands in `V y` whenever `z` is an entry of `l` with `r y z`, then the product of the `f y`
along `x :: l` lies in `V x`. -/
theorem prod_map_mem_of_isChain {r : ι → ι → Prop} (f : ι → M) (V : ι → Set M) {x : ι}
    {l : List ι} (hl : (x :: l).IsChain r) (hbase : ∀ y ∈ x :: l, f y ∈ V y)
    (hstep : ∀ ⦃y z⦄, y ∈ x :: l → z ∈ l → r y z → ∀ q ∈ V z, f y * q ∈ V y) :
    ((x :: l).map f).prod ∈ V x := by
  induction l generalizing x with
  | nil => simpa using hbase x mem_cons_self
  | cons z l ih =>
    rw [isChain_cons_cons] at hl
    rw [map_cons, prod_cons]
    exact hstep mem_cons_self mem_cons_self hl.1 _
      (ih hl.2 (fun y hy ↦ hbase y (.tail _ hy))
        fun _ _ hy hw hyw ↦ hstep (.tail _ hy) (.tail _ hw) hyw)

end IsChain

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

section Indexed

variable {α N : Type*} [CommMonoid N]

/-- A position-indexed product over `xs ++ ys` splits into the product over `xs` and the shifted
product over `ys`. -/
@[to_additive /-- A position-indexed sum over `xs ++ ys` splits into the sum over `xs` and the
shifted sum over `ys`. -/]
theorem prod_get_append (xs ys : List α) (f : α → ℕ → N) :
    ∏ i : Fin (xs ++ ys).length, f ((xs ++ ys).get i) i.val =
      (∏ i : Fin xs.length, f (xs.get i) i.val) *
        ∏ j : Fin ys.length, f (ys.get j) (xs.length + j.val) := by
  rw [← (finCongr List.length_append).symm.prod_comp, Fin.prod_univ_add]
  congr 1
  · exact Finset.prod_congr rfl fun _ _ ↦ by simp [List.getElem_append_left]
  · exact Finset.prod_congr rfl fun _ _ ↦ by simp [List.getElem_append_right]

/-- A position-indexed product over `List.replicate m a` equals the product over
`Finset.range m`. -/
@[to_additive /-- A position-indexed sum over `List.replicate m a` equals the sum over
`Finset.range m`. -/]
theorem prod_get_replicate (m : ℕ) (a : α) (f : α → ℕ → N) :
    ∏ i : Fin (List.replicate m a).length, f ((List.replicate m a).get i) i.val =
      ∏ r ∈ Finset.range m, f a r := by
  rw [← (finCongr List.length_replicate).symm.prod_comp]
  simp only [List.get_eq_getElem, List.getElem_replicate, finCongr_symm, finCongr_apply,
    Fin.val_cast]
  exact Fin.prod_univ_eq_prod_range (fun r ↦ f a r) m

/-- A position-indexed product over a `flatMap` of replicated blocks along `List.range n` splits
by blocks, with the `r`-th copy of `val j` sitting at index `(∑ k ∈ Finset.range j, d k) + r`. -/
@[to_additive /-- A position-indexed sum over a `flatMap` of replicated blocks along `List.range n`
splits by blocks, with the `r`-th copy of `val j` sitting at index
`(∑ k ∈ Finset.range j, d k) + r`. -/]
theorem prod_get_flatMap_replicate_range (n : ℕ) (d : ℕ → ℕ) (val : ℕ → α) (f : α → ℕ → N) :
    ∏ i : Fin ((List.range n).flatMap fun j ↦ List.replicate (d j) (val j)).length,
        f (((List.range n).flatMap fun j ↦ List.replicate (d j) (val j)).get i) i.val =
      ∏ j ∈ Finset.range n,
        ∏ r ∈ Finset.range (d j), f (val j) ((∑ k ∈ Finset.range j, d k) + r) := by
  induction n with
  | zero =>
    rw [Finset.range_zero, Finset.prod_empty]
    exact Finset.prod_eq_one fun i _ ↦ (Nat.not_lt_zero i.val (by simpa using i.isLt)).elim
  | succ m ih =>
    let xs := (List.range m).flatMap fun j ↦ List.replicate (d j) (val j)
    have hflat : (List.range (m + 1)).flatMap (fun j ↦ List.replicate (d j) (val j)) =
        xs ++ List.replicate (d m) (val m) := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hsplit := hflat ▸ prod_get_append xs (List.replicate (d m) (val m)) f
    rw [hsplit, ih, Finset.prod_range_succ]
    congr 1
    simpa [xs, List.length_flatMap, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
      using prod_get_replicate (d m) (val m) fun x r ↦ f x (xs.length + r)

end Indexed

section OfFn

variable {M : Type*} [Monoid M]

/-- **The ordered product of a tuple splits** after its first `k` entries:
`(b₀ ⋯ bₖ₋₁) (bₖ ⋯ bₙ₋₁) = b₀ ⋯ bₙ₋₁`. -/
theorem prod_ofFn_mul_prod_ofFn {n k : ℕ} (hk : k ≤ n) (b : Fin n → M) :
    (ofFn fun l : Fin k => b ⟨l, by omega⟩).prod *
        (ofFn fun l : Fin (n - k) => b ⟨k + l, by omega⟩).prod = (ofFn b).prod := by
  rw [← prod_take_mul_prod_drop (ofFn b) k]
  congr 2 <;> apply ext_getElem <;> simp [hk]

/-- **Contracting two adjacent entries does not change the ordered product**:
`b₀ ⋯ (bₗ bₗ₊₁) ⋯ bₙ = b₀ ⋯ bₙ`. This is `Fin.partialProd_contractNth_castSucc` for the final
partial products. -/
@[simp]
theorem prod_ofFn_contractNth {n : ℕ} (b : Fin (n + 1) → M) (l : Fin n) :
    (ofFn (Fin.contractNth l.castSucc (· * ·) b)).prod = (ofFn b).prod := by
  rw [← Fin.partialProd_last_eq_prod_ofFn, ← Fin.partialProd_last_eq_prod_ofFn,
    Fin.partialProd_contractNth_castSucc]

end OfFn

end List
