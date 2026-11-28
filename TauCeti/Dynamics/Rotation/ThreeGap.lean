/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import TauCeti.Algebra.AddCircle
public import TauCeti.Algebra.BigOperators.Group.List
public import TauCeti.Algebra.Order.Floor.Ring
public import TauCeti.Algebra.Order.Group.List
public import TauCeti.Data.List.Sort
public import TauCeti.Data.List.Zip
public import TauCeti.NumberTheory.Real.Irrational

/-!
# The fractional parts of an orbit of a rotation and the gaps between them

Fix a real number `α` and a natural number `N`. The first `N` points `0, α, 2α, …, (N - 1)α` of
the orbit of `0` under the rotation by `α` of the circle `ℝ / ℤ` are recorded by their
fractional parts, as the finite set `orbitFract α N` of real numbers in `[0, 1)`.
These points cut the circle into arcs. `gaps α N` is the multiset of the lengths of
these arcs: the gap from a point `y` is the distance to the next point above it, and the gap
from the largest point reaches `1`, which is the arc that wraps around to the point `0`.

This file sets up the two objects and their basic API: how many points there are (`N` for
irrational `α`, and `min N q.den` for a rational `α = q`), that the gaps are positive, that
there is one for each point, and that for `0 < N` they sum to `1` (for `N = 0` there is no point
and no gap). It also names the two lengths that the three-gap theorem is stated with:
`etaPos α N`, the least positive point, and `etaNeg α N`, the gap from the
largest point to `1`. The length `etaNeg α N` is a gap as soon as `0 < N`, and `etaPos α N` is a
gap when there are at least two distinct points, `2 ≤ #(orbitFract α N)`; with fewer points
there is no positive point, and `etaPos α N = 0` is not a gap.

The file then proves the three-gap theorem, for every real `α` and with no case split between
rational and irrational `α`: every gap is `etaPos α N`, `etaNeg α N` or their sum, so that at
most three distinct gap lengths occur.

Finally it describes the multiset of gaps through two return indices. `returnPos α N` is the
least natural number `n` with `Int.fract (n * α) = etaPos α N`, and `returnNeg α N` is the least
with `Int.fract (n * α) = 1 - etaNeg α N`. For `0 < N` they are indices below `N`:
`returnNeg α N` is the least index of the largest point, and `returnPos α N` is the least index
of the least positive point when there are at least two points. When the first `N` points are
distinct and `2 ≤ N`, the multiset `gaps α N` is the sum of three blocks: `N - returnPos α N`
copies of `etaPos α N`, `N - returnNeg α N` copies of `etaNeg α N` and
`returnPos α N + returnNeg α N - N` copies of `etaPos α N + etaNeg α N`. The sizes of the blocks
are not the multiplicities of the lengths in general, because the blocks of two equal lengths
add: for `α = 2 / 5` and `N = 4`, both `etaPos α N` and `etaNeg α N` are `1 / 5`, a gap that
occurs three times, in blocks of sizes `1` and `2`. When moreover `etaPos α N ≠ etaNeg α N`, the
three lengths are distinct and the sizes of the blocks are their multiplicities. This is the case
for irrational `α` and `2 ≤ N`.

All declarations are in the namespace `TauCeti.Rotation`.

## Main definitions

* `orbitFract`: the fractional parts of `n * α` for `n < N`, as a `Finset ℝ`.
* `gaps`: the multiset of gaps between consecutive points, with the wrap-around gap.
* `etaPos`, `etaNeg`: the least positive point and the wrap-around gap.
* `returnPos`, `returnNeg`: the return indices, the least natural numbers `n` with
  `Int.fract (n * α) = etaPos α N`, respectively `Int.fract (n * α) = 1 - etaNeg α N`.

## Main statements

* `fract_natCast_mul_mem_orbitFract`: the point `Int.fract (n * α)` of index `n < N` belongs
  to `orbitFract α N`.
* `card_orbitFract_of_irrational`: for irrational `α` there are `N` points.
* `card_orbitFract_ratCast`: for `α = q` rational there are `min N q.den` points.
* `card_orbitFract_eq_iff`: there are `N` points exactly when the points of index below `N` are
  distinct.
* `orbitFract_val`: when the first `N` points are distinct, the multiset of the points is the
  image of the indices below `N`.
* `card_gaps`: there are as many gaps as points.
* `sum_gaps`: for `0 < N` the gaps sum to `1`.
* `mem_gaps_iff_exists`: the gaps in terms of the points.
* `pos_of_mem_gaps`: every gap is positive.
* `isLeast_etaPos`: when `2 ≤ #(orbitFract α N)`, the length `etaPos α N` is the least
  nonzero point.
* `isGreatest_one_sub_etaNeg`: for `0 < N`, the largest point is `1 - etaNeg α N`.
* `etaPos_mem_gaps`: when `2 ≤ #(orbitFract α N)`, the length `etaPos α N` is a gap.
* `etaNeg_mem_gaps`: for `0 < N`, the length `etaNeg α N` is a gap.
* `etaPos_pos`, `etaNeg_pos`: `etaPos α N` is positive when
  `2 ≤ #(orbitFract α N)`, and `etaNeg α N` is always positive.
* `etaPos_le_of_mem`, `le_one_sub_etaNeg_of_mem`: a nonzero point is at least `etaPos α N`, and
  every point is at most `1 - etaNeg α N`.
* `etaPos_le_fract_sub_fract`, `etaNeg_le_fract_sub_fract`: for indices `i ≤ j < N`, the points
  of index `i` and `j` are at least `etaPos α N` apart when the point of index `j` is the
  larger, and at least `etaNeg α N` apart when it is the smaller.
* `returnPos_def`, `returnNeg_def`: the return indices as infima of sets of natural numbers.
* `fract_returnPos_mul`, `fract_returnNeg_mul`: the points of index `returnPos α N` and
  `returnNeg α N` are `etaPos α N` and `1 - etaNeg α N`.
* `returnPos_le`, `returnNeg_le`, `returnPos_lt`, `returnNeg_lt`: the return indices are at most
  every index of their points, and for `0 < N` they are below `N`.
* `returnPos_zero`, `returnNeg_zero`, `returnPos_one`, `returnNeg_one`: for `N = 0` and `N = 1`
  the return indices are `0`.
* `returnPos_eq_of_irrational`, `returnNeg_eq_of_irrational`: for irrational `α` they are the
  only indices of their points.
* `sub_eq_etaPos_of_add_lt`, `sub_eq_etaNeg_of_le`, `sub_eq_etaPos_add_etaNeg`: the gap from
  the point of index `n` to the next point above it. It is `etaPos α N` when `n + r < N` for an
  index `r` of the least positive point, it is `etaNeg α N` when `s ≤ n < N` for an index `s` of
  the largest point, and it is `etaPos α N + etaNeg α N` when neither holds for any such index.
* `sub_eq_ite_of_isLeast`: the three cases through the return indices. The gap from the point of
  index `n < N` to the next point above it is `etaPos α N` if `n + returnPos α N < N`, otherwise
  `etaNeg α N` if `returnNeg α N ≤ n`, and otherwise `etaPos α N + etaNeg α N`.
* `sub_eq_etaPos_or_etaNeg_or_add`: the gap from a point `x` to the next point `y` above it is
  `etaPos α N`, `etaNeg α N` or `etaPos α N + etaNeg α N`.
* `gaps_toFinset_subset`: **the three-gap theorem**, sharp form. Every gap is `etaPos α N`,
  `etaNeg α N` or `etaPos α N + etaNeg α N`.
* `card_toFinset_gaps_le_three`: **the three-gap theorem**. For every real `α` and every `N`
  there are at most three distinct gap lengths.
* `toFinset_gaps_eq_of_card_eq_three`: when exactly three lengths occur, they are these three.
* `le_returnPos_add_returnNeg`: when the first `N` points are distinct and `2 ≤ N`, the return
  indices add up to at least `N`.
* `gaps_eq_map_range`: when the first `N` points are distinct and `2 ≤ N`, the multiset of gaps
  is the image of the indices `n < N` under the gap from the point of index `n`, which is
  `etaPos α N` if `n + returnPos α N < N`, otherwise `etaNeg α N` if `returnNeg α N ≤ n`, and
  otherwise `etaPos α N + etaNeg α N`.
* `gaps_eq_replicate_add`: **the three blocks**. When the first `N` points are distinct and
  `2 ≤ N`, the multiset of gaps is the sum of `N - returnPos α N` copies of `etaPos α N`,
  `N - returnNeg α N` copies of `etaNeg α N` and `returnPos α N + returnNeg α N - N` copies of
  `etaPos α N + etaNeg α N`. The blocks of two equal lengths add.
* `etaPos_ne_etaNeg`: for irrational `α`, the lengths `etaPos α N` and `etaNeg α N` differ.
* `count_etaPos_gaps`, `count_etaNeg_gaps`, `count_etaPos_add_etaNeg_gaps`: **the
  multiplicities**. When the first `N` points are distinct, the three lengths occur
  `N - returnPos α N`, `N - returnNeg α N` and `returnPos α N + returnNeg α N - N` times; the
  first two need `etaPos α N ≠ etaNeg α N`, and the first and the last need `2 ≤ N`.
* `count_etaPos_gaps_of_irrational`, `count_etaNeg_gaps_of_irrational`,
  `count_etaPos_add_etaNeg_gaps_of_irrational`: the three multiplicities for irrational `α`.

`mem_gaps_iff_exists` describes the gaps through the points alone: the gap from a point
`y` is `z - y` for the least point `z` above `y`, and `1 - y` when `y` is the largest point.
`gaps_eq_coe` and `mem_gaps_iff` unfold `gaps` to the list it is
built from. The statements about lists of consecutive differences that the proofs use are
`List.sum_zipWith_sub_append_singleton_cons` and
`List.pos_of_mem_zipWith_sub_tail_append_singleton` (in
`TauCeti/Algebra/BigOperators/Group/List.lean` and
`TauCeti/Algebra/Order/Group/List.lean`), and
`List.getElem_zipWith_sub_tail_append_singleton` (in `TauCeti/Data/List/Zip.lean`),
`List.SortedLT.isLeast_inter_Ioi_getElem_succ` and
`List.SortedLE.isGreatest_getElem_of_not_succ_lt` (in `TauCeti/Data/List/Sort.lean`).

The point of index `j - i` or `i + j` is computed from the points of index `i` and `j` by
`Int.fract_natCast_sub_mul_of_le`, `Int.fract_natCast_sub_mul_of_lt`,
`Int.fract_natCast_add_mul_of_lt` and `Int.fract_natCast_add_mul_of_le` (in
`TauCeti/Algebra/Order/Floor/Ring.lean`).

## References

* P. Alessandri and V. Berthé, *Three distance theorems and combinatorics on words*,
  Enseign. Math. 44 (1998), 103–132. The three multiplicities are those of the *Three distance
  theorem* of §3.
* F. M. Liang, *A short proof of the 3d distance theorem*, Discrete Math. 28 (1979), 325–326.
* D. Kunert, three-gap theorem formalization in Lean (`dkunert/three-gap-theorem-lean`, MIT). The
  shape of the definitions `orbitFract`, `gaps`, `etaPos` and `etaNeg` (uniform in `α`, through
  `Int.fract`, with a multiset of gaps) follows it.
-/

public section

open Finset

namespace TauCeti

namespace Rotation

variable {α : ℝ} {M N : ℕ}

/-! ### The points -/

/-- The fractional parts of the first `N` multiples `0, α, …, (N - 1) * α` of `α`: the first `N`
points of the orbit of `0` under the rotation by `α`, as real numbers in `[0, 1)`. -/
noncomputable def orbitFract (α : ℝ) (N : ℕ) : Finset ℝ :=
  (range N).image fun n : ℕ => Int.fract (n * α)

@[simp]
theorem mem_orbitFract {x : ℝ} : x ∈ orbitFract α N ↔ ∃ n < N, Int.fract (n * α) = x := by
  simp [orbitFract]

@[simp]
theorem orbitFract_zero (α : ℝ) : orbitFract α 0 = ∅ := by
  simp [orbitFract]

@[simp]
theorem orbitFract_one (α : ℝ) : orbitFract α 1 = {0} := by
  simp [orbitFract]

theorem orbitFract_mono (α : ℝ) (h : M ≤ N) : orbitFract α M ⊆ orbitFract α N :=
  image_subset_image (range_subset_range.2 h)

/-- The points of `orbitFract α N` lie in `[0, 1)`. -/
theorem coe_orbitFract_subset_Ico (α : ℝ) (N : ℕ) : (orbitFract α N : Set ℝ) ⊆ Set.Ico 0 1 := by
  intro x hx
  obtain ⟨n, -, rfl⟩ := mem_orbitFract.1 (mem_coe.1 hx)
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- The point of index `n < N` belongs to `orbitFract α N`. -/
theorem fract_natCast_mul_mem_orbitFract (α : ℝ) {n : ℕ} (hn : n < N) :
    Int.fract (n * α) ∈ orbitFract α N :=
  mem_orbitFract.2 ⟨n, hn, rfl⟩

/-- The point `0` belongs to `orbitFract α N` as soon as `0 < N`. -/
theorem zero_mem_orbitFract (α : ℝ) (hN : 0 < N) : 0 ∈ orbitFract α N :=
  mem_orbitFract.2 ⟨0, hN, by simp⟩

theorem card_orbitFract_le (α : ℝ) (N : ℕ) : #(orbitFract α N) ≤ N :=
  card_image_le.trans_eq (card_range N)

/-- The orbit has `N` points exactly when the points of index below `N` are distinct. -/
theorem card_orbitFract_eq_iff :
    #(orbitFract α N) = N ↔ Set.InjOn (fun n : ℕ => Int.fract (n * α)) (Set.Iio N) := by
  rw [← coe_range, ← card_image_iff, card_range, orbitFract]

/-- When the first `N` points are distinct, the multiset of the points of the orbit is the image
of the indices below `N`: each point has exactly one index below `N`. -/
theorem orbitFract_val (h : #(orbitFract α N) = N) :
    (orbitFract α N).val = (Multiset.range N).map fun n : ℕ => Int.fract (n * α) := by
  rw [orbitFract, image_val_of_injOn (by rw [coe_range]; exact card_orbitFract_eq_iff.1 h),
    range_val]

/-- For irrational `α`, the first `N` points of the orbit are distinct. -/
theorem card_orbitFract_of_irrational (hα : Irrational α) (N : ℕ) : #(orbitFract α N) = N := by
  rw [orbitFract, card_image_of_injective _ hα.injective_fract_natCast_mul, card_range]

/-- For a rational number `q`, the orbit of `0` under the rotation by `q` has `q.den` points, so
its first `N` points are `min N q.den` in number. -/
theorem card_orbitFract_ratCast (q : ℚ) (N : ℕ) : #(orbitFract (q : ℝ) N) = min N q.den := by
  have key : orbitFract (q : ℝ) N = orbitFract (q : ℝ) (min N q.den) := by
    refine Subset.antisymm (fun x hx => ?_) (orbitFract_mono _ (min_le_left _ _))
    obtain ⟨n, hn, rfl⟩ := mem_orbitFract.1 hx
    exact mem_orbitFract.2 ⟨n % q.den,
      lt_min ((Nat.mod_le _ _).trans_lt hn) (Nat.mod_lt _ q.den_pos),
      (Int.fract_natCast_mul_ratCast_eq_iff q).2 (Nat.mod_modEq _ _)⟩
  rw [key, orbitFract, card_image_of_injOn, card_range]
  intro m hm n hn h
  have hm' : m < q.den := (mem_range.1 (mem_coe.1 hm)).trans_le (min_le_right _ _)
  have hn' : n < q.den := (mem_range.1 (mem_coe.1 hn)).trans_le (min_le_right _ _)
  exact ((Int.fract_natCast_mul_ratCast_eq_iff q).1 h).eq_of_lt_of_lt hm' hn'

/-- For `0 < N`, the sorted list of the points starts with `0`. -/
theorem sort_orbitFract (α : ℝ) (hN : 0 < N) :
    (orbitFract α N).sort (· ≤ ·) = 0 :: ((orbitFract α N).erase 0).sort (· ≤ ·) := by
  conv_lhs => rw [← insert_erase (zero_mem_orbitFract α hN)]
  exact sort_insert _ (fun b hb => (coe_orbitFract_subset_Ico α N (mem_of_mem_erase hb)).1)
    (notMem_erase _ _)

/-! ### The gaps -/

/-- The multiset of gaps between consecutive points of `orbitFract α N`: with `s` the sorted list
of the points, the differences `s[i + 1] - s[i]`, together with the wrap-around gap `1 - s.max`
from the largest point to `1`. The gap from a point `y` is the distance to the next point above
`y`, so on the circle `ℝ / ℤ` the gaps are the lengths of the arcs between consecutive points. -/
noncomputable def gaps (α : ℝ) (N : ℕ) : Multiset ℝ :=
  let s := (orbitFract α N).sort (· ≤ ·)
  ((List.zipWith (· - ·) (s.tail ++ [1]) s : List ℝ) : Multiset ℝ)

/-- The multiset `gaps α N` is the list of the differences of consecutive entries of the sorted
list of the points, closed up by `1`, read as a multiset. -/
theorem gaps_eq_coe (α : ℝ) (N : ℕ) :
    gaps α N = ((List.zipWith (· - ·) (((orbitFract α N).sort (· ≤ ·)).tail ++ [1])
      ((orbitFract α N).sort (· ≤ ·)) : List ℝ) : Multiset ℝ) := by
  rw [gaps]

/-- A real number is a gap exactly when it is one of the differences of consecutive entries of
the sorted list of the points, closed up by `1`. -/
theorem mem_gaps_iff {g : ℝ} :
    g ∈ gaps α N ↔ g ∈ List.zipWith (· - ·) (((orbitFract α N).sort (· ≤ ·)).tail ++ [1])
      ((orbitFract α N).sort (· ≤ ·)) := by
  rw [gaps_eq_coe, Multiset.mem_coe]

/-- There are as many gaps as points. -/
theorem card_gaps (α : ℝ) (N : ℕ) : (gaps α N).card = #(orbitFract α N) := by
  simp [gaps_eq_coe]
  omega

@[simp]
theorem gaps_zero (α : ℝ) : gaps α 0 = 0 := by
  simp [gaps_eq_coe]

@[simp]
theorem gaps_one (α : ℝ) : gaps α 1 = {1} := by
  simp [gaps_eq_coe]

/-- For `0 < N`, the gaps sum to `1`, the length of the circle. -/
theorem sum_gaps (α : ℝ) (hN : 0 < N) : (gaps α N).sum = 1 := by
  rw [gaps_eq_coe, Multiset.sum_coe, sort_orbitFract α hN, List.tail_cons,
    List.sum_zipWith_sub_append_singleton_cons, sub_zero]

/-- The multiset of gaps is the image of the points under any function `F` such that `F y` is
the gap from the point `y`: the distance to the next point above `y`, and `1 - y` when `y` is the
largest point. -/
private theorem gaps_eq_map_val {F : ℝ → ℝ}
    (hF : ∀ y ∈ orbitFract α N,
      (∀ z, IsLeast ((orbitFract α N : Set ℝ) ∩ Set.Ioi y) z → F y = z - y) ∧
        (IsGreatest (orbitFract α N : Set ℝ) y → F y = 1 - y)) :
    gaps α N = (orbitFract α N).val.map F := by
  set l := (orbitFract α N).sort (· ≤ ·) with hl
  have hs : l.SortedLT := sortedLT_sort _
  have hset : (orbitFract α N : Set ℝ) = {x | x ∈ l} := by ext; simp [hl]
  have key : List.zipWith (· - ·) (l.tail ++ [1]) l = l.map F := by
    refine List.ext_getElem (by simp; omega) fun i _ h₂ => ?_
    have hi : i < l.length := by simpa using h₂
    have hmem : l[i] ∈ orbitFract α N := (mem_sort _).1 (List.getElem_mem hi)
    rw [List.getElem_zipWith_sub_tail_append_singleton, List.getElem_map]
    by_cases h' : i + 1 < l.length
    · have h1 := hs.isLeast_inter_Ioi_getElem_succ h'
      rw [← hset] at h1
      rw [dite_eq_left h', (hF _ hmem).1 _ h1]
    · have h1 := hs.sortedLE.isGreatest_getElem_of_not_succ_lt hi h'
      rw [← hset] at h1
      rw [dite_eq_right h', (hF _ hmem).2 h1]
  rw [gaps_eq_coe, ← hl, key, ← Multiset.map_coe, hl, sort_eq]

/-- The gaps in terms of the points: a real number `g` is a gap exactly when, for some point `y`,
either `g = z - y` for the least point `z` above `y`, or `y` is the largest point and
`g = 1 - y`. -/
theorem mem_gaps_iff_exists {g : ℝ} :
    g ∈ gaps α N ↔ ∃ y ∈ orbitFract α N,
      (∃ z, IsLeast ((orbitFract α N : Set ℝ) ∩ Set.Ioi y) z ∧ g = z - y) ∨
        (IsGreatest (orbitFract α N : Set ℝ) y ∧ g = 1 - y) := by
  -- The points above `y`, and the gap `F y` from `y`.
  let t : ℝ → Finset ℝ := fun y => (orbitFract α N).filter (y < ·)
  let F : ℝ → ℝ := fun y => if h : (t y).Nonempty then (t y).min' h - y else 1 - y
  have ht : ∀ y (h : (t y).Nonempty),
      IsLeast ((orbitFract α N : Set ℝ) ∩ Set.Ioi y) ((t y).min' h) := fun y h => by
    have hset : (t y : Set ℝ) = (orbitFract α N : Set ℝ) ∩ Set.Ioi y := by ext; simp [t]
    rw [← hset]
    exact isLeast_min' _ h
  have hF : ∀ y ∈ orbitFract α N,
      (∀ z, IsLeast ((orbitFract α N : Set ℝ) ∩ Set.Ioi y) z → F y = z - y) ∧
        (IsGreatest (orbitFract α N : Set ℝ) y → F y = 1 - y) := by
    refine fun y _ => ⟨fun z hz => ?_, fun hy => ?_⟩
    · have h : (t y).Nonempty := ⟨z, mem_filter.2 ⟨mem_coe.1 hz.1.1, hz.1.2⟩⟩
      rw [show F y = (t y).min' h - y from dite_eq_left h, (ht y h).unique hz]
    · exact dite_eq_right fun ⟨x, hx⟩ =>
        not_lt.2 (hy.2 (mem_coe.2 (mem_filter.1 hx).1)) (mem_filter.1 hx).2
  rw [gaps_eq_map_val hF, Multiset.mem_map]
  refine exists_congr fun y => and_congr_right fun (hy : y ∈ orbitFract α N) => ⟨?_, ?_⟩
  · rintro rfl
    by_cases h : (t y).Nonempty
    · exact Or.inl ⟨_, ht y h, dite_eq_left h⟩
    · exact Or.inr ⟨⟨mem_coe.2 hy, fun x hx =>
        not_lt.1 fun hlt => h ⟨x, mem_filter.2 ⟨mem_coe.1 hx, hlt⟩⟩⟩, dite_eq_right h⟩
  · rintro (⟨z, hz, rfl⟩ | ⟨hy', rfl⟩)
    exacts [(hF y hy).1 z hz, (hF y hy).2 hy']

/-- Every gap is positive. -/
theorem pos_of_mem_gaps {g : ℝ} (hg : g ∈ gaps α N) : 0 < g :=
  List.pos_of_mem_zipWith_sub_tail_append_singleton (sortedLT_sort _)
    (fun _ hx => (coe_orbitFract_subset_Ico α N (mem_coe.2 ((mem_sort _).1 hx))).2)
    (mem_gaps_iff.1 hg)

/-! ### The two return lengths -/

/-- The least positive point of `orbitFract α N`, written `η⁺`. It is meaningful when the orbit
has at least two points; otherwise there is no positive point and the value is `0`. -/
noncomputable def etaPos (α : ℝ) (N : ℕ) : ℝ :=
  sInf (((orbitFract α N).erase 0 : Finset ℝ) : Set ℝ)

/-- The wrap-around gap from the largest point of `orbitFract α N` to `1`, written `η⁻`. -/
noncomputable def etaNeg (α : ℝ) (N : ℕ) : ℝ :=
  1 - sSup ((orbitFract α N : Finset ℝ) : Set ℝ)

theorem etaPos_def (α : ℝ) (N : ℕ) :
    etaPos α N = sInf (((orbitFract α N).erase 0 : Finset ℝ) : Set ℝ) := (rfl)

theorem etaNeg_def (α : ℝ) (N : ℕ) :
    etaNeg α N = 1 - sSup ((orbitFract α N : Finset ℝ) : Set ℝ) := (rfl)

/-- With fewer than two points there is no positive point, and `etaPos α N` is `0`. -/
theorem etaPos_of_card_lt_two (h : #(orbitFract α N) < 2) : etaPos α N = 0 := by
  have he : (orbitFract α N).erase 0 = ∅ := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · rw [← card_eq_zero, card_erase_of_mem (zero_mem_orbitFract α hN)]
      omega
  simp [etaPos, he]

@[simp]
theorem etaNeg_zero (α : ℝ) : etaNeg α 0 = 1 := by
  simp [etaNeg]

/-- When the orbit has at least two points, `etaPos α N` is the least of its nonzero points. -/
theorem isLeast_etaPos (h : 2 ≤ #(orbitFract α N)) :
    IsLeast ((orbitFract α N : Set ℝ) \ {0}) (etaPos α N) := by
  have ht : ((orbitFract α N).erase 0).Nonempty :=
    card_pos.1 (lt_of_lt_of_le (by omega) pred_card_le_card_erase)
  rw [← coe_erase, etaPos, ht.csInf_eq_min']
  exact isLeast_min' _ ht

/-- For `0 < N`, the largest point of the orbit is `1 - etaNeg α N`. -/
theorem isGreatest_one_sub_etaNeg (α : ℝ) (hN : 0 < N) :
    IsGreatest (orbitFract α N : Set ℝ) (1 - etaNeg α N) := by
  have hne : (orbitFract α N).Nonempty := ⟨0, zero_mem_orbitFract α hN⟩
  rw [etaNeg, sub_sub_cancel, hne.csSup_eq_max']
  exact isGreatest_max' _ hne

/-- When the orbit has at least two points, its least positive point is a gap: the gap from the
point `0`. -/
theorem etaPos_mem_gaps (h : 2 ≤ #(orbitFract α N)) : etaPos α N ∈ gaps α N := by
  have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
  -- Since the points are nonnegative, the points above `0` are the nonzero points.
  have hset : (orbitFract α N : Set ℝ) ∩ Set.Ioi 0 = (orbitFract α N : Set ℝ) \ {0} := by
    ext x
    refine ⟨fun ⟨hx, hx0⟩ => ⟨hx, (Set.mem_Ioi.1 hx0).ne'⟩, fun ⟨hx, hx0⟩ => ⟨hx, ?_⟩⟩
    exact (coe_orbitFract_subset_Ico α N hx).1.lt_of_ne' fun h0 => hx0 (Set.mem_singleton_iff.2 h0)
  exact mem_gaps_iff_exists.2 ⟨0, zero_mem_orbitFract α hN,
    Or.inl ⟨etaPos α N, hset ▸ isLeast_etaPos h, (sub_zero _).symm⟩⟩

/-- For `0 < N`, the wrap-around gap is a gap: the gap from the largest point. -/
theorem etaNeg_mem_gaps (α : ℝ) (hN : 0 < N) : etaNeg α N ∈ gaps α N :=
  have hmax := isGreatest_one_sub_etaNeg α hN
  mem_gaps_iff_exists.2 ⟨_, mem_coe.1 hmax.1, Or.inr ⟨hmax, (sub_sub_cancel _ _).symm⟩⟩

/-- The wrap-around gap is positive. -/
theorem etaNeg_pos (α : ℝ) (N : ℕ) : 0 < etaNeg α N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [etaNeg]
  · exact pos_of_mem_gaps (etaNeg_mem_gaps α hN)

/-- When the orbit has at least two points, its least positive point is positive. -/
theorem etaPos_pos (h : 2 ≤ #(orbitFract α N)) : 0 < etaPos α N := by
  obtain ⟨hmem, hne⟩ := (isLeast_etaPos h).1
  exact (coe_orbitFract_subset_Ico α N hmem).1.lt_of_ne' fun h0 => hne (Set.mem_singleton_iff.2 h0)

/-! ### Lower bounds for the distance between two points

Two indices below `N` whose points differ have points at least `etaPos α N` or at least
`etaNeg α N` apart, according to whether the later point is the larger or the smaller one. -/

/-- A nonzero point of the orbit is at least `etaPos α N`. -/
theorem etaPos_le_of_mem {x : ℝ} (hx : x ∈ orbitFract α N) (h0 : x ≠ 0) : etaPos α N ≤ x := by
  obtain ⟨n, hn, -⟩ := mem_orbitFract.1 hx
  have h2 : 2 ≤ #(orbitFract α N) :=
    one_lt_card.2 ⟨0, zero_mem_orbitFract α (by omega), x, hx, h0.symm⟩
  exact (isLeast_etaPos h2).2 ⟨mem_coe.2 hx, h0⟩

/-- A point of the orbit is at most `1 - etaNeg α N`. -/
theorem le_one_sub_etaNeg_of_mem {x : ℝ} (hx : x ∈ orbitFract α N) : x ≤ 1 - etaNeg α N := by
  obtain ⟨n, hn, -⟩ := mem_orbitFract.1 hx
  exact (isGreatest_one_sub_etaNeg α (by omega)).2 (mem_coe.2 hx)

/-- If the later of two points of the orbit is the larger one, they are at least `etaPos α N`
apart. -/
theorem etaPos_le_fract_sub_fract {i j : ℕ} (hij : i ≤ j) (hj : j < N)
    (h : Int.fract (i * α) < Int.fract (j * α)) :
    etaPos α N ≤ Int.fract (j * α) - Int.fract (i * α) := by
  rw [← Int.fract_natCast_sub_mul_of_le hij h.le]
  refine etaPos_le_of_mem (mem_orbitFract.2 ⟨j - i, by omega, rfl⟩) ?_
  rw [Int.fract_natCast_sub_mul_of_le hij h.le]
  exact (sub_pos.2 h).ne'

/-- If the later of two points of the orbit is the smaller one, they are at least `etaNeg α N`
apart. -/
theorem etaNeg_le_fract_sub_fract {i j : ℕ} (hij : i ≤ j) (hj : j < N)
    (h : Int.fract (j * α) < Int.fract (i * α)) :
    etaNeg α N ≤ Int.fract (i * α) - Int.fract (j * α) := by
  have h1 : Int.fract (↑(j - i) * α) ≤ 1 - etaNeg α N :=
    le_one_sub_etaNeg_of_mem (mem_orbitFract.2 ⟨j - i, by omega, rfl⟩)
  rw [Int.fract_natCast_sub_mul_of_lt hij h] at h1
  linarith

/-! ### The return indices

The return index `returnPos α N` is the least natural number `n` with
`Int.fract (n * α) = etaPos α N`, and `returnNeg α N` is the least natural number `n` with
`Int.fract (n * α) = 1 - etaNeg α N`. For `0 < N` both are indices below `N`: `returnNeg α N` is
then the least index of the largest point, and `returnPos α N` is the least index of the least
positive point when the orbit has at least two points. When the orbit has at most one point,
`etaPos α N = 0` and `returnPos α N = 0`. -/

/-- The return index `r⁺`: the least index `n` with `Int.fract (n * α) = etaPos α N`. When the
orbit has at least two points, it is the least index of the least positive point. -/
noncomputable def returnPos (α : ℝ) (N : ℕ) : ℕ :=
  sInf {n : ℕ | Int.fract (n * α) = etaPos α N}

/-- The return index `r⁻`: the least index `n` with `Int.fract (n * α) = 1 - etaNeg α N`. For
`0 < N`, it is the least index of the largest point. -/
noncomputable def returnNeg (α : ℝ) (N : ℕ) : ℕ :=
  sInf {n : ℕ | Int.fract (n * α) = 1 - etaNeg α N}

theorem returnPos_def (α : ℝ) (N : ℕ) :
    returnPos α N = sInf {n : ℕ | Int.fract (n * α) = etaPos α N} := (rfl)

theorem returnNeg_def (α : ℝ) (N : ℕ) :
    returnNeg α N = sInf {n : ℕ | Int.fract (n * α) = 1 - etaNeg α N} := (rfl)

/-- The index `returnPos α N` is at most every index of the point `etaPos α N`. -/
theorem returnPos_le {n : ℕ} (h : Int.fract (n * α) = etaPos α N) : returnPos α N ≤ n :=
  Nat.sInf_le h

/-- The index `returnNeg α N` is at most every index of the point `1 - etaNeg α N`. -/
theorem returnNeg_le {n : ℕ} (h : Int.fract (n * α) = 1 - etaNeg α N) : returnNeg α N ≤ n :=
  Nat.sInf_le h

/-- For `0 < N`, the point `etaPos α N` has an index below `N`: an index of the least positive
point when the orbit has at least two points, and the index `0` otherwise. -/
private theorem exists_lt_fract_eq_etaPos (α : ℝ) (hN : 0 < N) :
    ∃ n < N, Int.fract (n * α) = etaPos α N := by
  rcases lt_or_ge #(orbitFract α N) 2 with h | h
  · exact ⟨0, hN, by simp [etaPos_of_card_lt_two h]⟩
  · exact mem_orbitFract.1 (mem_coe.1 (isLeast_etaPos h).1.1)

/-- For `0 < N`, the largest point `1 - etaNeg α N` has an index below `N`. -/
private theorem exists_lt_fract_eq_one_sub_etaNeg (α : ℝ) (hN : 0 < N) :
    ∃ n < N, Int.fract (n * α) = 1 - etaNeg α N :=
  mem_orbitFract.1 (mem_coe.1 (isGreatest_one_sub_etaNeg α hN).1)

/-- The point of index `returnPos α N` is `etaPos α N`. -/
@[simp]
theorem fract_returnPos_mul (α : ℝ) (N : ℕ) : Int.fract (returnPos α N * α) = etaPos α N := by
  refine Nat.sInf_mem (s := {n : ℕ | Int.fract (n * α) = etaPos α N}) ?_
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨0, by simp [etaPos_of_card_lt_two (α := α) (N := 0) (by simp)]⟩
  · obtain ⟨n, -, hn⟩ := exists_lt_fract_eq_etaPos α hN
    exact ⟨n, hn⟩

/-- The point of index `returnNeg α N` is `1 - etaNeg α N`. -/
@[simp]
theorem fract_returnNeg_mul (α : ℝ) (N : ℕ) :
    Int.fract (returnNeg α N * α) = 1 - etaNeg α N := by
  refine Nat.sInf_mem (s := {n : ℕ | Int.fract (n * α) = 1 - etaNeg α N}) ?_
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨0, by simp⟩
  · obtain ⟨n, -, hn⟩ := exists_lt_fract_eq_one_sub_etaNeg α hN
    exact ⟨n, hn⟩

/-- For `0 < N`, `returnPos α N` is an index below `N`. -/
theorem returnPos_lt (α : ℝ) (hN : 0 < N) : returnPos α N < N := by
  obtain ⟨n, hnN, hn⟩ := exists_lt_fract_eq_etaPos α hN
  exact (returnPos_le hn).trans_lt hnN

/-- For `0 < N`, `returnNeg α N` is an index below `N`. -/
theorem returnNeg_lt (α : ℝ) (hN : 0 < N) : returnNeg α N < N := by
  obtain ⟨n, hnN, hn⟩ := exists_lt_fract_eq_one_sub_etaNeg α hN
  exact (returnNeg_le hn).trans_lt hnN

@[simp]
theorem returnPos_zero (α : ℝ) : returnPos α 0 = 0 :=
  Nat.le_zero.1 (returnPos_le (n := 0)
    (by simp [etaPos_of_card_lt_two (α := α) (N := 0) (by simp)]))

@[simp]
theorem returnNeg_zero (α : ℝ) : returnNeg α 0 = 0 :=
  Nat.le_zero.1 (returnNeg_le (n := 0) (by simp))

@[simp]
theorem returnPos_one (α : ℝ) : returnPos α 1 = 0 :=
  Nat.lt_one_iff.1 (returnPos_lt α one_pos)

@[simp]
theorem returnNeg_one (α : ℝ) : returnNeg α 1 = 0 :=
  Nat.lt_one_iff.1 (returnNeg_lt α one_pos)

/-- For irrational `α`, the index `returnPos α N` is the only index of the point `etaPos α N`. -/
theorem returnPos_eq_of_irrational (hα : Irrational α) {n : ℕ}
    (h : Int.fract (n * α) = etaPos α N) : returnPos α N = n :=
  hα.injective_fract_natCast_mul ((fract_returnPos_mul α N).trans h.symm)

/-- For irrational `α`, the index `returnNeg α N` is the only index of the point
`1 - etaNeg α N`. -/
theorem returnNeg_eq_of_irrational (hα : Irrational α) {n : ℕ}
    (h : Int.fract (n * α) = 1 - etaNeg α N) : returnNeg α N = n :=
  hα.injective_fract_natCast_mul ((fract_returnNeg_mul α N).trans h.symm)

/-! ### The three-gap theorem

Let `r` be an index of the least positive point `etaPos α N`, and `s` an index of the largest
point `1 - etaNeg α N`. The gap from a point `x` to the next point `y` above it is `etaPos α N`
if `x` has an index `n` with `n + r < N`, and it is `etaNeg α N` if `x` has an index `n` with
`s ≤ n < N`. If neither holds for any index of `x` and any such `r` and `s`, the gap is
`etaPos α N + etaNeg α N`; no index `m` of `y` then has `returnPos α N ≤ m`, since `x` would
have the index `m - returnPos α N`. For an index `n < N` of `x` it is enough to test the two
return indices, which are the least such `r` and `s`: this is `sub_eq_ite_of_isLeast`. -/

/-- If a point has an index `n` such that `n + r` is still an index below `N`, where `r` is an
index of the least positive point, then the gap from this point is `etaPos α N`. -/
theorem sub_eq_etaPos_of_add_lt {n r : ℕ} {y : ℝ} (hr : Int.fract (r * α) = etaPos α N)
    (hnr : n + r < N)
    (hy : IsLeast ((orbitFract α N : Set ℝ) ∩ Set.Ioi (Int.fract (n * α))) y) :
    y - Int.fract (n * α) = etaPos α N := by
  obtain ⟨m, hm, rfl⟩ := mem_orbitFract.1 (mem_coe.1 hy.1.1)
  have hxy : Int.fract (n * α) < Int.fract (m * α) := hy.1.2
  have ha : 0 < etaPos α N :=
    etaPos_pos (one_lt_card.2
      ⟨_, fract_natCast_mul_mem_orbitFract α (Nat.lt_of_add_right_lt hnr), _,
        fract_natCast_mul_mem_orbitFract α hm, hxy.ne⟩)
  have hm1 := Int.fract_lt_one (m * α)
  have hnr' := fract_natCast_mul_mem_orbitFract α hnr
  rcases lt_or_ge (Int.fract (n * α) + Int.fract (r * α)) 1 with h | h
  · -- The point of index `n + r` is `x + etaPos α N`, and `y` is not above it.
    have h2 := Int.fract_natCast_add_mul_of_lt h
    have h3 := hy.2 ⟨mem_coe.2 hnr', by rw [Set.mem_Ioi, h2]; linarith⟩
    rcases lt_or_ge n m with hnm | hmn
    · -- The point `y` comes later than `x`, so it is at least `etaPos α N` above it.
      have h1 := etaPos_le_fract_sub_fract hnm.le hm hxy
      linarith
    · have h4 := Int.fract_natCast_sub_mul_of_le (i := m) (j := n + r) (by omega) h3
      by_contra hne
      have h5 := etaPos_le_of_mem
        (fract_natCast_mul_mem_orbitFract α (N := N) (n := n + r - m) (by omega))
        (by rw [h4]; intro h0; apply hne; linarith)
      rw [h4] at h5
      linarith
  · -- The point of index `n + r` would be `0`.
    have h2 := Int.fract_natCast_add_mul_of_le h
    have h3 : Int.fract (↑(n + r) * α) = 0 := by
      by_contra h0
      have := etaPos_le_of_mem hnr' h0
      linarith
    rcases lt_or_ge n m with hnm | hmn
    · have h1 := etaPos_le_fract_sub_fract hnm.le hm hxy
      linarith
    · -- Then `1 - y` is a point below `etaPos α N`.
      have h4 := Int.fract_natCast_sub_mul_of_lt (i := m) (j := n + r) (by omega)
        (by rw [h3]; linarith [Int.fract_nonneg (n * α)])
      have h5 := etaPos_le_of_mem
        (fract_natCast_mul_mem_orbitFract α (N := N) (n := n + r - m) (by omega))
        (by rw [h4, h3]; intro h0; linarith)
      rw [h4, h3] at h5
      linarith

/-- If a point has an index `n` with `s ≤ n`, where `s` is an index of the largest point, and it
is not the largest point, then the gap from this point is `etaNeg α N`. -/
theorem sub_eq_etaNeg_of_le {n s : ℕ} {y : ℝ} (hs : Int.fract (s * α) = 1 - etaNeg α N)
    (hsn : s ≤ n) (hn : n < N)
    (hy : IsLeast ((orbitFract α N : Set ℝ) ∩ Set.Ioi (Int.fract (n * α))) y) :
    y - Int.fract (n * α) = etaNeg α N := by
  obtain ⟨m, hm, rfl⟩ := mem_orbitFract.1 (mem_coe.1 hy.1.1)
  have hxy : Int.fract (n * α) < Int.fract (m * α) := hy.1.2
  have hb := etaNeg_pos α N
  have h1 := le_one_sub_etaNeg_of_mem (fract_natCast_mul_mem_orbitFract α hm)
  -- The point of index `n - s` is `x + etaNeg α N`, and `y` is not below it.
  have h2 := Int.fract_natCast_sub_mul_of_lt (a := α) hsn (by linarith)
  have h3 := hy.2 ⟨mem_coe.2 (fract_natCast_mul_mem_orbitFract α (N := N) (n := n - s) (by omega)),
    by rw [Set.mem_Ioi, h2]; linarith⟩
  rcases lt_or_ge m n with hmn | hnm
  · have := etaNeg_le_fract_sub_fract hmn.le hn hxy
    linarith
  · by_contra hne
    have h4 : Int.fract (m * α) < Int.fract (↑(n - s) * α) :=
      lt_of_le_of_ne h3 (by rw [h2]; intro h0; apply hne; linarith)
    have := etaNeg_le_fract_sub_fract (i := n - s) (j := m) (by omega) hm h4
    linarith

/-- If the point `y` next above the point `x` has an index `m` with `r ≤ m`, where `r` is an
index of the least positive point, then `x` has the index `m - r`. -/
private theorem fract_natCast_sub_mul_eq_of_isLeast {m r : ℕ} {x : ℝ}
    (hr : Int.fract (r * α) = etaPos α N) (hrm : r ≤ m) (hm : m < N) (hx : x ∈ orbitFract α N)
    (hy : IsLeast ((orbitFract α N : Set ℝ) ∩ Set.Ioi x) (Int.fract (m * α))) :
    Int.fract (↑(m - r) * α) = x := by
  obtain ⟨n, hn, rfl⟩ := mem_orbitFract.1 hx
  have hxy : Int.fract (n * α) < Int.fract (m * α) := hy.1.2
  have hm' := fract_natCast_mul_mem_orbitFract α hm
  have ha : 0 < etaPos α N := etaPos_pos (one_lt_card.2 ⟨_, hx, _, hm', hxy.ne⟩)
  have h1 := etaPos_le_of_mem hm' (by intro h0; linarith [Int.fract_nonneg (n * α)])
  have h2 := Int.fract_natCast_sub_mul_of_le (a := α) hrm (by linarith)
  have h3 : Int.fract (↑(m - r) * α) ≤ Int.fract (n * α) := by
    by_contra h
    have := hy.2 ⟨mem_coe.2 (fract_natCast_mul_mem_orbitFract α (N := N) (n := m - r) (by omega)),
      not_le.1 h⟩
    linarith
  rcases lt_trichotomy n (m - r) with h | h | h
  · have := etaPos_le_fract_sub_fract (i := n) (j := m) (by omega) hm hxy
    linarith
  · rw [h]
  · by_contra hne
    have := etaPos_le_fract_sub_fract (i := m - r) (j := n) h.le hn (lt_of_le_of_ne h3 hne)
    linarith

/-- Let `r` be the least index of the least positive point and `s` an index of the largest
point. If a point has an index `n` with `n < s` such that `n + r` is not an index below `N`,
then the gap from this point is at most `etaPos α N + etaNeg α N`. -/
private theorem sub_le_etaPos_add_etaNeg {n r s : ℕ} {y : ℝ} (hr : Int.fract (r * α) = etaPos α N)
    (hrmin : ∀ j : ℕ, Int.fract (j * α) = etaPos α N → r ≤ j)
    (hs : Int.fract (s * α) = 1 - etaNeg α N) (hrN : r < N) (hsN : s < N) (hns : n < s)
    (hnr : N ≤ n + r)
    (hy : IsLeast ((orbitFract α N : Set ℝ) ∩ Set.Ioi (Int.fract (n * α))) y) :
    y - Int.fract (n * α) ≤ etaPos α N + etaNeg α N := by
  have hxy : Int.fract (n * α) < y := hy.1.2
  have hyb := le_one_sub_etaNeg_of_mem (mem_coe.1 hy.1.1)
  have har := le_one_sub_etaNeg_of_mem (fract_natCast_mul_mem_orbitFract α hrN)
  have ha : 0 < etaPos α N :=
    etaPos_pos (one_lt_card.2 ⟨_, fract_natCast_mul_mem_orbitFract α (hns.trans hsN), _,
      mem_coe.1 hy.1.1, hxy.ne⟩)
  have hb := etaNeg_pos α N
  -- The point of index `n + r - s` is not `0`, since `r` is the least index of its point.
  have key : Int.fract (↑(n + r - s) * α) ≠ 0 := by
    intro h0
    have h1 := Int.fract_natCast_sub_mul_of_le (i := n + r - s) (j := r) (by omega)
      (by rw [h0]; exact Int.fract_nonneg _)
    have := hrmin _ (by rw [h1, h0, sub_zero, hr])
    omega
  have hmem := fract_natCast_mul_mem_orbitFract α (N := N) (n := n + r - s) (by omega)
  -- So it is `x + etaPos α N + etaNeg α N`, a point above `x`.
  rcases lt_or_ge (Int.fract (n * α) + Int.fract (r * α)) 1 with h | h
  · have h1 := Int.fract_natCast_add_mul_of_lt h
    rcases lt_or_ge (Int.fract (↑(n + r) * α)) (Int.fract (s * α)) with h2 | h2
    · have h3 := Int.fract_natCast_sub_mul_of_lt (i := s) (j := n + r) (by omega) h2
      have := hy.2 ⟨mem_coe.2 hmem, by rw [Set.mem_Ioi, h3]; linarith⟩
      linarith
    · have h3 := Int.fract_natCast_sub_mul_of_le (i := s) (j := n + r) (by omega) h2
      have := etaPos_le_of_mem hmem key
      linarith
  · have h1 := Int.fract_natCast_add_mul_of_le h
    have h3 := Int.fract_natCast_sub_mul_of_lt (a := α) (i := s) (j := n + r) (by omega)
      (by linarith)
    have := etaPos_le_of_mem hmem key
    linarith

/-- Let `r` and `s` be the least indices of the least positive point and of the largest point.
If the point of index `n < s` is below the point of index `m < r`, then the two points are at
least `etaPos α N + etaNeg α N` apart. -/
private theorem etaPos_add_etaNeg_le_fract_sub_fract {n m r s : ℕ}
    (hr : Int.fract (r * α) = etaPos α N)
    (hrmin : ∀ j : ℕ, Int.fract (j * α) = etaPos α N → r ≤ j)
    (hs : Int.fract (s * α) = 1 - etaNeg α N)
    (hsmin : ∀ j : ℕ, Int.fract (j * α) = 1 - etaNeg α N → s ≤ j) (hrN : r < N) (hsN : s < N)
    (hns : n < s) (hmr : m < r) (h : Int.fract (n * α) < Int.fract (m * α)) :
    etaPos α N + etaNeg α N ≤ Int.fract (m * α) - Int.fract (n * α) := by
  rcases lt_trichotomy n m with hnm | rfl | hmn
  · -- The difference is the point of index `m - n`, which comes before the index `r`.
    have h1 := Int.fract_natCast_sub_mul_of_le hnm.le h.le
    rcases lt_or_ge (Int.fract (r * α)) (Int.fract (↑(m - n) * α)) with h2 | h2
    · have h3 := Int.fract_natCast_sub_mul_of_lt (i := m - n) (j := r) (by omega) h2
      have := le_one_sub_etaNeg_of_mem
        (fract_natCast_mul_mem_orbitFract α (N := N) (n := r - (m - n)) (by omega))
      linarith
    · have h3 := etaPos_le_fract_sub_fract (N := N) hnm.le (by omega) h
      have := hrmin (m - n) (by linarith)
      omega
  · exact absurd h (lt_irrefl _)
  · -- One minus the difference is the point of index `n - m`, which comes before the index `s`.
    have h1 := Int.fract_natCast_sub_mul_of_lt hmn.le h
    have h2 := le_one_sub_etaNeg_of_mem
      (fract_natCast_mul_mem_orbitFract α (N := N) (n := n - m) (by omega))
    have h3 := Int.fract_natCast_sub_mul_of_le (a := α) (i := n - m) (j := s) (by omega)
      (by linarith)
    rcases eq_or_ne (Int.fract (↑(s - (n - m)) * α)) 0 with h4 | h4
    · have := hsmin (n - m) (by linarith)
      omega
    · have := etaPos_le_of_mem
        (fract_natCast_mul_mem_orbitFract α (N := N) (n := s - (n - m)) (by omega)) h4
      linarith

/-- If a point has an index `n` such that `n + r` is not an index below `N` for any index `r` of
the least positive point, and such that `n < s` for every index `s` of the largest point, then
the gap from this point is `etaPos α N + etaNeg α N`. -/
theorem sub_eq_etaPos_add_etaNeg {n : ℕ} {y : ℝ}
    (hr : ∀ j : ℕ, Int.fract (j * α) = etaPos α N → N ≤ n + j)
    (hs : ∀ j : ℕ, Int.fract (j * α) = 1 - etaNeg α N → n < j)
    (hy : IsLeast ((orbitFract α N : Set ℝ) ∩ Set.Ioi (Int.fract (n * α))) y) :
    y - Int.fract (n * α) = etaPos α N + etaNeg α N := by
  obtain ⟨m, hm, rfl⟩ := mem_orbitFract.1 (mem_coe.1 hy.1.1)
  have hN : 0 < N := Nat.zero_lt_of_lt hm
  -- The return indices are the least indices of the least positive point and of the largest
  -- point.
  have hr' := fract_returnPos_mul α N
  have hs' := fract_returnNeg_mul α N
  have hrN := returnPos_lt α hN
  have hsN := returnNeg_lt α hN
  have hns : n < returnNeg α N := hs _ hs'
  have hnr : N ≤ n + returnPos α N := hr _ hr'
  have hx := fract_natCast_mul_mem_orbitFract α (hns.trans hsN)
  -- No index `m` of `y` has `returnPos α N ≤ m`: the point of index `n` would have the index
  -- `m - returnPos α N` too, and the point of index
  -- `returnNeg α N - (n - (m - returnPos α N))` would be the largest point.
  have hmr : m < returnPos α N := by
    by_contra hC
    have h := fract_natCast_sub_mul_eq_of_isLeast hr' (not_lt.1 hC) hm hx hy
    have h0 := Int.fract_natCast_sub_mul_of_le (a := α) (i := m - returnPos α N) (j := n)
      (by omega) h.le
    rw [h, sub_self] at h0
    have h1 := Int.fract_natCast_sub_mul_of_le (a := α) (i := n - (m - returnPos α N))
      (j := returnNeg α N) (by omega) (by rw [h0]; exact Int.fract_nonneg _)
    have := returnNeg_le (α := α) (N := N) (n := returnNeg α N - (n - (m - returnPos α N)))
      (by rw [h1, h0, sub_zero, hs'])
    omega
  exact le_antisymm
    (sub_le_etaPos_add_etaNeg hr' (fun _ => returnPos_le) hs' hrN hsN hns hnr hy)
    (etaPos_add_etaNeg_le_fract_sub_fract hr' (fun _ => returnPos_le) hs'
      (fun _ => returnNeg_le) hrN hsN hns hmr hy.1.2)

/-- The gap from the point of index `n < N` to the next point `y` above it, through the return
indices: it is `etaPos α N` if `n + returnPos α N < N`, otherwise `etaNeg α N` if
`returnNeg α N ≤ n`, and otherwise `etaPos α N + etaNeg α N`. The points of index below `N` need
not be distinct. -/
theorem sub_eq_ite_of_isLeast {n : ℕ} {y : ℝ} (hn : n < N)
    (hy : IsLeast ((orbitFract α N : Set ℝ) ∩ Set.Ioi (Int.fract (n * α))) y) :
    y - Int.fract (n * α) = if n + returnPos α N < N then etaPos α N
      else if returnNeg α N ≤ n then etaNeg α N else etaPos α N + etaNeg α N := by
  split_ifs with h1 h2
  · exact sub_eq_etaPos_of_add_lt (fract_returnPos_mul α N) h1 hy
  · exact sub_eq_etaNeg_of_le (fract_returnNeg_mul α N) h2 hn hy
  · -- The return indices are at most every index of their points.
    refine sub_eq_etaPos_add_etaNeg (fun j hj => ?_) (fun j hj => ?_) hy
    · have := returnPos_le hj
      omega
    · have := returnNeg_le hj
      omega

/-- The gap from a point `x` of the orbit to the next point `y` above it is `etaPos α N`,
`etaNeg α N` or `etaPos α N + etaNeg α N`. -/
theorem sub_eq_etaPos_or_etaNeg_or_add {x y : ℝ} (hx : x ∈ orbitFract α N)
    (hy : IsLeast ((orbitFract α N : Set ℝ) ∩ Set.Ioi x) y) :
    y - x = etaPos α N ∨ y - x = etaNeg α N ∨ y - x = etaPos α N + etaNeg α N := by
  obtain ⟨n, hn, rfl⟩ := mem_orbitFract.1 hx
  rw [sub_eq_ite_of_isLeast hn hy]
  split_ifs <;> simp

/-- **The three-gap theorem**, in its sharp form: every gap is one of `etaPos α N`, `etaNeg α N`
and `etaPos α N + etaNeg α N`. This holds for every real `α`, rational or not, and for every
`N`: when the orbit has a single point, the only gap is `1 = etaNeg α N`. -/
theorem gaps_toFinset_subset (α : ℝ) (N : ℕ) :
    (gaps α N).toFinset ⊆ {etaPos α N, etaNeg α N, etaPos α N + etaNeg α N} := by
  intro g hg
  obtain ⟨y, hy, ⟨z, hz, rfl⟩ | ⟨hy', rfl⟩⟩ :=
    mem_gaps_iff_exists.1 (Multiset.mem_toFinset.1 hg)
  · simpa using sub_eq_etaPos_or_etaNeg_or_add hy hz
  · have hN' : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
    rw [hy'.unique (isGreatest_one_sub_etaNeg α hN'), sub_sub_cancel]
    simp

/-- **The three-gap theorem**: the points `0, α, …, (N - 1) * α` cut the circle `ℝ / ℤ` into
arcs of at most three distinct lengths. -/
theorem card_toFinset_gaps_le_three (α : ℝ) (N : ℕ) : #(gaps α N).toFinset ≤ 3 :=
  (card_le_card (gaps_toFinset_subset α N)).trans card_le_three

/-- When exactly three gap lengths occur, they are `etaPos α N`, `etaNeg α N` and
`etaPos α N + etaNeg α N`. -/
theorem toFinset_gaps_eq_of_card_eq_three (h : #(gaps α N).toFinset = 3) :
    (gaps α N).toFinset = {etaPos α N, etaNeg α N, etaPos α N + etaNeg α N} :=
  eq_of_subset_of_card_le (gaps_toFinset_subset α N) (card_le_three.trans_eq h.symm)

/-! ### The multiplicities

Assume that the first `N` points are distinct and that `2 ≤ N`. By `sub_eq_ite_of_isLeast`, the
gap from the point of index `n < N` is `etaPos α N` for the `N - returnPos α N` indices with
`n + returnPos α N < N`, it is `etaNeg α N` for the `N - returnNeg α N` indices with
`returnNeg α N ≤ n < N`, and it is `etaPos α N + etaNeg α N` for the other
`returnPos α N + returnNeg α N - N` indices `n < N`. So the multiset of gaps is the sum of three
blocks of these sizes. Two of the three lengths can be equal, and their blocks then add. When
`etaPos α N ≠ etaNeg α N`, as for irrational `α`, the three lengths are distinct and the sizes of
the blocks are their multiplicities. -/

/-- When the first `N` points are distinct and `2 ≤ N`, the two return indices add up to at
least `N`. -/
theorem le_returnPos_add_returnNeg (hN : 2 ≤ N) (h : #(orbitFract α N) = N) :
    N ≤ returnPos α N + returnNeg α N := by
  have hcard : 2 ≤ #(orbitFract α N) := h.symm ▸ hN
  have hr := fract_returnPos_mul α N
  have hs := fract_returnNeg_mul α N
  have ha := etaPos_pos hcard
  have hb := etaNeg_pos α N
  by_contra hlt
  have hmem := fract_natCast_mul_mem_orbitFract α (N := N)
    (n := returnPos α N + returnNeg α N) (by omega)
  rcases lt_or_ge (Int.fract (returnPos α N * α) + Int.fract (returnNeg α N * α)) 1 with h1 | h1
  · -- The point of index `returnPos α N + returnNeg α N` would be above the largest point.
    have h2 := Int.fract_natCast_add_mul_of_lt h1
    have := le_one_sub_etaNeg_of_mem hmem
    linarith
  · -- It would be a point below `etaPos α N`, hence the point `0` of index `0`.
    have h2 := Int.fract_natCast_add_mul_of_le h1
    have h0 : Int.fract (↑(returnPos α N + returnNeg α N) * α) = 0 := by
      by_contra h0
      have := etaPos_le_of_mem hmem h0
      linarith
    have h3 : returnPos α N + returnNeg α N = 0 :=
      card_orbitFract_eq_iff.1 h (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega))
        (by simpa using h0)
    have h4 : returnPos α N = 0 := by omega
    rw [h4, Nat.cast_zero, zero_mul, Int.fract_zero] at hr
    linarith

/-- When the first `N` points are distinct and `2 ≤ N`, the multiset of gaps is the image of the
indices `n < N` under the gap from the point of index `n`: this gap is `etaPos α N` if
`n + returnPos α N < N`, otherwise `etaNeg α N` if `returnNeg α N ≤ n`, and otherwise
`etaPos α N + etaNeg α N`. -/
theorem gaps_eq_map_range (hN : 2 ≤ N) (h : #(orbitFract α N) = N) :
    gaps α N = (Multiset.range N).map fun n =>
      if n + returnPos α N < N then etaPos α N
      else if returnNeg α N ≤ n then etaNeg α N else etaPos α N + etaNeg α N := by
  have hinj := card_orbitFract_eq_iff.1 h
  have hsN := returnNeg_lt α (N := N) (by omega)
  have hrs := le_returnPos_add_returnNeg hN h
  -- The function `F` sends the point of index `n < N` to the gap `c n` from it.
  let c : ℕ → ℝ := fun n => if n + returnPos α N < N then etaPos α N
    else if returnNeg α N ≤ n then etaNeg α N else etaPos α N + etaNeg α N
  let F : ℝ → ℝ := fun y => c (Function.invFunOn (fun n : ℕ => Int.fract (n * α)) (Set.Iio N) y)
  have hF : ∀ n < N, F (Int.fract (n * α)) = c n := fun n hn =>
    congrArg c (hinj.leftInvOn_invFunOn (Set.mem_Iio.2 hn))
  refine (gaps_eq_map_val (F := F) fun y hy => ?_).trans ?_
  · obtain ⟨n, hn, rfl⟩ := mem_orbitFract.1 hy
    rw [hF n hn]
    refine ⟨fun z hz => (sub_eq_ite_of_isLeast hn hz).symm, fun hmax => ?_⟩
    -- The largest point has the index `returnNeg α N` only.
    have hmax' := hmax.unique (isGreatest_one_sub_etaNeg α (N := N) (by omega))
    have hns : n = returnNeg α N :=
      hinj (Set.mem_Iio.2 hn) (Set.mem_Iio.2 hsN) (hmax'.trans (fract_returnNeg_mul α N).symm)
    rw [show c n = etaNeg α N from (ite_eq_right (by omega)).trans (ite_eq_left hns.ge), hmax',
      sub_sub_cancel]
  · rw [orbitFract_val h, Multiset.map_map]
    exact Multiset.map_congr rfl fun n hn => hF n (Multiset.mem_range.1 hn)

/-- **The three blocks of gaps.** When the first `N` points are distinct and `2 ≤ N`, the
multiset of gaps is the sum of three blocks: `N - returnPos α N` copies of `etaPos α N`,
`N - returnNeg α N` copies of `etaNeg α N` and `returnPos α N + returnNeg α N - N` copies of
`etaPos α N + etaNeg α N`. The size of a block is the multiplicity of its length only when the
other two lengths differ from it: the blocks of two equal lengths add. -/
theorem gaps_eq_replicate_add (hN : 2 ≤ N) (h : #(orbitFract α N) = N) :
    gaps α N = Multiset.replicate (N - returnPos α N) (etaPos α N) +
      Multiset.replicate (N - returnNeg α N) (etaNeg α N) +
        Multiset.replicate (returnPos α N + returnNeg α N - N) (etaPos α N + etaNeg α N) := by
  have hrN := returnPos_lt α (N := N) (by omega)
  have hsN := returnNeg_lt α (N := N) (by omega)
  have hrs := le_returnPos_add_returnNeg hN h
  rw [gaps_eq_map_range hN h]
  set c : ℕ → ℝ := fun n => if n + returnPos α N < N then etaPos α N
    else if returnNeg α N ≤ n then etaNeg α N else etaPos α N + etaNeg α N
  -- The indices below `N - returnPos α N`, then those below `returnNeg α N`, then the others.
  have hsplit : Multiset.range N = Multiset.Ico 0 (N - returnPos α N) +
      Multiset.Ico (N - returnPos α N) (returnNeg α N) + Multiset.Ico (returnNeg α N) N := by
    rw [Multiset.Ico_add_Ico_eq_Ico (Nat.zero_le _)
        (show N - returnPos α N ≤ returnNeg α N by omega),
      Multiset.Ico_add_Ico_eq_Ico (Nat.zero_le _) hsN.le]
    exact congrArg Finset.val (range_eq_Ico N)
  -- On an interval of indices where `c` is constant, its values form a block.
  have hblock : ∀ (a b : ℕ) (x : ℝ), (∀ n ∈ Multiset.Ico a b, c n = x) →
      (Multiset.Ico a b).map c = Multiset.replicate (b - a) x := fun a b x hx => by
    rw [Multiset.map_congr rfl hx, Multiset.map_const']
    exact congrArg (Multiset.replicate · x) (Nat.card_Ico a b)
  have hpos := hblock 0 (N - returnPos α N) (etaPos α N) fun n hn =>
    ite_eq_left (by have := Multiset.mem_Ico.1 hn; omega)
  have hsum := hblock (N - returnPos α N) (returnNeg α N) (etaPos α N + etaNeg α N) fun n hn =>
    (ite_eq_right (by have := Multiset.mem_Ico.1 hn; omega)).trans
      (ite_eq_right (by have := Multiset.mem_Ico.1 hn; omega))
  have hneg := hblock (returnNeg α N) N (etaNeg α N) fun n hn =>
    (ite_eq_right (by have := Multiset.mem_Ico.1 hn; omega)).trans
      (ite_eq_left (by have := Multiset.mem_Ico.1 hn; omega))
  rw [Nat.sub_zero] at hpos
  rw [show returnNeg α N - (N - returnPos α N) = returnPos α N + returnNeg α N - N by omega]
    at hsum
  -- The middle block is the last summand of the statement.
  rw [hsplit, Multiset.map_add, Multiset.map_add, hpos, hsum, hneg]
  exact add_right_comm _ _ _

/-- For irrational `α`, the two return lengths are different. -/
theorem etaPos_ne_etaNeg (hα : Irrational α) (N : ℕ) : etaPos α N ≠ etaNeg α N := by
  have h := card_orbitFract_of_irrational hα N
  rcases lt_or_ge N 2 with hN | hN
  · rw [etaPos_of_card_lt_two (h.trans_lt hN)]
    exact (etaNeg_pos α N).ne
  intro heq
  have hr := fract_returnPos_mul α N
  have hs := fract_returnNeg_mul α N
  have h2 := Int.fract_natCast_add_mul_of_le (a := α) (i := returnPos α N)
    (j := returnNeg α N) (by rw [hr, hs, heq, add_sub_cancel])
  rw [hr, hs, heq, add_sub_cancel, sub_self] at h2
  have h3 : returnPos α N + returnNeg α N = 0 :=
    hα.injective_fract_natCast_mul (by simpa using h2)
  have := le_returnPos_add_returnNeg hN h
  omega

/-- **Multiplicity of the gap `etaPos α N`**: when the first `N` points are distinct, `2 ≤ N`
and `etaPos α N ≠ etaNeg α N`, it occurs `N - returnPos α N` times. -/
theorem count_etaPos_gaps (hN : 2 ≤ N) (h : #(orbitFract α N) = N)
    (hne : etaPos α N ≠ etaNeg α N) : (gaps α N).count (etaPos α N) = N - returnPos α N := by
  simp [gaps_eq_replicate_add hN h, Multiset.count_replicate, hne.symm, (etaNeg_pos α N).ne']

/-- **Multiplicity of the gap `etaNeg α N`**: when the first `N` points are distinct and
`etaPos α N ≠ etaNeg α N`, it occurs `N - returnNeg α N` times. -/
theorem count_etaNeg_gaps (h : #(orbitFract α N) = N) (hne : etaPos α N ≠ etaNeg α N) :
    (gaps α N).count (etaNeg α N) = N - returnNeg α N := by
  rcases lt_or_ge N 2 with hN | hN
  · interval_cases N
    · simp
    · simp [etaNeg]
  · simp [gaps_eq_replicate_add hN h, Multiset.count_replicate, hne,
      (etaPos_pos (h.symm ▸ hN)).ne']

/-- **Multiplicity of the gap `etaPos α N + etaNeg α N`**: when the first `N` points are distinct
and `2 ≤ N`, it occurs `returnPos α N + returnNeg α N - N` times, also when `etaPos α N` and
`etaNeg α N` are equal. -/
theorem count_etaPos_add_etaNeg_gaps (hN : 2 ≤ N) (h : #(orbitFract α N) = N) :
    (gaps α N).count (etaPos α N + etaNeg α N) = returnPos α N + returnNeg α N - N := by
  simp [gaps_eq_replicate_add hN h, Multiset.count_replicate, (etaPos_pos (h.symm ▸ hN)).ne',
    (etaNeg_pos α N).ne']

/-- For irrational `α` and `2 ≤ N`, the gap `etaPos α N` occurs `N - returnPos α N` times. -/
theorem count_etaPos_gaps_of_irrational (hα : Irrational α) (hN : 2 ≤ N) :
    (gaps α N).count (etaPos α N) = N - returnPos α N :=
  count_etaPos_gaps hN (card_orbitFract_of_irrational hα N) (etaPos_ne_etaNeg hα N)

/-- For irrational `α`, the gap `etaNeg α N` occurs `N - returnNeg α N` times. -/
theorem count_etaNeg_gaps_of_irrational (hα : Irrational α) (N : ℕ) :
    (gaps α N).count (etaNeg α N) = N - returnNeg α N :=
  count_etaNeg_gaps (card_orbitFract_of_irrational hα N) (etaPos_ne_etaNeg hα N)

/-- For irrational `α` and `2 ≤ N`, the gap `etaPos α N + etaNeg α N` occurs
`returnPos α N + returnNeg α N - N` times. -/
theorem count_etaPos_add_etaNeg_gaps_of_irrational (hα : Irrational α) (hN : 2 ≤ N) :
    (gaps α N).count (etaPos α N + etaNeg α N) = returnPos α N + returnNeg α N - N :=
  count_etaPos_add_etaNeg_gaps hN (card_orbitFract_of_irrational hα N)

end Rotation

end TauCeti
