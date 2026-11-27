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

All declarations are in the namespace `TauCeti.Rotation`.

## Main definitions

* `orbitFract`: the fractional parts of `n * α` for `n < N`, as a `Finset ℝ`.
* `gaps`: the multiset of gaps between consecutive points, with the wrap-around gap.
* `etaPos`, `etaNeg`: the least positive point and the wrap-around gap.

## Main statements

* `fract_natCast_mul_mem_orbitFract`: the point `Int.fract (n * α)` of index `n < N` belongs
  to `orbitFract α N`.
* `card_orbitFract_of_irrational`: for irrational `α` there are `N` points.
* `card_orbitFract_ratCast`: for `α = q` rational there are `min N q.den` points.
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
* `sub_eq_etaPos_or_etaNeg_or_add`: the gap from a point `x` to the next point `y` above it is
  `etaPos α N`, `etaNeg α N` or `etaPos α N + etaNeg α N`.
* `gaps_toFinset_subset`: **the three-gap theorem**, sharp form. Every gap is `etaPos α N`,
  `etaNeg α N` or `etaPos α N + etaNeg α N`.
* `card_toFinset_gaps_le_three`: **the three-gap theorem**. For every real `α` and every `N`
  there are at most three distinct gap lengths.
* `toFinset_gaps_eq_of_card_eq_three`: when exactly three lengths occur, they are these three.

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
  Enseign. Math. 44 (1998), 103–132.
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

/-- The gaps in terms of the points: a real number `g` is a gap exactly when, for some point `y`,
either `g = z - y` for the least point `z` above `y`, or `y` is the largest point and
`g = 1 - y`. -/
theorem mem_gaps_iff_exists {g : ℝ} :
    g ∈ gaps α N ↔ ∃ y ∈ orbitFract α N,
      (∃ z, IsLeast ((orbitFract α N : Set ℝ) ∩ Set.Ioi y) z ∧ g = z - y) ∨
        (IsGreatest (orbitFract α N : Set ℝ) y ∧ g = 1 - y) := by
  set l := (orbitFract α N).sort (· ≤ ·) with hl
  have hs : l.SortedLT := sortedLT_sort _
  have hset : (orbitFract α N : Set ℝ) = {x | x ∈ l} := by ext; simp [hl]
  have hlen : (List.zipWith (· - ·) (l.tail ++ [1]) l).length = l.length := by simp; omega
  rw [mem_gaps_iff, List.mem_iff_getElem, hset]
  constructor
  · rintro ⟨i, hi', rfl⟩
    have hi : i < l.length := hlen ▸ hi'
    refine ⟨l[i], (mem_sort _).1 (List.getElem_mem _), ?_⟩
    rw [List.getElem_zipWith_sub_tail_append_singleton]
    by_cases h : i + 1 < l.length
    · exact Or.inl ⟨l[i + 1], hs.isLeast_inter_Ioi_getElem_succ h, by rw [dite_eq_left h]⟩
    · exact Or.inr ⟨hs.sortedLE.isGreatest_getElem_of_not_succ_lt hi h, by rw [dite_eq_right h]⟩
  · rintro ⟨y, hy, ⟨z, hz, rfl⟩ | ⟨hy', rfl⟩⟩ <;>
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ((mem_sort (· ≤ ·)).2 hy) <;>
      by_cases h : i + 1 < l.length
    · refine ⟨i, hlen ▸ hi, ?_⟩
      rw [List.getElem_zipWith_sub_tail_append_singleton,
        ← (hs.isLeast_inter_Ioi_getElem_succ h).unique hz, dite_eq_left h]
    · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hz.1.1
      have := hs.getElem_lt_getElem_iff.1 (Set.mem_Ioi.1 hz.1.2)
      omega
    · exact absurd (hy'.2 (hs.isLeast_inter_Ioi_getElem_succ h).1.1)
        (not_le.2 (hs.getElem_lt_getElem_iff.2 (by omega)))
    · exact ⟨i, hlen ▸ hi, by rw [List.getElem_zipWith_sub_tail_append_singleton, dite_eq_right h]⟩

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

/-! ### The three-gap theorem

Let `r` be the least index of the least positive point `etaPos α N`, and `s` the least index of
the largest point `1 - etaNeg α N`. The gap from a point `x` to the next point `y` above it is
`etaPos α N` if `x` has an index `n` with `n + r < N`, it is `etaNeg α N` if `x` has an index
`n` with `s ≤ n`, and it is `etaPos α N + etaNeg α N` otherwise. In the last case no index `m` of
`y` has `r ≤ m` or `m + s < N`, since `x` would then have the index `m - r` or `m + s`. -/

/-- If a point has an index `n` such that `n + r` is still an index below `N`, where `r` is an
index of the least positive point, then the gap from this point is `etaPos α N`. -/
private theorem sub_eq_etaPos_of_add_lt {n r : ℕ} {y : ℝ} (hr : Int.fract (r * α) = etaPos α N)
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
private theorem sub_eq_etaNeg_of_le {n s : ℕ} {y : ℝ} (hs : Int.fract (s * α) = 1 - etaNeg α N)
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

/-- If the point `y` next above the point `x` has an index `m` such that `m + s` is still an
index below `N`, where `s` is an index of the largest point, then `x` has the index `m + s`. -/
private theorem fract_natCast_add_mul_eq_of_isLeast {m s : ℕ} {x : ℝ}
    (hs : Int.fract (s * α) = 1 - etaNeg α N) (hms : m + s < N) (hx : x ∈ orbitFract α N)
    (hy : IsLeast ((orbitFract α N : Set ℝ) ∩ Set.Ioi x) (Int.fract (m * α))) :
    Int.fract (↑(m + s) * α) = x := by
  obtain ⟨n, hn, rfl⟩ := mem_orbitFract.1 hx
  have hxy : Int.fract (n * α) < Int.fract (m * α) := hy.1.2
  have hb := etaNeg_pos α N
  have hn0 := Int.fract_nonneg (n * α)
  have h1 : 1 ≤ Int.fract (m * α) + Int.fract (s * α) := by
    by_contra h
    have h2 := Int.fract_natCast_add_mul_of_lt (not_le.1 h)
    have := le_one_sub_etaNeg_of_mem (fract_natCast_mul_mem_orbitFract α hms)
    linarith
  have h2 := Int.fract_natCast_add_mul_of_le h1
  have h3 : Int.fract (↑(m + s) * α) ≤ Int.fract (n * α) := by
    by_contra h
    have := hy.2 ⟨mem_coe.2 (fract_natCast_mul_mem_orbitFract α hms), not_le.1 h⟩
    linarith
  rcases lt_trichotomy n (m + s) with h | h | h
  · by_contra hne
    have := etaNeg_le_fract_sub_fract (i := n) (j := m + s) h.le hms (lt_of_le_of_ne h3 hne)
    linarith
  · rw [h]
  · have := etaNeg_le_fract_sub_fract (i := m) (j := n) (by omega) hn hxy
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

/-- The gap from a point `x` of the orbit to the next point `y` above it is `etaPos α N`,
`etaNeg α N` or `etaPos α N + etaNeg α N`. -/
theorem sub_eq_etaPos_or_etaNeg_or_add {x y : ℝ} (hx : x ∈ orbitFract α N)
    (hy : IsLeast ((orbitFract α N : Set ℝ) ∩ Set.Ioi x) y) :
    y - x = etaPos α N ∨ y - x = etaNeg α N ∨ y - x = etaPos α N + etaNeg α N := by
  obtain ⟨n, hn, rfl⟩ := mem_orbitFract.1 hx
  obtain ⟨m, hm, rfl⟩ := mem_orbitFract.1 (mem_coe.1 hy.1.1)
  have hcard : 2 ≤ #(orbitFract α N) :=
    one_lt_card.2 ⟨_, hx, _, mem_coe.1 hy.1.1, (Set.mem_Ioi.1 hy.1.2).ne⟩
  -- Let `r` and `s` be the least indices of the least positive point and of the largest point.
  obtain ⟨r₀, hr₀N, hr₀⟩ := mem_orbitFract.1 (mem_coe.1 (isLeast_etaPos hcard).1.1)
  obtain ⟨s₀, hs₀N, hs₀⟩ :=
    mem_orbitFract.1 (mem_coe.1 (isGreatest_one_sub_etaNeg α (Nat.zero_lt_of_lt hn)).1)
  have hexr : ∃ j : ℕ, Int.fract (j * α) = etaPos α N := ⟨r₀, hr₀⟩
  have hexs : ∃ j : ℕ, Int.fract (j * α) = 1 - etaNeg α N := ⟨s₀, hs₀⟩
  obtain ⟨r, hr, hrmin⟩ : ∃ r : ℕ, Int.fract (r * α) = etaPos α N ∧
      ∀ j : ℕ, Int.fract (j * α) = etaPos α N → r ≤ j :=
    ⟨Nat.find hexr, Nat.find_spec hexr, fun j hj => Nat.find_min' hexr hj⟩
  obtain ⟨s, hs, hsmin⟩ : ∃ s : ℕ, Int.fract (s * α) = 1 - etaNeg α N ∧
      ∀ j : ℕ, Int.fract (j * α) = 1 - etaNeg α N → s ≤ j :=
    ⟨Nat.find hexs, Nat.find_spec hexs, fun j hj => Nat.find_min' hexs hj⟩
  have hrN : r < N := (hrmin r₀ hr₀).trans_lt hr₀N
  have hsN : s < N := (hsmin s₀ hs₀).trans_lt hs₀N
  by_cases hA : n + r < N
  · exact Or.inl (sub_eq_etaPos_of_add_lt hr hA hy)
  by_cases hB : s ≤ n
  · exact Or.inr (Or.inl (sub_eq_etaNeg_of_le hs hB hn hy))
  by_cases hC : r ≤ m
  · have h := fract_natCast_sub_mul_eq_of_isLeast hr hC hm hx hy
    rw [← h] at hy ⊢
    exact Or.inl (sub_eq_etaPos_of_add_lt hr (by omega) hy)
  by_cases hD : m + s < N
  · have h := fract_natCast_add_mul_eq_of_isLeast hs hD hx hy
    rw [← h] at hy ⊢
    exact Or.inr (Or.inl (sub_eq_etaNeg_of_le hs (Nat.le_add_left s m) hD hy))
  exact Or.inr (Or.inr (le_antisymm
    (sub_le_etaPos_add_etaNeg hr hrmin hs hrN hsN (by omega) (by omega) hy)
    (etaPos_add_etaNeg_le_fract_sub_fract hr hrmin hs hsmin hrN hsN (by omega) (by omega)
      hy.1.2)))

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

end Rotation

end TauCeti
