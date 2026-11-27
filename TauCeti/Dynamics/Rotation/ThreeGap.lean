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

All declarations are in the namespace `TauCeti.Rotation`.

## Main definitions

* `orbitFract`: the fractional parts of `n * α` for `n < N`, as a `Finset ℝ`.
* `gaps`: the multiset of gaps between consecutive points, with the wrap-around gap.
* `etaPos`, `etaNeg`: the least positive point and the wrap-around gap.

## Main statements

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

## References

* P. Alessandri and V. Berthé, *Three distance theorems and combinatorics on words*,
  Enseign. Math. 44 (1998), 103–132.
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

end Rotation

end TauCeti
