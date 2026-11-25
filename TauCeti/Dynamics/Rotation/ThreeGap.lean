/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import TauCeti.Algebra.AddCircle
public import TauCeti.NumberTheory.Real.Irrational

/-!
# The fractional parts of an orbit of a rotation and the gaps between them

Fix a real number `α` and a natural number `N`. The first `N` points `0, α, 2α, …, (N - 1)α` of
the orbit of `0` under the rotation by `α` of the circle `ℝ / ℤ` are recorded by their
fractional parts, as the finite set `Rotation.orbitFract α N` of real numbers in `[0, 1)`.
These points cut the circle into arcs. `Rotation.gaps α N` is the multiset of the lengths of
these arcs: the gap from a point `y` is the distance to the next point above it, and the gap
from the largest point reaches `1`, which is the arc that wraps around to the point `0`.

This file sets up the two objects and their basic API: how many points there are (`N` for
irrational `α`, and `min N q.den` for a rational `α = q`), that the gaps are positive, that
there is one for each point, and that they sum to `1`. It also names the two lengths that the
three-gap theorem is stated with: `Rotation.etaPos α N`, the least positive point, and
`Rotation.etaNeg α N`, the gap from the largest point to `1`. Both are gaps.

## Main definitions

* `Rotation.orbitFract`: the fractional parts of `n * α` for `n < N`, as a `Finset ℝ`.
* `Rotation.gaps`: the multiset of gaps between consecutive points, with the wrap-around gap.
* `Rotation.etaPos`, `Rotation.etaNeg`: the least positive point and the wrap-around gap.

## Main statements

* `Rotation.card_orbitFract_of_irrational`: for irrational `α` there are `N` points.
* `Rotation.card_orbitFract_ratCast`: for `α = q` rational there are `min N q.den` points.
* `Rotation.card_gaps`: there are as many gaps as points.
* `Rotation.sum_gaps`: for `0 < N` the gaps sum to `1`.
* `Rotation.pos_of_mem_gaps`: every gap is positive.
* `Rotation.etaPos_mem_gaps`, `Rotation.etaNeg_mem_gaps`: the two named lengths are gaps.

## References

* P. Alessandri and V. Berthé, *Three distance theorems and combinatorics on words*,
  Enseign. Math. 44 (1998), 103–132.
-/

public section

open Finset

namespace Rotation

variable {α : ℝ} {M N : ℕ}

/-! ### The points -/

/-- The fractional parts of the first `N` multiples `0, α, …, (N - 1) * α` of `α`: the first `N`
points of the orbit of `0` under the rotation by `α`, as real numbers in `[0, 1)`. -/
noncomputable def orbitFract (α : ℝ) (N : ℕ) : Finset ℝ :=
  (range N).image fun n : ℕ => Int.fract (n * α)

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

/-- The differences of consecutive entries of the list `a :: l` closed up by an end point `b`
telescope: they sum to `b - a`. -/
private theorem sum_zipWith_sub_tail_append {G : Type*} [AddCommGroup G] (a b : G) (l : List G) :
    (List.zipWith (· - ·) ((a :: l).tail ++ [b]) (a :: l)).sum = b - a := by
  induction l generalizing a with
  | nil => simp
  | cons c l ih =>
    have h := ih c
    simp only [List.tail_cons, List.cons_append, List.zipWith_cons_cons, List.sum_cons] at h ⊢
    rw [h]
    abel

/-- The gaps of a strictly increasing list closed up by a strict upper bound are positive. -/
private theorem pos_of_mem_zipWith_sub_tail_append {b : ℝ} :
    ∀ {l : List ℝ}, l.Pairwise (· < ·) → (∀ x ∈ l, x < b) →
      ∀ g ∈ List.zipWith (· - ·) (l.tail ++ [b]) l, 0 < g
  | [], _, _, g, hg => by simp at hg
  | [a], _, hb, g, hg => by
    obtain rfl : g = b - a := by simpa using hg
    exact sub_pos.2 (hb a (by simp))
  | a :: c :: l, hl, hb, g, hg => by
    simp only [List.tail_cons, List.cons_append, List.zipWith_cons_cons, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact sub_pos.2 (List.rel_of_pairwise_cons hl (by simp))
    · exact pos_of_mem_zipWith_sub_tail_append (List.Pairwise.of_cons hl)
        (fun x hx => hb x (List.mem_cons_of_mem _ hx)) g (by simpa using hg)

/-- The last gap of a nonempty list closed up by `b` is `b` minus the last entry. -/
private theorem sub_getLast_mem_zipWith_sub_tail_append {b : ℝ} :
    ∀ {l : List ℝ} (hl : l ≠ []), b - l.getLast hl ∈ List.zipWith (· - ·) (l.tail ++ [b]) l
  | [a], _ => by simp
  | a :: c :: l, _ => by
    have h := sub_getLast_mem_zipWith_sub_tail_append (b := b) (List.cons_ne_nil c l)
    simp only [List.tail_cons, List.cons_append, List.zipWith_cons_cons, List.mem_cons,
      List.getLast_cons_cons] at h ⊢
    exact Or.inr h

/-- The multiset of gaps between consecutive points of `orbitFract α N`: with `s` the sorted list
of the points, the differences `s[i + 1] - s[i]`, together with the wrap-around gap `1 - s.max`
from the largest point to `1`. The gap from a point `y` is the distance to the next point above
`y`, so on the circle `ℝ / ℤ` the gaps are the lengths of the arcs between consecutive points. -/
noncomputable def gaps (α : ℝ) (N : ℕ) : Multiset ℝ :=
  let s := (orbitFract α N).sort (· ≤ ·)
  ((List.zipWith (· - ·) (s.tail ++ [1]) s : List ℝ) : Multiset ℝ)

/-- There are as many gaps as points. -/
theorem card_gaps (α : ℝ) (N : ℕ) : (gaps α N).card = #(orbitFract α N) := by
  simp only [gaps, Multiset.coe_card, List.length_zipWith, List.length_append, List.length_tail,
    length_sort, List.length_singleton]
  omega

@[simp]
theorem gaps_zero (α : ℝ) : gaps α 0 = 0 := by
  simp [gaps]

@[simp]
theorem gaps_one (α : ℝ) : gaps α 1 = {1} := by
  simp [gaps]

/-- For `0 < N`, the gaps sum to `1`, the length of the circle. -/
theorem sum_gaps (α : ℝ) (hN : 0 < N) : (gaps α N).sum = 1 := by
  rw [gaps, sort_orbitFract α hN, Multiset.sum_coe, sum_zipWith_sub_tail_append, sub_zero]

/-- Every gap is positive. -/
theorem pos_of_mem_gaps {g : ℝ} (hg : g ∈ gaps α N) : 0 < g :=
  pos_of_mem_zipWith_sub_tail_append (sortedLT_sort _).pairwise
    (fun _ hx => (coe_orbitFract_subset_Ico α N ((mem_sort _).1 hx)).2) g hg

/-! ### The two return lengths -/

/-- The least positive point of `orbitFract α N`, written `η⁺`. It is meaningful when the orbit
has at least two points; otherwise there is no positive point and the value is `0`. -/
noncomputable def etaPos (α : ℝ) (N : ℕ) : ℝ :=
  sInf (((orbitFract α N).erase 0 : Finset ℝ) : Set ℝ)

/-- The wrap-around gap from the largest point of `orbitFract α N` to `1`, written `η⁻`. -/
noncomputable def etaNeg (α : ℝ) (N : ℕ) : ℝ :=
  1 - sSup ((orbitFract α N : Finset ℝ) : Set ℝ)

/-- When the orbit has at least two points, its least positive point is a gap: the gap from the
point `0`. -/
theorem etaPos_mem_gaps (h : 2 ≤ #(orbitFract α N)) : etaPos α N ∈ gaps α N := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp at h
    · exact hN
  have ht : ((orbitFract α N).erase 0).Nonempty := by
    rw [← card_pos, card_erase_of_mem (zero_mem_orbitFract α hN)]
    omega
  have hmin : etaPos α N = ((orbitFract α N).erase 0).min' ht := (isLeast_min' _ ht).csInf_eq
  have hsort : ((orbitFract α N).erase 0).sort (· ≤ ·) = ((orbitFract α N).erase 0).min' ht ::
      (((orbitFract α N).erase 0).erase (((orbitFract α N).erase 0).min' ht)).sort (· ≤ ·) := by
    conv_lhs => rw [← insert_erase (min'_mem _ ht)]
    exact sort_insert _ (fun b hb => min'_le _ _ (mem_of_mem_erase hb)) (notMem_erase _ _)
  rw [gaps, sort_orbitFract α hN, hsort, hmin]
  simp

/-- For `0 < N`, the wrap-around gap is a gap: the gap from the largest point. -/
theorem etaNeg_mem_gaps (α : ℝ) (hN : 0 < N) : etaNeg α N ∈ gaps α N := by
  have hne : (orbitFract α N).Nonempty := ⟨0, zero_mem_orbitFract α hN⟩
  have hl : (orbitFract α N).sort (· ≤ ·) ≠ [] := by
    rw [sort_orbitFract α hN]
    exact List.cons_ne_nil _ _
  have hmax : sSup ((orbitFract α N : Finset ℝ) : Set ℝ) =
      ((orbitFract α N).sort (· ≤ ·)).getLast hl := by
    rw [hne.csSup_eq_max', max'_eq_sorted_last, List.getLast_eq_getElem]
  rw [etaNeg, hmax]
  exact sub_getLast_mem_zipWith_sub_tail_append hl

/-- The wrap-around gap is positive. -/
theorem etaNeg_pos (α : ℝ) (N : ℕ) : 0 < etaNeg α N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [etaNeg]
  · exact pos_of_mem_gaps (etaNeg_mem_gaps α hN)

/-- When the orbit has at least two points, its least positive point is positive. -/
theorem etaPos_pos (h : 2 ≤ #(orbitFract α N)) : 0 < etaPos α N :=
  pos_of_mem_gaps (etaPos_mem_gaps h)

end Rotation
