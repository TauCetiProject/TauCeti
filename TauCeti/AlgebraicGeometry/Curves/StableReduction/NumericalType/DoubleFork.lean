/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Fork
import Mathlib.Tactic.Linarith

/-!
# Double-ended forks of `(-2)`-indices

A chain of `(-2)`-indices cannot have an additional leaf at both its second and its penultimate
component while remaining a proper subgraph of a numerical type. The two fork classifications
make every displayed edge simply laced and all component weights equal. The affine-`D` marks give
zero row sums on the chain and nonnegative row sums on the two leaves; a possible extra intersection
between the leaves only increases their row sums. This contradicts negative definiteness.

This is [Stacks, Lemma 55.5.11](https://stacks.math.columbia.edu/tag/0C8H). It is part of the
classification of proper connected subgraphs of `(-2)`-indices used to bound the multiplicities of
a minimal numerical type.

## Main result

* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.not_oppositeFork`: a proper chain of
  length at least four cannot carry distinct fork leaves at both ends.
-/

public section

namespace TauCeti

open Finset

namespace NumericalType

universe u

variable {T : NumericalType.{u}} {t : ℕ} {c : ℕ → T.Component}
  {left right : T.Component}

namespace IsSelfIntersectionMinusTwoFork

private lemma affine_sum_nonneg
    (hr : T.IsSelfIntersectionMinusTwoFork t c right)
    (hl : T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left)
    (ht : 3 < t) {w : ℕ+} (d : ℕ → T.Component) (y : ℕ → ℤ)
    (hd_lt : ∀ {i}, i < t → d i = c i) (hd_right : d t = right)
    (hd_left : d (t + 1) = left) (hw : ∀ i < t, (T.weight (c i) : ℤ) = w)
    (hwright : (T.weight right : ℤ) = w) (hwleft : (T.weight left : ℤ) = w)
    (hedge : ∀ i, i + 1 < t → T.intersection (c i) (c (i + 1)) = w)
    (hrightEdge : T.intersection (c (t - 2)) right = w)
    (hleftEdge : T.intersection (c 1) left = w)
    (hleftZero : ∀ {i}, i < t → i ≠ 1 → T.intersection (c i) left = 0)
    (hleftRight : left ≠ right) (hy0 : y 0 = 1) (hyLast : y (t - 1) = 1)
    (hyInterior : ∀ {i}, 0 < i → i + 1 < t → y i = 2) (hyRight : y t = 1)
    (hyLeft : y (t + 1) = 1) :
    ∀ i < t + 2, 0 ≤ ∑ j ∈ range (t + 2), T.intersection (d i) (d j) * y j := by
  have hforkCard := hr.le_card
  have hchainCard : t < Fintype.card T.Component := by
    omega
  have hsplit (x : T.Component) :
      ∑ j ∈ range (t + 2), T.intersection x (d j) * y j =
        (∑ j ∈ range t, T.intersection x (c j) * y j) +
          T.intersection x right * y t + T.intersection x left * y (t + 1) := by
    rw [show t + 2 = (t + 1) + 1 by omega, sum_range_succ, sum_range_succ, hd_right,
      hd_left]
    congr 2
    exact sum_congr rfl fun j hj ↦ by rw [hd_lt (mem_range.mp hj)]
  have hchainRow {i : ℕ} (hit : i < t) :
      0 ≤ ∑ j ∈ range (t + 2), T.intersection (d i) (d j) * y j := by
    rw [hd_lt hit, hsplit]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hr.left_sum_eq hchainCard (by omega) y, hy0, hyInterior (i := 1) (by omega)
          (by omega), hr.intersection_self 0 (by omega), hedge 0 (by omega),
          hw 0 (by omega),
          hr.branch_intersection_eq_zero (i := 0) (by omega) (by omega),
          hleftZero (i := 0) (by omega) (by omega), hyRight, hyLeft]
      linarith
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hit) with hilast | hilast
    · obtain rfl : i = t - 1 := by omega
      have hedgeLast : T.intersection (c (t - 2)) (c (t - 1)) = w := by
        simpa only [show t - 2 + 1 = t - 1 by omega] using hedge (t - 2) (by omega)
      rw [hr.right_sum_eq hchainCard (by omega) y, hyInterior (i := t - 2) (by omega)
          (by omega), hyLast, T.intersection_comm (c (t - 1)) (c (t - 2)),
          hedgeLast, hr.intersection_self (t - 1) (by omega), hw (t - 1) (by omega),
          hr.branch_intersection_eq_zero (i := t - 1) (by omega) (by omega),
          hleftZero (i := t - 1) (by omega) (by omega), hyRight, hyLeft]
      linarith
    · rw [hr.interior_sum_eq hchainCard y hi0 hilast,
          T.intersection_comm (c i) (c (i - 1))]
      have hedgePrev : T.intersection (c (i - 1)) (c i) = w := by
        simpa only [show i - 1 + 1 = i by omega] using hedge (i - 1) (by omega)
      rw [hedgePrev, hedge i hilast, hr.intersection_self i hit, hw i hit,
          hyInterior hi0 hilast, hyRight, hyLeft]
      by_cases hi1 : i = 1
      · subst i
        rw [hy0, hyInterior (i := 2) (by omega) (by omega),
          hr.branch_intersection_eq_zero (i := 1) (by omega) (by omega), hleftEdge]
        linarith
      · by_cases hipenultimate : i = t - 2
        · subst i
          have hyPrev : y (t - 2 - 1) = 2 := hyInterior (by omega) (by omega)
          have hyNext : y (t - 2 + 1) = 1 := by
            rw [show t - 2 + 1 = t - 1 by omega, hyLast]
          have hleftZero' : T.intersection (c (t - 2)) left = 0 :=
            hleftZero (by omega) (by omega)
          rw [hyPrev, hyNext, hrightEdge, hleftZero']
          linarith
        · rw [hyInterior (i := i - 1) (by omega) (by omega),
            hyInterior (i := i + 1) (by omega) (by omega),
            hr.branch_intersection_eq_zero hit hipenultimate, hleftZero hit hi1]
          linarith
  have hrightRow :
      0 ≤ ∑ j ∈ range (t + 2), T.intersection (d t) (d j) * y j := by
    rw [hd_right, hsplit]
    have hsum : (∑ j ∈ range t, T.intersection right (c j) * y j) =
        T.intersection right (c (t - 2)) * y (t - 2) := by
      refine sum_eq_single (t - 2) (fun j hj hne ↦ ?_) (fun hj ↦ ?_)
      · rw [T.intersection_comm,
          hr.branch_intersection_eq_zero (mem_range.mp hj) (by omega), zero_mul]
      · exact absurd (mem_range.mpr (by omega)) hj
    rw [hsum, T.intersection_comm right, hrightEdge,
      hyInterior (i := t - 2) (by omega) (by omega), hr.branch_intersection_self,
      hwright, hyRight, hyLeft]
    have := T.offDiagonal_nonneg right left hleftRight.symm
    linarith
  have hleftRow :
      0 ≤ ∑ j ∈ range (t + 2), T.intersection (d (t + 1)) (d j) * y j := by
    rw [hd_left, hsplit]
    have hsum : (∑ j ∈ range t, T.intersection left (c j) * y j) =
        T.intersection left (c 1) * y 1 := by
      refine sum_eq_single 1 (fun j hj hne ↦ ?_) (fun hj ↦ ?_)
      · rw [T.intersection_comm, hleftZero (mem_range.mp hj) hne, zero_mul]
      · exact absurd (mem_range.mpr (by omega)) hj
    rw [hsum, T.intersection_comm left, hleftEdge, hyInterior (i := 1) (by omega)
        (by omega), hl.branch_intersection_self, hwleft, hyRight, hyLeft]
    have := T.offDiagonal_nonneg left right hleftRight
    linarith
  intro i hi
  by_cases hit : i < t
  · exact hchainRow hit
  rcases (show i = t ∨ i = t + 1 by omega) with rfl | rfl
  · exact hrightRow
  · exact hleftRow

/-- A chain of at least four `(-2)`-indices cannot have additional leaves meeting its second and
penultimate components when the displayed components form a proper subset of the numerical type.
The leaves are necessarily distinct, but they may intersect each other; the affine-`D` marks still
give nonnegative row sums ([Stacks, Lemma 55.5.11](https://stacks.math.columbia.edu/tag/0C8H)). -/
theorem not_oppositeFork (hr : T.IsSelfIntersectionMinusTwoFork t c right)
    (hl : T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left)
    (ht : 3 < t) (hcard : t + 2 < Fintype.card T.Component) : False := by
  have hchainCard : t < Fintype.card T.Component := by omega
  have hrightCard : t + 1 < Fintype.card T.Component := by omega
  have hleftRight : left ≠ right := by
    intro h
    have hrightZero : T.intersection (c 1) right = 0 :=
      hr.branch_intersection_eq_zero (by omega) (by omega)
    have hleftPos : 0 < T.intersection (c 1) left := by
      simpa only [show t - 1 - (t - 2) = 1 by omega] using hl.branch_intersection_pos
    rw [h] at hleftPos
    omega
  have hleft_ne_chain : ∀ i < t, left ≠ c i := by
    intro i hi
    have hreverse : t - 1 - (t - 1 - i) = i := by omega
    simpa only [hreverse] using hl.branch_ne (t - 1 - i) (by omega)
  -- Classifying the two forks fixes one common weight, every chain edge, and the two leaf edges.
  obtain ⟨w, hw, hwright, hedge, hrightEdge⟩ := hr.exists_weight_intersection_eq hrightCard
  obtain ⟨w', hw', hwleft', -, hleftEdge'⟩ := hl.exists_weight_intersection_eq hrightCard
  have hreverseLast : t - 1 - 0 = t - 1 := by omega
  have hww : (w' : ℤ) = w := by
    have hw'last : (T.weight (c (t - 1)) : ℤ) = w' := by
      simpa only [hreverseLast] using hw' 0 (by omega)
    exact hw'last.symm.trans (hw (t - 1) (by omega))
  have hwleft : (T.weight left : ℤ) = w := hwleft'.trans hww
  have hreversePenultimate : t - 1 - (t - 2) = 1 := by omega
  have hleftEdge : T.intersection (c 1) left = w := by
    simpa only [hreversePenultimate, hww] using hleftEdge'
  have hleftZero : ∀ {i}, i < t → i ≠ 1 → T.intersection (c i) left = 0 := by
    intro i hi hi1
    have hreverse : t - 1 - (t - 1 - i) = i := by omega
    have hreverse_ne : t - 1 - i ≠ t - 2 := by omega
    simpa only [hreverse] using
      hl.branch_intersection_eq_zero (i := t - 1 - i) (by omega) hreverse_ne
  -- Enumerate the chain followed by its right and left leaves.
  let d : ℕ → T.Component := fun i ↦ if i < t then c i else if i = t then right else left
  have hd_lt {i : ℕ} (hi : i < t) : d i = c i := by simp [d, hi]
  have hd_right : d t = right := by simp [d]
  have hd_left : d (t + 1) = left := by simp [d]
  have hd_injective : ∀ i < t + 2, ∀ j < t + 2, d i = d j → i = j := by
    intro i hi j hj hij
    by_cases hit : i < t
    · by_cases hjt : j < t
      · rw [hd_lt hit, hd_lt hjt] at hij
        exact hr.injOn i hit j hjt hij
      · rcases (show j = t ∨ j = t + 1 by omega) with rfl | rfl
        · rw [hd_lt hit, hd_right] at hij
          exact (hr.branch_ne i hit hij.symm).elim
        · rw [hd_lt hit, hd_left] at hij
          exact (hleft_ne_chain i hit hij.symm).elim
    · by_cases hjt : j < t
      · rcases (show i = t ∨ i = t + 1 by omega) with rfl | rfl
        · rw [hd_right, hd_lt hjt] at hij
          exact (hr.branch_ne j hjt hij).elim
        · rw [hd_left, hd_lt hjt] at hij
          exact (hleft_ne_chain j hjt hij).elim
      · rcases (show i = t ∨ i = t + 1 by omega) with hi_eq | hi_eq
        · rcases (show j = t ∨ j = t + 1 by omega) with hj_eq | hj_eq
          · omega
          · subst i
            subst j
            rw [hd_right, hd_left] at hij
            exact (hleftRight hij.symm).elim
        · rcases (show j = t ∨ j = t + 1 by omega) with hj_eq | hj_eq
          · subst i
            subst j
            rw [hd_left, hd_right] at hij
            exact (hleftRight hij).elim
          · omega
  -- These are the affine `D` marks: one at the four leaves and two on the interior chain.
  let y : ℕ → ℤ := fun i ↦ if i < t then if i = 0 ∨ i + 1 = t then 1 else 2 else 1
  have hy0 : y 0 = 1 := by simp [y]
  have hyLast : y (t - 1) = 1 := by simp [y]; omega
  have hyInterior {i : ℕ} (hi : 0 < i) (hit : i + 1 < t) : y i = 2 := by
    simp [y, hi.ne', hit.ne]; omega
  have hyRight : y t = 1 := by simp [y]
  have hyLeft : y (t + 1) = 1 := by simp [y]
  refine T.not_forall_sum_intersection_mul_nonneg_of_pos (c := d) hd_injective hcard
    (y := y) (fun i hi ↦ ?_) ⟨0, by omega, by simp [y]⟩ ?_
  · simp only [y]
    split_ifs <;> omega
  exact affine_sum_nonneg hr hl ht d y hd_lt hd_right hd_left hw hwright hwleft hedge
    hrightEdge hleftEdge hleftZero hleftRight hy0 hyLast hyInterior hyRight hyLeft

end IsSelfIntersectionMinusTwoFork

end NumericalType

end TauCeti
