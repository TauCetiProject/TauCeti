/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Int

/-!
# Integer intervals: translation boundaries and absolute-value balls

The symmetric interval `[-n, n]` has `2 n + 1` elements (`Int.card_Icc_neg_natCast_natCast`).
Translating a finite integer interval by `k` changes at most `2 * k.natAbs` of its elements.
This bound is independent of the endpoints, including when the interval is empty. It gives
vanishing relative boundary for intervals whose lengths tend to infinity.

For a cutoff `Y` in an ordered ring with a floor, the integers `c` with `|c| < Y` form the
interval `(-⌈Y⌉, ⌈Y⌉)` (`TauCeti.setOf_abs_intCast_lt_eq_Ioo`). They are therefore finitely many,
and at most `3 Y` of them once `Y ≥ 1`. This is the one-coefficient count behind boxes of integer
polynomials with real coefficient bounds.
-/

public section

open Finset
open scoped symmDiff

namespace Int

/-- Translating a finite integer interval by `k` changes at most `2 * |k|` elements. -/
theorem card_image_add_left_Icc_symmDiff_le (k a b : ℤ) :
    #(((Icc a b).image (k + ·)) ∆ Icc a b) ≤ 2 * k.natAbs := by
  have hcard : #((Icc a b).image (k + ·)) = #(Icc a b) :=
    card_image_of_injective _ (add_right_injective k)
  have hdiff : #((Icc a b).image (k + ·) \ Icc a b) =
      #(Icc a b \ (Icc a b).image (k + ·)) := card_sdiff_comm hcard
  have hbound : #(Icc a b \ (Icc a b).image (k + ·)) ≤ k.natAbs := by
    rcases le_total 0 k with hk | hk
    · have hsub : Icc a b \ (Icc a b).image (k + ·) ⊆ Ico a (a + k) := by
        intro x hx
        rw [Finset.image_add_left_Icc a b k] at hx
        simp only [mem_sdiff, mem_Icc, mem_Ico] at hx ⊢
        omega
      have := card_le_card hsub
      rw [card_Ico] at this
      omega
    · have hsub : Icc a b \ (Icc a b).image (k + ·) ⊆ Ioc (b + k) b := by
        intro x hx
        rw [Finset.image_add_left_Icc a b k] at hx
        simp only [mem_sdiff, mem_Icc, mem_Ioc] at hx ⊢
        omega
      have := card_le_card hsub
      rw [card_Ioc] at this
      omega
  rw [Finset.symmDiff_def, card_union_of_disjoint disjoint_sdiff_sdiff, hdiff]
  omega

/-- The symmetric interval `[-n, n]` of integers has `2 n + 1` elements. -/
theorem card_Icc_neg_natCast_natCast (n : ℕ) : #(Icc (-(n : ℤ)) n) = 2 * n + 1 := by
  rw [card_Icc]
  omega

end Int

namespace TauCeti

section Ring

variable {K : Type*} [Ring K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- The integers of absolute value less than `Y` are the interval `(-⌈Y⌉, ⌈Y⌉)`. -/
theorem setOf_abs_intCast_lt_eq_Ioo (Y : K) :
    {c : ℤ | |(c : K)| < Y} = ↑(Finset.Ioo (-⌈Y⌉) ⌈Y⌉) := by
  ext c
  simp [abs_lt, Int.lt_ceil, neg_lt]

/-- There are finitely many integers of absolute value less than `Y`. -/
theorem finite_setOf_abs_intCast_lt (Y : K) : {c : ℤ | |(c : K)| < Y}.Finite := by
  rw [setOf_abs_intCast_lt_eq_Ioo]
  exact Finset.finite_toSet _

end Ring

/-- For `Y ≥ 1`, there are at most `3 Y` integers of absolute value less than `Y`. -/
theorem ncard_setOf_abs_intCast_lt_le {K : Type*} [CommRing K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K] {Y : K} (hY : 1 ≤ Y) :
    ({c : ℤ | |(c : K)| < Y}.ncard : K) ≤ 3 * Y := by
  have hceil : (1 : ℤ) ≤ ⌈Y⌉ := Int.one_le_ceil_iff.mpr (zero_lt_one.trans_le hY)
  rw [setOf_abs_intCast_lt_eq_Ioo, Set.ncard_coe_finset, Int.card_Ioo, ← Int.cast_natCast,
    Int.toNat_of_nonneg (by omega)]
  push_cast
  linarith [Int.ceil_lt_add_one Y]

end TauCeti
