/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Sqrt
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Int.Order.Lemmas

/-!
# Finite integer intervals

Translating a finite integer interval by `k` changes at most `2 * k.natAbs` of its elements.
This bound is independent of the endpoints, including when the interval is empty. It gives
vanishing relative boundary for intervals whose lengths tend to infinity.

For `0 ≤ c`, filtering the symmetric integer interval `[-c, c]` by `t² ≤ c` gives
`[-c.sqrt, c.sqrt]`.

## Main results

* `Int.card_image_add_left_Icc_symmDiff_le`: `#(((Icc a b).image (k + ·)) ∆ Icc a b) ≤ 2 * |k|`.
* `Int.filter_sq_le_Icc_neg_eq_Icc_sqrt`:
  `(Icc (-c) c).filter (fun t ↦ t ^ 2 ≤ c) = Icc (-c.sqrt) c.sqrt` for `0 ≤ c`.
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

/-- Filtering the symmetric integer interval `[-c, c]` (`0 ≤ c`) by `t² ≤ c` gives
`[-c.sqrt, c.sqrt]`. -/
theorem filter_sq_le_Icc_neg_eq_Icc_sqrt {c : ℤ} (hc : 0 ≤ c) :
    (Icc (-c) c).filter (fun t ↦ t ^ 2 ≤ c) = Icc (-c.sqrt) c.sqrt := by
  have hle : c.sqrt ≤ c :=
    (Nat.cast_le.mpr (Nat.sqrt_le_self c.toNat)).trans_eq (Int.eq_natCast_toNat.mpr hc).symm
  ext t
  simp only [mem_filter, ← abs_le_sqrt_iff_sq_le hc, abs_le, mem_Icc]
  omega

end Int
