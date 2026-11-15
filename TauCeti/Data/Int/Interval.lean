/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Int

/-!
# Translation boundaries of integer intervals

Translating a finite integer interval by `k` changes at most `2 * k.natAbs` of its elements.
This bound is independent of the endpoints, including when the interval is empty. It gives
vanishing relative boundary for intervals whose lengths tend to infinity.
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

end Int
