/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Algebra.Order.Ring.Int

/-!
# Suprema in complete lattices

This file adds supremum identities for complete lattices that are not in Mathlib.

## Main declarations

* `iSup_int_eq_sup_pos_mul_sup_zero_sup_neg_mul`: for `c ≠ 0`, a supremum over the integers
  splits by the sign of `n * c` into the parts with `n * c` positive, `n = 0`, and `n * c`
  negative.
-/

public section

/-- **Splitting a supremum over `ℤ` by the sign of `n * c`.** For `c ≠ 0`, the supremum of
`f n` over all integers `n` is the join of the suprema over `0 < n * c` and over `0 < n * -c`
with the middle term `f 0`. -/
theorem iSup_int_eq_sup_pos_mul_sup_zero_sup_neg_mul {α : Type*} [CompleteLattice α]
    (f : ℤ → α) {c : ℤ} (hc : c ≠ 0) :
    ⨆ n : ℤ, f n = (⨆ (n : ℤ) (_ : 0 < n * c), f n) ⊔ f 0 ⊔ ⨆ (n : ℤ) (_ : 0 < n * -c), f n := by
  refine le_antisymm (iSup_le fun n ↦ ?_) (sup_le (sup_le (iSup₂_le fun n _ ↦ le_iSup f n)
    (le_iSup f 0)) (iSup₂_le fun n _ ↦ le_iSup f n))
  rcases lt_trichotomy (n * c) 0 with h | h | h
  · exact le_sup_of_le_right (le_iSup₂_of_le n (by rwa [mul_neg, neg_pos]) le_rfl)
  · obtain rfl : n = 0 := (mul_eq_zero.mp h).resolve_right hc
    exact le_sup_of_le_left le_sup_right
  · exact le_sup_of_le_left (le_sup_of_le_left (le_iSup₂_of_le n h le_rfl))
