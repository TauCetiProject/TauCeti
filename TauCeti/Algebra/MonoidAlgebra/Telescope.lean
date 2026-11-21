/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Telescoping strings in a group algebra

Let `g` and `y` be commuting elements of a group `G`. Multiplying the string
`y + y g⁻¹ + ⋯ + y g⁻⁽ⁿ⁻¹⁾` of basis elements of `R[G]` by `1 - g⁻¹` telescopes to
`y - y g⁻ⁿ`, and multiplying `y g + ⋯ + y gⁿ` by `1 - g⁻¹` telescopes to `y gⁿ - y`. In additive
notation, with `e^x` for the basis element at `x`, these are the identities
`(1 - e^{-α}) (e^y + e^{y - α} + ⋯ + e^{y - (n - 1) α}) = e^y - e^{y - n α}` and
`(1 - e^{-α}) (e^{y + α} + ⋯ + e^{y + n α}) = e^{y + n α} - e^y` for root strings in the group
algebra of a weight lattice.

## Main statements

* `Commute.one_sub_single_inv_mul_sum_div`: the descending string telescopes; its additive
  form is `AddCommute.one_sub_single_neg_mul_sum_sub`.
* `Commute.one_sub_single_inv_mul_sum_mul`: the ascending string telescopes; its additive
  form is `AddCommute.one_sub_single_neg_mul_sum_add`.
-/

public section

open MonoidAlgebra

variable {R : Type*} [Ring R] {G : Type*} [Group G]

namespace Commute

/-- For commuting `g` and `y`, multiplying the descending string `y + y g⁻¹ + ⋯ + y g⁻⁽ⁿ⁻¹⁾` by
`1 - g⁻¹` telescopes. -/
@[to_additive (dont_translate := R) one_sub_single_neg_mul_sum_sub
  /-- For commuting `α` and `y`, multiplying the descending string
  `e^y + e^{y - α} + ⋯ + e^{y - (n - 1) α}` by `1 - e^{-α}` telescopes. -/]
theorem one_sub_single_inv_mul_sum_div {g y : G} (hgy : Commute g y) (n : ℕ) :
    (1 - single g⁻¹ (1 : R)) * ∑ j ∈ Finset.range n, single (y / g ^ j) 1 =
      single y 1 - single (y / g ^ n) 1 := by
  have h := Finset.sum_range_sub' (fun j ↦ single (y / g ^ j) (1 : R)) n
  rw [pow_zero, div_one] at h
  rw [Finset.mul_sum, ← h]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj : g⁻¹ * (y / g ^ j) = y / g ^ (j + 1) := by
    rw [pow_succ, div_mul_eq_div_div_swap, div_eq_mul_inv y g, ← hgy.inv_left.eq, mul_div_assoc]
  rw [sub_mul, one_mul, single_mul_single, mul_one, hj]

/-- For commuting `g` and `y`, multiplying the ascending string `y g + ⋯ + y gⁿ` by `1 - g⁻¹`
telescopes. -/
@[to_additive (dont_translate := R) one_sub_single_neg_mul_sum_add
  /-- For commuting `α` and `y`, multiplying the ascending string
  `e^{y + α} + ⋯ + e^{y + n α}` by `1 - e^{-α}` telescopes. -/]
theorem one_sub_single_inv_mul_sum_mul {g y : G} (hgy : Commute g y) (n : ℕ) :
    (1 - single g⁻¹ (1 : R)) * ∑ j ∈ Finset.range n, single (y * g ^ (j + 1)) 1 =
      single (y * g ^ n) 1 - single y 1 := by
  have h := Finset.sum_range_sub (fun j ↦ single (y * g ^ j) (1 : R)) n
  rw [pow_zero, mul_one] at h
  rw [Finset.mul_sum, ← h]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj : g⁻¹ * (y * g ^ (j + 1)) = y * g ^ j := by
    rw [pow_succ', ← mul_assoc y, ← hgy.eq, mul_assoc, inv_mul_cancel_left]
  rw [sub_mul, one_mul, single_mul_single, mul_one, hj]

end Commute
