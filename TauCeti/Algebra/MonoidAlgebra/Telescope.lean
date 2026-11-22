/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs

import Mathlib.Algebra.Ring.GeomSum

/-!
# Telescoping strings in a group algebra

Let `g` and `y` be commuting elements of a group `G`. Multiplying the string
`y + y g⁻¹ + ⋯ + y g⁻⁽ⁿ⁻¹⁾` of basis elements of `R[G]` by `1 - g⁻¹` telescopes to
`y - y g⁻ⁿ`, and multiplying `y g + ⋯ + y gⁿ` by `1 - g⁻¹` telescopes to `y gⁿ - y`. In additive
notation, with `e^x` for the basis element at `x`, these are the identities
`(1 - e^{-α}) (e^y + e^{y - α} + ⋯ + e^{y - (n - 1) α}) = e^y - e^{y - n α}` and
`(1 - e^{-α}) (e^{y + α} + ⋯ + e^{y + n α}) = e^{y + n α} - e^y` for root strings in the group
algebra of a weight lattice.

Both are instances of the geometric-sum identities `mul_neg_geom_sum` and `mul_geom_sum` in the
ring `R[G]`: the summands are `g⁻ʲ * y`, respectively `g * gʲ * y`, as products of basis elements.

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
  have hterm (j : ℕ) : single (y / g ^ j) (1 : R) = single g⁻¹ 1 ^ j * single y 1 := by
    rw [single_pow, one_pow, single_mul_single, one_mul, inv_pow, (hgy.pow_left j).inv_left.eq,
      div_eq_mul_inv]
  rw [Finset.sum_congr rfl fun j _ ↦ hterm j, ← Finset.sum_mul, ← mul_assoc, mul_neg_geom_sum,
    sub_mul, one_mul, hterm]

/-- For commuting `g` and `y`, multiplying the ascending string `y g + ⋯ + y gⁿ` by `1 - g⁻¹`
telescopes. -/
@[to_additive (dont_translate := R) one_sub_single_neg_mul_sum_add
  /-- For commuting `α` and `y`, multiplying the ascending string
  `e^{y + α} + ⋯ + e^{y + n α}` by `1 - e^{-α}` telescopes. -/]
theorem one_sub_single_inv_mul_sum_mul {g y : G} (hgy : Commute g y) (n : ℕ) :
    (1 - single g⁻¹ (1 : R)) * ∑ j ∈ Finset.range n, single (y * g ^ (j + 1)) 1 =
      single (y * g ^ n) 1 - single y 1 := by
  have hterm (j : ℕ) : single (y * g ^ j) (1 : R) = single g 1 ^ j * single y 1 := by
    rw [single_pow, one_pow, single_mul_single, one_mul, (hgy.pow_left j).eq]
  have hg : (1 - single g⁻¹ (1 : R)) * single g 1 = single g 1 - 1 := by
    rw [sub_mul, one_mul, single_mul_single, inv_mul_cancel, one_mul, one_def]
  rw [Finset.sum_congr rfl fun j _ ↦ by rw [hterm, pow_succ'], ← Finset.sum_mul, ← Finset.mul_sum,
    ← mul_assoc, ← mul_assoc, hg, mul_geom_sum, sub_mul, one_mul, hterm]

end Commute
