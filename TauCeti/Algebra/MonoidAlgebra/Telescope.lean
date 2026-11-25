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

Let `g` and `y` be commuting elements of a group `G` and let `r : R`. Multiplying the string
`r y + r y g⁻¹ + ⋯ + r y g⁻⁽ⁿ⁻¹⁾` of elements of `R[G]` by `1 - g⁻¹` telescopes to
`r y - r y g⁻ⁿ`, and multiplying `r y g + ⋯ + r y gⁿ` by `1 - g⁻¹` telescopes to `r y gⁿ - r y`.
In additive notation, with `e^x` for the basis element at `x`, these are the identities
`(1 - e^{-α}) (r e^y + r e^{y - α} + ⋯ + r e^{y - (n - 1) α}) = r e^y - r e^{y - n α}` and
`(1 - e^{-α}) (r e^{y + α} + ⋯ + r e^{y + n α}) = r e^{y + n α} - r e^y` for root strings in the
group algebra of a weight lattice.

Both are instances of the geometric-sum identities `mul_neg_geom_sum` and `mul_geom_sum` in the
ring `R[G]`: the summands are `g⁻ʲ * (r y)`, respectively `g * gʲ * (r y)`, as products in `R[G]`.

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

/-- For commuting `g` and `y`, multiplying the descending string
`r y + r y g⁻¹ + ⋯ + r y g⁻⁽ⁿ⁻¹⁾` by `1 - g⁻¹` telescopes. -/
@[to_additive (dont_translate := R) one_sub_single_neg_mul_sum_sub
  /-- For commuting `α` and `y`, multiplying the descending string
  `r e^y + r e^{y - α} + ⋯ + r e^{y - (n - 1) α}` by `1 - e^{-α}` telescopes. -/]
theorem one_sub_single_inv_mul_sum_div {g y : G} (hgy : Commute g y) (n : ℕ) (r : R) :
    (1 - single g⁻¹ 1) * ∑ j ∈ Finset.range n, single (y / g ^ j) r =
      single y r - single (y / g ^ n) r := by
  have hterm (j : ℕ) : single (y / g ^ j) r = single g⁻¹ 1 ^ j * single y r := by
    simp [single_pow, (hgy.pow_left j).inv_left.eq, div_eq_mul_inv]
  calc (1 - single g⁻¹ 1) * ∑ j ∈ Finset.range n, single (y / g ^ j) r
      = ((1 - single g⁻¹ 1) * ∑ j ∈ Finset.range n, single g⁻¹ 1 ^ j) * single y r := by
        simp only [hterm, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    _ = single y r - single (y / g ^ n) r := by
        rw [mul_neg_geom_sum, sub_mul, one_mul, hterm]

/-- For commuting `g` and `y`, multiplying the ascending string `r y g + ⋯ + r y gⁿ` by
`1 - g⁻¹` telescopes. -/
@[to_additive (dont_translate := R) one_sub_single_neg_mul_sum_add
  /-- For commuting `α` and `y`, multiplying the ascending string
  `r e^{y + α} + ⋯ + r e^{y + n α}` by `1 - e^{-α}` telescopes. -/]
theorem one_sub_single_inv_mul_sum_mul {g y : G} (hgy : Commute g y) (n : ℕ) (r : R) :
    (1 - single g⁻¹ 1) * ∑ j ∈ Finset.range n, single (y * g ^ (j + 1)) r =
      single (y * g ^ n) r - single y r := by
  have hterm (j : ℕ) : single (y * g ^ j) r = single g 1 ^ j * single y r := by
    simp [single_pow, (hgy.pow_left j).eq]
  have hg : (1 - single g⁻¹ (1 : R)) * single g 1 = single g 1 - 1 := by
    simp [sub_mul, one_def]
  calc (1 - single g⁻¹ 1) * ∑ j ∈ Finset.range n, single (y * g ^ (j + 1)) r
      = (1 - single g⁻¹ 1) * single g 1 * (∑ j ∈ Finset.range n, single g 1 ^ j) *
          single y r := by
        simp_rw [hterm, pow_succ', mul_assoc, Finset.sum_mul, Finset.mul_sum]
    _ = single (y * g ^ n) r - single y r := by
        rw [hg, mul_geom_sum, sub_mul, one_mul, hterm]

end Commute
