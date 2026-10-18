/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.Valuation

/-!
# The multiplicative valuation of Hahn series

For a linearly ordered additive group `Γ` and a domain `R`, Mathlib's `HahnSeries.addVal Γ R` is
the additive valuation `x ↦ x.orderTop` with values in `WithTop Γ`. This file supplies the
corresponding multiplicative valuation `HahnSeries.valuation Γ R` with values in `Γᵐ⁰`, sending
a nonzero series of order `q` to `WithZero.exp (-q)` and `0` to `0`. This is the normalization of
Mathlib's valuation on Laurent series, for which `X` has valuation `exp (-1)`; it is the form a
`Valued` instance, and hence a valuation topology, is built from.

## Main definitions

* `HahnSeries.valuation Γ R`: the valuation `x ↦ exp (-x.order)` on `HahnSeries Γ R`.

## Main results

* `HahnSeries.valuation_of_ne_zero`: the value of a nonzero series is `exp (-x.order)`.
* `HahnSeries.valuation_le_exp_neg_iff` and `HahnSeries.valuation_lt_exp_neg_iff`: the valuation
  is at most (below) `exp (-q)` exactly when the order is at least (above) `q`, so balls for the
  valuation are the sets of series of large order.
-/

public section

open WithZero
open scoped WithZero

namespace HahnSeries

variable (Γ R : Type*) [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Ring R]
  [IsDomain R]

open scoped Classical in
/-- The multiplicative valuation on Hahn series, sending a nonzero series `x` to
`exp (-x.order)` and `0` to `0`. -/
noncomputable def valuation : Valuation (HahnSeries Γ R) Γᵐ⁰ where
  toFun x := if x = 0 then 0 else exp (-x.order)
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    simp [hx, hy, order_mul hx hy, exp_add, mul_comm]
  map_add_le_max' x y := by
    by_cases hxy : x + y = 0
    · simp [hxy]
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    simp only [hxy, hx, hy, ite_false, le_max_iff, exp_le_exp, neg_le_neg_iff]
    exact (le_total x.order y.order).imp
      (fun h ↦ (min_eq_left h).symm.trans_le (min_order_le_order_add hxy))
      (fun h ↦ (min_eq_right h).symm.trans_le (min_order_le_order_add hxy))

variable {Γ R}

/-- The valuation of a nonzero Hahn series is `exp (-x.order)`. -/
theorem valuation_of_ne_zero {x : HahnSeries Γ R} (hx : x ≠ 0) :
    valuation Γ R x = exp (-x.order) := by
  simp [valuation, hx]

/-- The valuation of the monomial `r t ^ q`, `r ≠ 0`, is `exp (-q)`. -/
@[simp]
theorem valuation_single (q : Γ) {r : R} (hr : r ≠ 0) :
    valuation Γ R (single q r) = exp (-q) := by
  rw [valuation_of_ne_zero (single_ne_zero hr), order_single hr]

/-- A Hahn series has valuation at most `exp (-q)` exactly when its order is at least `q`. -/
theorem valuation_le_exp_neg_iff {x : HahnSeries Γ R} {q : Γ} :
    valuation Γ R x ≤ exp (-q) ↔ (q : WithTop Γ) ≤ x.orderTop := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [valuation_of_ne_zero hx, exp_le_exp, neg_le_neg_iff, ← order_eq_orderTop_of_ne_zero hx,
    WithTop.coe_le_coe]

/-- A Hahn series has valuation below `exp (-q)` exactly when its order is above `q`. -/
theorem valuation_lt_exp_neg_iff {x : HahnSeries Γ R} {q : Γ} :
    valuation Γ R x < exp (-q) ↔ (q : WithTop Γ) < x.orderTop := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [valuation_of_ne_zero hx, exp_lt_exp, neg_lt_neg_iff, ← order_eq_orderTop_of_ne_zero hx,
    WithTop.coe_lt_coe]

end HahnSeries
