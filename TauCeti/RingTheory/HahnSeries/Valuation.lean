/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.Valuation

/-!
# The multiplicative valuation of Hahn series

Let `Γ` be a linearly ordered additive group and `R` a domain. Mathlib's `HahnSeries.addVal`
is the additive valuation `x ↦ ord x = x.orderTop` with values in `WithTop Γ`. This file defines
its multiplicative counterpart

`HahnSeries.valuation Γ R : Valuation R⟦Γ⟧ Γᵐ⁰`,

sending a nonzero series of order `g` to `exp (-g)` and `0` to `0`. Thus series of large order
have small valuation. For `Γ = ℤ` and a field `K` of coefficients it takes the same values as
Mathlib's valuation on `K⸨X⸩`, which sends `f ≠ 0` to `exp (-ord f)`
(`TauCeti.LaurentSeries.valuation_eq_exp_neg_order`); for `Γ = ℚ` it restricts to the valuation of
the Puiseux field.

The comparison lemmas translate between the two valuations: `v x < exp (-g)` exactly when
`g < ord x`, and `v x ≤ exp (-g)` exactly when `g ≤ ord x`. These are the form in which balls of
the valuation topology are described by orders.

## Main definitions

* `HahnSeries.valuation Γ R`: the multiplicative valuation `x ↦ exp (-ord x)`.

## Main results

* `HahnSeries.valuation_eq_exp_neg_order`: a nonzero series of order `g` has valuation `exp (-g)`.
* `HahnSeries.valuation_lt_exp_neg_iff`, `HahnSeries.valuation_le_exp_neg_iff`: valuation balls
  are order conditions.
* `HahnSeries.valuation_le_valuation_iff`: the valuation reverses the order of `ord`.
-/

public section

open WithZero

namespace HahnSeries

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Ring R]
  [IsDomain R]

open scoped Classical in
variable (Γ R) in
/-- The multiplicative valuation on `R⟦Γ⟧`, sending a nonzero series of order `g` to `exp (-g)` and
`0` to `0`. -/
noncomputable def valuation : Valuation R⟦Γ⟧ Γᵐ⁰ where
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
    simp only [hxy, hx, hy, ↓reduceIte, le_max_iff, exp_le_exp, neg_le_neg_iff]
    exact (min_le_iff.mp (min_order_le_order_add hxy))

variable {x y : R⟦Γ⟧}

/-- A nonzero Hahn series of order `g` has valuation `exp (-g)`. -/
theorem valuation_eq_exp_neg_order (hx : x ≠ 0) : valuation Γ R x = exp (-x.order) := by
  simp [valuation, hx]

/-- The valuation of `x` vanishes exactly when `x = 0`. -/
@[simp]
theorem valuation_eq_zero_iff : valuation Γ R x = 0 ↔ x = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  simp [valuation_eq_exp_neg_order hx, hx]

/-- The monomial `r t ^ g`, for `r ≠ 0`, has valuation `exp (-g)`. -/
@[simp]
theorem valuation_single (g : Γ) {r : R} (hr : r ≠ 0) :
    valuation Γ R (single g r) = exp (-g) := by
  rw [valuation_eq_exp_neg_order (single_ne_zero hr), order_single hr]

/-- The valuation of `x` is below `exp (-g)` exactly when the order of `x` exceeds `g`. -/
theorem valuation_lt_exp_neg_iff (g : Γ) :
    valuation Γ R x < exp (-g) ↔ (g : WithTop Γ) < x.orderTop := by
  by_cases hx : x = 0
  · simp [hx]
  rw [valuation_eq_exp_neg_order hx, ← order_eq_orderTop_of_ne_zero hx, exp_lt_exp, neg_lt_neg_iff,
    WithTop.coe_lt_coe]

/-- The valuation of `x` is at most `exp (-g)` exactly when the order of `x` is at least `g`. -/
theorem valuation_le_exp_neg_iff (g : Γ) :
    valuation Γ R x ≤ exp (-g) ↔ (g : WithTop Γ) ≤ x.orderTop := by
  by_cases hx : x = 0
  · simp [hx]
  rw [valuation_eq_exp_neg_order hx, ← order_eq_orderTop_of_ne_zero hx, exp_le_exp, neg_le_neg_iff,
    WithTop.coe_le_coe]

/-- The valuation reverses the order: `v x ≤ v y` exactly when `ord y ≤ ord x`. -/
theorem valuation_le_valuation_iff :
    valuation Γ R x ≤ valuation Γ R y ↔ y.orderTop ≤ x.orderTop := by
  by_cases hy : y = 0
  · simp [hy]
  rw [valuation_eq_exp_neg_order hy, valuation_le_exp_neg_iff, order_eq_orderTop_of_ne_zero hy]

end HahnSeries
