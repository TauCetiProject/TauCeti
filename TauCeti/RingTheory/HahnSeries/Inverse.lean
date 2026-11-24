/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.Summable

/-!
# `leadingCoeff` and `order` of inverses, quotients, and integer powers of Hahn series

Over a field of coefficients a nonzero Hahn series is invertible, `HahnSeries.leadingCoeff` is
multiplicative (`HahnSeries.leadingCoeff_mul`), and `HahnSeries.order` is additive on nonzero
products (`HahnSeries.order_mul`). This file records what those give for inversion, division, and
integer powers, complementing Mathlib's `HahnSeries.order_pow`.

There is deliberately no `orderTop` counterpart here. The other invariant already has one, and a
better one: `HahnSeries.addVal` is an `AddValuation` whose value is `orderTop`
(`HahnSeries.addVal_apply`), so `AddValuation.map_inv` and `AddValuation.map_div` give
`s⁻¹.orderTop = -s.orderTop` and `(s / t).orderTop = s.orderTop - t.orderTop` directly — and
without any nonzero hypothesis, since `-⊤ = ⊤` in the value group. By contrast, `HahnSeries.order`
takes values in `Γ` (with `(0 : HahnSeries Γ R).order = 0`), where `s⁻¹.order = -s.order` and
`(s ^ k).order = k • s.order` also hold unconditionally.

## Main results

* `HahnSeries.leadingCoeff_inv`: `s⁻¹.leadingCoeff = s.leadingCoeff⁻¹`.
* `HahnSeries.leadingCoeff_div`: `(s / t).leadingCoeff = s.leadingCoeff / t.leadingCoeff`.
* `HahnSeries.order_inv`: `s⁻¹.order = -s.order`.
* `HahnSeries.order_zpow`: `(s ^ k).order = k • s.order`.

All four hold with no nonzero hypothesis, since inversion, division by zero, and powers of zero
agree on both sides, and all four are `@[simp]`.

## Provenance

`leadingCoeff_inv` and `leadingCoeff_div` were ported from the AINTLIB `HasseWeil` project
(Apache-2.0), revision `513e83879e2f`, file `HasseWeil/HahnSeriesAux.lean`. That file's two further
declarations, `orderTop_inv_eq_neg` and `orderTop_div`, are **not** ported: they are the `addVal`
consequences described above, which the source predates. `order_inv` and `order_zpow` were added
directly for Tau Ceti.
-/

public section

namespace HahnSeries

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
variable {R : Type*} [Field R] {s t : HahnSeries Γ R}

/-- The leading coefficient of the inverse of a Hahn series over a field is the inverse of its
leading coefficient. No nonzero hypothesis is needed: at `s = 0` both sides are `0`. -/
@[simp]
theorem leadingCoeff_inv : s⁻¹.leadingCoeff = s.leadingCoeff⁻¹ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  exact eq_inv_of_mul_eq_one_right (by simp [← leadingCoeff_mul, hs])

/-- The leading coefficient of a quotient of Hahn series over a field is the quotient of the
leading coefficients, with no nonzero hypothesis: at `t = 0` both sides are `0`. -/
@[simp]
theorem leadingCoeff_div : (s / t).leadingCoeff = s.leadingCoeff / t.leadingCoeff := by
  simp [div_eq_mul_inv]

/-- The order of the inverse of a Hahn series over a field is the negation of its order. No nonzero
hypothesis is needed: at `s = 0` both sides are `0`. -/
@[simp]
theorem order_inv (s : HahnSeries Γ R) : s⁻¹.order = -s.order := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  have hmul := order_mul (inv_ne_zero hs) hs
  rw [inv_mul_cancel₀ hs, order_one] at hmul
  exact eq_neg_of_add_eq_zero_left hmul.symm

/-- The order of an integer power of a Hahn series over a field is the corresponding integer
multiple of its order, with no nonzero hypothesis. -/
@[simp]
theorem order_zpow (s : HahnSeries Γ R) (k : ℤ) : (s ^ k).order = k • s.order := by
  cases k with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, order_pow, natCast_zsmul]
  | negSucc n => rw [zpow_negSucc, order_inv, order_pow, negSucc_zsmul]

end HahnSeries
