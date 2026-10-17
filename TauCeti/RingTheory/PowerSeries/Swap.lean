/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Exchanging the variables of an iterated power series

A power series in `v` whose coefficients are power series in `u`, an element of `R⟦X⟧⟦X⟧`, is a
power series in the two variables `u` and `v`: the coefficient of `uᵃ vᵇ` in `G` is
`coeff a (coeff b G)`. This file defines the exchange of the two variables, `PowerSeries.swap`,
as a ring homomorphism. It is an involution.

## Main definitions

* `PowerSeries.swap`: the ring homomorphism `R⟦X⟧⟦X⟧ → R⟦X⟧⟦X⟧` exchanging the two variables.

## Main results

* `PowerSeries.coeff_coeff_swap`: the coefficient of `uᵃ vᵇ` in `swap G` is that of `uᵇ vᵃ` in
  `G`.
* `PowerSeries.swap_swap`: `swap` is an involution.
* `PowerSeries.swap_C`, `PowerSeries.swap_map_C`, `PowerSeries.swap_X`: `swap` exchanges the
  power series in the inner variable `u`, embedded as constants, with those in the outer variable
  `v`, embedded through `map C`.
* `Polynomial.coeff_coeff_swapPowerSeries`: the coefficient of `Xⁱ` in the `tᵏ`-coefficient of
  `swapPowerSeries Q` is the `tᵏ`-coefficient of the coefficient of `Xⁱ` in `Q`.
* `Polynomial.swapPowerSeries_C`, `Polynomial.swapPowerSeries_X`: the values of
  `swapPowerSeries` on constants and on the polynomial variable.
* `Polynomial.swapPowerSeries_injective`: `swapPowerSeries` is injective.
-/

public section

namespace PowerSeries

variable {R : Type*} [Semiring R]

/-- The exchange of the two variables of `R⟦X⟧⟦X⟧`, viewed as power series in `u` and `v`: the
coefficient of `uᵃ vᵇ` in `swap G` is the coefficient of `uᵇ vᵃ` in `G`. -/
noncomputable def swap : R⟦X⟧⟦X⟧ →+* R⟦X⟧⟦X⟧ where
  toFun G := mk fun b ↦ mk fun a ↦ coeff b (coeff a G)
  map_one' := by
    refine PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ ?_
    simp only [coeff_mk, coeff_one]
    split_ifs <;> simp_all
  map_mul' G H := by
    refine PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ ?_
    simp only [coeff_mk, coeff_mul, map_sum]
    exact Finset.sum_comm
  map_zero' := by
    refine PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ ?_
    simp
  map_add' G H := by
    refine PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ ?_
    simp

/-- The coefficient of `uᵃ vᵇ` in `swap G` is the coefficient of `uᵇ vᵃ` in `G`. -/
@[simp]
theorem coeff_coeff_swap (G : R⟦X⟧⟦X⟧) (a b : ℕ) :
    coeff a (coeff b (swap G)) = coeff b (coeff a G) := by
  simp [swap]

/-- Exchanging the variables twice is the identity. -/
@[simp]
theorem swap_swap (G : R⟦X⟧⟦X⟧) : swap (swap G) = G :=
  PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ by simp

/-- Exchanging the variables sends a power series in the inner variable `u` to the same power
series in the outer variable `v`. -/
@[simp]
theorem swap_C (f : R⟦X⟧) : swap (C f) = map C f :=
  PowerSeries.ext fun b ↦ PowerSeries.ext fun a ↦ by
    simp only [coeff_coeff_swap, coeff_C, coeff_map]
    split_ifs <;> simp

/-- Exchanging the variables sends a power series in the outer variable `v` to the same power
series in the inner variable `u`. -/
@[simp]
theorem swap_map_C (f : R⟦X⟧) : swap (map C f) = C f := by
  rw [← swap_C, swap_swap]

/-- Exchanging the variables sends the outer variable `v` to the inner variable `u`. -/
@[simp]
theorem swap_X : swap (X : R⟦X⟧⟦X⟧) = C X := by
  rw [← map_X (C (R := R)), swap_map_C]

end PowerSeries

open scoped Polynomial PowerSeries

namespace Polynomial

variable {R : Type*} [CommSemiring R]

/-- The ring homomorphism `R⟦X⟧[X] →+* R[X]⟦X⟧` exchanging the two variables: a polynomial in
`X` whose coefficients are power series in `t` is sent to the power series in `t` whose
coefficients are polynomials in `X`. -/
noncomputable def swapPowerSeries : R⟦X⟧[X] →+* R[X]⟦X⟧ :=
  eval₂RingHom (PowerSeries.map C) (PowerSeries.C X)

/-- `swapPowerSeries` sends a constant power series in `t` to the same power series with
constant polynomial coefficients. -/
@[simp]
theorem swapPowerSeries_C (a : R⟦X⟧) : swapPowerSeries (C a) = PowerSeries.map C a :=
  eval₂_C _ _

/-- `swapPowerSeries` sends the polynomial variable to the constant power series `X`. -/
@[simp]
theorem swapPowerSeries_X : swapPowerSeries (X : R⟦X⟧[X]) = PowerSeries.C (X : R[X]) :=
  eval₂_X _ _

/-- The coefficient of `Xⁱ` in the `tᵏ`-coefficient of `swapPowerSeries Q` is the
`tᵏ`-coefficient of the coefficient of `Xⁱ` in `Q`. -/
@[simp]
theorem coeff_coeff_swapPowerSeries (Q : R⟦X⟧[X]) (k i : ℕ) :
    (PowerSeries.coeff k (swapPowerSeries Q)).coeff i = PowerSeries.coeff k (Q.coeff i) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    simp only [swapPowerSeries, coe_eval₂RingHom, eval₂_monomial, ← map_pow,
      PowerSeries.coeff_mul_C, PowerSeries.coeff_map, coeff_C_mul_X_pow, coeff_monomial]
    split_ifs <;> simp_all

/-- The constant coefficient of `swapPowerSeries Q` is the reduction of `Q` modulo `t`. -/
@[simp]
theorem constantCoeff_swapPowerSeries (Q : R⟦X⟧[X]) :
    PowerSeries.constantCoeff (swapPowerSeries Q) = Q.map PowerSeries.constantCoeff := by
  ext i
  rw [coeff_map, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coeff_swapPowerSeries]

/-- A polynomial over `R⟦t⟧` is determined by its image under `swapPowerSeries`. -/
theorem swapPowerSeries_injective : Function.Injective (swapPowerSeries (R := R)) := by
  intro P Q h
  ext i k
  rw [← coeff_coeff_swapPowerSeries, h, coeff_coeff_swapPowerSeries]

end Polynomial
