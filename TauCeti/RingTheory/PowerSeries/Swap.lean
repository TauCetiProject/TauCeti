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
