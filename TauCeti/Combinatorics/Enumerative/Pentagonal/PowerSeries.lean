/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries

/-!
# The formal pentagonal series

The pentagonal series has constant coefficient one, linear coefficient minus one, and is preserved
by coefficient ring maps.

## Main results

* `PowerSeries.map_pentagonalSeries`: coefficient ring maps preserve the pentagonal series.
* `PowerSeries.constantCoeff_pentagonalSeries`: the constant coefficient is one.
* `PowerSeries.coeff_one_pentagonalSeries`: the linear coefficient is minus one.
-/

public section

namespace PowerSeries

/-- Applying a coefficient ring homomorphism to the pentagonal series preserves the series. -/
@[simp]
theorem map_pentagonalSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (pentagonalSeries R).map f = pentagonalSeries S := by
  ext n
  have hR := coeff_pentagonalSeries_mul_eq_extend R n (fun _ ↦ 1)
  have hS := coeff_pentagonalSeries_mul_eq_extend S n (fun _ ↦ 1)
  simp only [mul_one] at hR hS
  rw [coeff_map, hR, hS, Function.apply_extend ⇑f]
  simp [Function.comp_def, Int.coe_negOnePow, Pi.zero_def]

/-- The pentagonal series has constant coefficient one. -/
@[simp]
theorem constantCoeff_pentagonalSeries (R : Type*) [CommRing R] :
    constantCoeff (pentagonalSeries R) = 1 := by
  have hzero : pentagonal 0 = 0 := by norm_num [pentagonal_def]
  simpa [hzero, coeff_zero_eq_constantCoeff_apply] using
    coeff_pentagonalSeries_pentagonal R 0

/-- The linear coefficient of the pentagonal series is minus one. -/
@[simp]
theorem coeff_one_pentagonalSeries (R : Type*) [CommRing R] :
    coeff 1 (pentagonalSeries R) = -1 := by
  have hone : pentagonal 1 = 1 := by norm_num [pentagonal_def]
  simpa [hone] using coeff_pentagonalSeries_pentagonal R 1

end PowerSeries
