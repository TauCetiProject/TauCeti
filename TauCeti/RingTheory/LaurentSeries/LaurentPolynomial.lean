/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.LaurentSeries

/-!
# Laurent polynomials as Laurent series

A Laurent polynomial is a Laurent series with finitely many nonzero coefficients. This file
defines the ring homomorphism `LaurentPolynomial.toLaurentSeries : R[T;T⁻¹] →+* R⸨X⸩` sending `T`
to `X`, and shows that it preserves coefficients, so in particular it is injective.

## Main definitions

* `LaurentPolynomial.toLaurentSeries`: the inclusion of Laurent polynomials into Laurent series.

## Main results

* `LaurentPolynomial.toLaurentSeries_T`: `Tⁿ` is sent to `Xⁿ`, for every integer `n`.
* `LaurentPolynomial.coeff_toLaurentSeries`: the inclusion preserves coefficients.
* `LaurentPolynomial.toLaurentSeries_injective`: the inclusion is injective.
-/

public section

open scoped LaurentPolynomial LaurentSeries

namespace LaurentPolynomial

variable {R : Type*} [CommSemiring R]

/-- `X` as a unit of `R⸨X⸩`, with inverse `X⁻¹`. -/
private noncomputable def singleOneUnit : (R⸨X⸩)ˣ where
  val := HahnSeries.single 1 1
  inv := HahnSeries.single (-1) 1
  val_inv := by simp
  inv_val := by simp

private theorem val_singleOneUnit_zpow (n : ℤ) :
    ((singleOneUnit (R := R) ^ n : (R⸨X⸩)ˣ) : R⸨X⸩) = HahnSeries.single n 1 := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul, ih]
    simp [singleOneUnit]
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, ih]
    simp [singleOneUnit, sub_eq_add_neg]

/-- The inclusion of Laurent polynomials into Laurent series, sending `T` to `X`. -/
noncomputable def toLaurentSeries : R[T;T⁻¹] →+* R⸨X⸩ :=
  eval₂ HahnSeries.C singleOneUnit

/-- `Tⁿ` is sent to `Xⁿ`, for every integer `n`. -/
@[simp]
theorem toLaurentSeries_T (n : ℤ) : toLaurentSeries (T n : R[T;T⁻¹]) = HahnSeries.single n 1 := by
  rw [toLaurentSeries, eval₂_T, val_singleOneUnit_zpow]

/-- Constants are sent to constants. -/
@[simp]
theorem toLaurentSeries_C (r : R) : toLaurentSeries (C r) = HahnSeries.C r := by
  rw [toLaurentSeries, eval₂_C]

/-- The inclusion of Laurent polynomials into Laurent series preserves coefficients. -/
@[simp]
theorem coeff_toLaurentSeries (p : R[T;T⁻¹]) (n : ℤ) :
    (toLaurentSeries p).coeff n = p.coeff n := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | C_mul_T m r =>
    rw [map_mul, toLaurentSeries_T, toLaurentSeries_C, ← single_eq_C_mul_T, HahnSeries.C_apply,
      HahnSeries.single_mul_single, zero_add, mul_one, HahnSeries.coeff_single,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    simp [eq_comm]

/-- The inclusion of Laurent polynomials into Laurent series is injective. -/
theorem toLaurentSeries_injective : Function.Injective (toLaurentSeries (R := R)) :=
  fun p q h ↦ LaurentPolynomial.ext fun n ↦ by
    rw [← coeff_toLaurentSeries, h, coeff_toLaurentSeries]

end LaurentPolynomial
