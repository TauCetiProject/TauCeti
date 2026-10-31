/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Power series with a left inverse for substitution

Mathlib constructs the inverse for substitution of a power series `Q = uX + ⋯` whose linear
coefficient `u` is a unit (`PowerSeries.substInvOfIsUnit`). This file records the converse: if a
power series `Q` with nilpotent constant coefficient, so that it can be substituted, has a left
inverse `P` for substitution, `P(Q) = X`, then the linear coefficient of `Q` is a unit. Indeed the
chain rule gives `P'(Q) * Q' = 1`, so the derivative `Q'` is a unit of `R⟦X⟧`, and its constant
coefficient is the linear coefficient of `Q`.

If moreover `Q` has zero constant coefficient, then `Q` is `X` times a unit of `R⟦X⟧`, which is the
form used to change formal parameters.

## Main results

* `PowerSeries.isUnit_coeff_one_of_subst_eq_X`: if `Q` can be substituted and `P(Q) = X`, then the
  linear coefficient of `Q` is a unit.
* `PowerSeries.exists_unit_eq_X_mul_of_subst_eq_X`: if `constantCoeff Q = 0` and `P(Q) = X`, then
  `Q = X * v` for a unit `v` of `R⟦X⟧`.
* `PowerSeries.map_substInvOfIsUnit`: compositional inverses commute with coefficient maps.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- A power series `Q` with nilpotent constant coefficient that has a left inverse `P` for
substitution, `P(Q) = X`, has a unit of `R` as its linear coefficient. -/
theorem isUnit_coeff_one_of_subst_eq_X {P Q : R⟦X⟧} (hQ : HasSubst Q) (h : P.subst Q = X) :
    IsUnit (coeff 1 Q) := by
  -- by the chain rule, `P'(Q) * Q' = 1`
  have hd : (d⁄dX P).subst Q * d⁄dX Q = 1 := by rw [← derivative_subst hQ, h, derivative_X]
  -- so `Q'` is a unit, and its constant coefficient is the linear coefficient of `Q`
  simpa only [← coeff_zero_eq_constantCoeff_apply, coeff_derivative, Nat.cast_zero, zero_add,
    mul_one] using isUnit_iff_constantCoeff.mp (.of_mul_eq_one_right _ hd)

/-- A power series `Q` with zero constant coefficient that has a left inverse `P` for
substitution, `P(Q) = X`, is `X` times a unit of `R⟦X⟧`. -/
theorem exists_unit_eq_X_mul_of_subst_eq_X {P Q : R⟦X⟧} (hQ : constantCoeff Q = 0)
    (h : P.subst Q = X) : ∃ v : R⟦X⟧ˣ, Q = X * (v : R⟦X⟧) := by
  have hu := isUnit_coeff_one_of_subst_eq_X (.of_constantCoeff_zero' hQ) h
  obtain ⟨b, rfl⟩ := X_dvd_iff.mpr hQ
  -- the linear coefficient of `X * b` is the constant coefficient of `b`
  rw [coeff_succ_X_mul 0 b, coeff_zero_eq_constantCoeff_apply] at hu
  obtain ⟨v, rfl⟩ := isUnit_iff_constantCoeff.mpr hu
  exact ⟨v, rfl⟩

/-- The compositional inverse of a series `P = u X + ⋯` with `u` a unit commutes with applying a
ring homomorphism to the coefficients. -/
@[simp]
theorem map_substInvOfIsUnit {S : Type*} [CommRing S] (f : R →+* S) {P : R⟦X⟧}
    (hP : constantCoeff P = 0) (hP' : IsUnit (coeff 1 P)) :
    (P.substInvOfIsUnit hP').map f =
      (P.map f).substInvOfIsUnit (by simpa only [coeff_map] using hP'.map f) := by
  have hQ := HasSubst.substInvOfIsUnit P hP'
  refine (P.map f).eq_substInvOfIsUnit_of_subst_eq_X
    (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff, hP,
      map_zero]) _
    (.of_constantCoeff_zero' (by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff,
        constantCoeff_substInvOfIsUnit, map_zero])) ?_
  -- `PowerSeries.map` is `MvPowerSeries.map` on the unit index type.
  rw [show (P.substInvOfIsUnit hP').map f = MvPowerSeries.map f (P.substInvOfIsUnit hP') from rfl,
    ← map_subst hQ, P.subst_substInvOfIsUnit_right hP hP']
  exact map_X f

end PowerSeries
