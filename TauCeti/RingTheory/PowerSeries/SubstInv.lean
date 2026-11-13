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
* `PowerSeries.subst_eq_iff_eq_subst_substInvOfIsUnit`: substituting a series `P = u X + ⋯` with
  `u` a unit is undone by substituting its compositional inverse: `f(P) = g ↔ f = g(P⁻¹)`, so `f`
  is determined by `f(P)`.
* `PowerSeries.map_substInvOfIsUnit`: coefficient maps commute with the explicit construction
  `substInvOfIsUnit` for any series with a unit linear coefficient; it is a compositional inverse
  when the constant coefficient is zero.
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

/-- Substituting a series `P = u X + ⋯` with `u` a unit is undone by substituting its
compositional inverse: `f(P) = g` if and only if `f = g(P⁻¹)`. In particular a power series `f` is
determined by `f(P)`. -/
theorem subst_eq_iff_eq_subst_substInvOfIsUnit {P : R⟦X⟧} (hP : constantCoeff P = 0)
    (hP' : IsUnit (coeff 1 P)) {f g : R⟦X⟧} :
    f.subst P = g ↔ f = g.subst (P.substInvOfIsUnit hP') := by
  have hP₀ : HasSubst P := .of_constantCoeff_zero' hP
  have hQ := HasSubst.substInvOfIsUnit P hP'
  constructor <;> rintro rfl
  · rw [subst_comp_subst_apply hP₀ hQ, P.subst_substInvOfIsUnit_right hP hP', X_subst]
  · rw [subst_comp_subst_apply hQ hP₀, P.subst_substInvOfIsUnit_left hP hP', X_subst]

/-- The coefficients of the explicit construction `substInvFun` commute with ring homomorphisms,
for any series with an invertible linear coefficient. -/
private theorem map_substInvFun {S : Type*} [CommRing S] (f : R →+* S) (P : R⟦X⟧)
    [Invertible (coeff 1 P)] [Invertible (coeff 1 (P.map f))] (n : ℕ) :
    f (substInvFun P n) = substInvFun (P.map f) n := by
  have hinv : f (⅟(coeff 1 P)) = ⅟(coeff 1 (P.map f)) := by
    let _ : Invertible (f (coeff 1 P)) :=
      ‹Invertible (coeff 1 (P.map f))›.copy _ (coeff_map f 1 P).symm
    convert map_invOf f (coeff 1 P) using 1
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [substInvFun]
    | 1, _ => simp [substInvFun, hinv]
    | m + 2, ih =>
      have hS : HasSubst (∑ i : Fin (m + 2), C (substInvFun P i.1) * X ^ i.1) := by
        refine .of_constantCoeff_zero' ?_
        rw [map_sum]
        refine Finset.sum_eq_zero fun i _ ↦ ?_
        rcases i with ⟨_ | k, hk⟩
        · simp [substInvFun]
        · simp [map_pow]
      have key : map f (P.subst (∑ i : Fin (m + 2), C (substInvFun P i.1) * X ^ i.1)) =
          ((P.map f).subst (map f (∑ i : Fin (m + 2), C (substInvFun P i.1) * X ^ i.1))) :=
        map_subst hS P
      have hSm : map f (∑ i : Fin (m + 2), C (substInvFun P i.1) * X ^ i.1) =
          ∑ i : Fin (m + 2), C (substInvFun (P.map f) i.1) * X ^ i.1 := by
        simp only [map_sum, map_mul, map_C, map_pow, map_X]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [ih i (by omega)]
      rw [substInvFun, substInvFun, map_mul, map_neg, hinv, ← coeff_map, key, hSm]
      all_goals omega

/-- Applying a ring homomorphism to the coefficients commutes with the explicit construction
`substInvOfIsUnit`, for any series `P` whose linear coefficient is a unit; no condition on the
constant coefficient of `P` is needed. When `constantCoeff P = 0` this construction is the
compositional inverse of `P`. -/
@[simp]
theorem map_substInvOfIsUnit {S : Type*} [CommRing S] (f : R →+* S) {P : R⟦X⟧}
    (hP' : IsUnit (coeff 1 P)) :
    (P.substInvOfIsUnit hP').map f =
      (P.map f).substInvOfIsUnit (by simpa only [coeff_map] using hP'.map f) := by
  have hPf : IsUnit (coeff 1 (P.map f)) := by simpa only [coeff_map] using hP'.map f
  let := hP'.invertible
  let := hPf.invertible
  ext n
  simp only [substInvOfIsUnit, substInv, coeff_map, coeff_mk]
  exact map_substInvFun f P n

end PowerSeries
