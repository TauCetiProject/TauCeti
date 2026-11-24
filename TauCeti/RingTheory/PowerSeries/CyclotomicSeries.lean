/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The cyclotomic series `f_a` and the smoothing series `F_a`

For a natural number `a`, the *cyclotomic series* is the finite geometric sum

`f_a(T) = ∑_{0 ≤ i < a} (1 + T) ^ i`,

so that `T f_a = (1 + T) ^ a - 1` (`PowerSeries.X_mul_cyclotomicSeries`). It is the polynomial
`((1 + T) ^ a - 1) / T` with the division by `T` carried out exactly: its coefficients are
`f_a[n] = choose a (n + 1)` (`PowerSeries.coeff_cyclotomicSeries`), so `f_0 = 0`, `f_1 = 1` and
`f_3 = 3 + 3T + T²`. Its constant coefficient is `a`, and `f_a` is a unit of `R⟦T⟧` exactly when
`a` is a unit of `R` (`PowerSeries.isUnit_cyclotomicSeries_iff`). Over `ℤ_p` with `p ∤ a` this is
the series `((1 + T) ^ a - 1) / T` of a `p`-adic cyclotomic unit, `(ζ ^ a - 1) / (ζ - 1)` at
`T = ζ - 1`.

When `a` is a unit of `R`, the *smoothing series* `F_a = smoothingSeries a ha` is the unique
power series with

`T f_a F_a = f_a - a`  (`PowerSeries.smoothingSeries_spec`, `PowerSeries.eq_smoothingSeries_iff`).

Formally `F_a = 1 / T - a / ((1 + T) ^ a - 1)`; neither term on the right is a power series, but
their difference is. Over `ℤ_p` with `p ∤ a`, this is the series that the theory of `p`-adic
measures identifies with the Amice transform of the Bernoulli distribution smoothed by `a`
(Rodrigues Jacinto–Williams, Proposition 4.11), whose moments are
`(1 - a ^ (k + 1)) B_(k+1) / (k + 1)`; that comparison is not made in this file. Here everything
is algebraic and holds over an arbitrary commutative ring: the inverse of `f_a` is the unit
inverse in `R⟦T⟧`, and no division by `T` or by `2` is used. The constant coefficient
satisfies `2 F_a[0] = a - 1` (`PowerSeries.two_mul_constantCoeff_smoothingSeries`), so it is
`(a - 1) / 2` when `2` is a unit (`PowerSeries.constantCoeff_smoothingSeries_of_isUnit_two`); for
`a = 3` over `ℤ₂`, where `2` is not a unit, it still gives `F_3[0] = 1`. Both series commute with
every change of coefficients (`PowerSeries.map_cyclotomicSeries`,
`PowerSeries.map_smoothingSeries`).

## Main definitions

* `PowerSeries.cyclotomicSeries a`: the series `f_a = ∑_{i < a} (1 + T) ^ i`.
* `PowerSeries.smoothingSeries a ha`: the series `F_a` with `T f_a F_a = f_a - a`, for `a` a unit.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Essential Number
  Theory 4 (2025), §4 (Proposition 4.4, Definition 4.10 and Proposition 4.11) and §10.2
  (Proposition 10.4 and Lemma 10.5).
-/

public section

noncomputable section

open Finset

namespace PowerSeries

variable {R S : Type*}

section Semiring

variable [Semiring R]

/-- The cyclotomic series `f_a = ∑_{i < a} (1 + X) ^ i`, so that `X f_a = (1 + X) ^ a - 1`. -/
def cyclotomicSeries (a : ℕ) : R⟦X⟧ :=
  ∑ i ∈ range a, (1 + X) ^ i

theorem cyclotomicSeries_def (a : ℕ) :
    (cyclotomicSeries a : R⟦X⟧) = ∑ i ∈ range a, (1 + X) ^ i := (rfl)

@[simp]
theorem cyclotomicSeries_zero : (cyclotomicSeries 0 : R⟦X⟧) = 0 := by
  simp [cyclotomicSeries_def]

@[simp]
theorem cyclotomicSeries_one : (cyclotomicSeries 1 : R⟦X⟧) = 1 := by
  simp [cyclotomicSeries_def]

theorem cyclotomicSeries_succ (a : ℕ) :
    (cyclotomicSeries (a + 1) : R⟦X⟧) = cyclotomicSeries a + (1 + X) ^ a := by
  simp [cyclotomicSeries_def, sum_range_succ]

/-- The coefficients of `(1 + X) ^ a` are the binomial coefficients. -/
theorem coeff_one_add_X_pow (a n : ℕ) : coeff n ((1 + X : R⟦X⟧) ^ a) = (a.choose n : R) := by
  rw [show (1 + X : R⟦X⟧) ^ a = ((1 + Polynomial.X : Polynomial R) ^ a : Polynomial R) by simp,
    Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-- The coefficients of the cyclotomic series: `f_a[n] = choose a (n + 1)`. -/
@[simp]
theorem coeff_cyclotomicSeries (a n : ℕ) :
    coeff n (cyclotomicSeries a : R⟦X⟧) = (a.choose (n + 1) : R) := by
  induction a with
  | zero => simp
  | succ a ih =>
    simp [cyclotomicSeries_succ, ih, coeff_one_add_X_pow, Nat.choose_succ_succ', add_comm]

@[simp]
theorem constantCoeff_cyclotomicSeries (a : ℕ) :
    constantCoeff (cyclotomicSeries a : R⟦X⟧) = a := by
  simp [← coeff_zero_eq_constantCoeff_apply]

/-- The cyclotomic series commutes with every change of coefficients. -/
@[simp]
theorem map_cyclotomicSeries [Semiring S] (f : R →+* S) (a : ℕ) :
    map f (cyclotomicSeries a : R⟦X⟧) = cyclotomicSeries a := by
  simp [cyclotomicSeries_def]

end Semiring

section Ring

variable [Ring R]

/-- The denominator factorization `X f_a = (1 + X) ^ a - 1`. -/
theorem X_mul_cyclotomicSeries (a : ℕ) :
    X * (cyclotomicSeries a : R⟦X⟧) = (1 + X) ^ a - 1 := by
  rw [cyclotomicSeries_def, ← mul_geom_sum, add_sub_cancel_left]

/-- The cyclotomic series `f_a` is a unit of `R⟦X⟧` exactly when `a` is a unit of `R`. -/
theorem isUnit_cyclotomicSeries_iff {a : ℕ} :
    IsUnit (cyclotomicSeries a : R⟦X⟧) ↔ IsUnit (a : R) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_cyclotomicSeries]

end Ring

section CommRing

variable [CommRing R] [CommRing S]

/-- The smoothing series: for `a` a unit, the power series `F_a` with `X f_a F_a = f_a - a`
(`smoothingSeries_spec`), formally `1 / X - a / ((1 + X) ^ a - 1)`. It is the quotient
`∑ₙ f_a[n + 1] Xⁿ` of `f_a - a` by `X`, multiplied by the unit inverse of `f_a`. -/
def smoothingSeries (a : ℕ) (ha : IsUnit (a : R)) : R⟦X⟧ :=
  mk (fun n ↦ coeff (n + 1) (cyclotomicSeries a : R⟦X⟧)) *
    ↑(isUnit_cyclotomicSeries_iff.2 ha).unit⁻¹

/-- The defining equation `X f_a F_a = f_a - a` of the smoothing series. -/
theorem smoothingSeries_spec (a : ℕ) (ha : IsUnit (a : R)) :
    X * cyclotomicSeries a * smoothingSeries a ha = cyclotomicSeries a - C (a : R) := by
  have hQ := sub_const_eq_X_mul_shift (cyclotomicSeries a : R⟦X⟧)
  rw [constantCoeff_cyclotomicSeries] at hQ
  rw [smoothingSeries, hQ]
  linear_combination (X * mk fun n ↦ coeff (n + 1) (cyclotomicSeries a : R⟦X⟧)) *
    (isUnit_cyclotomicSeries_iff.2 ha).mul_val_inv

/-- Without the factor `X`: `f_a F_a` is the quotient `∑ₙ f_a[n + 1] Xⁿ` of `f_a - a` by `X`. -/
theorem cyclotomicSeries_mul_smoothingSeries (a : ℕ) (ha : IsUnit (a : R)) :
    cyclotomicSeries a * smoothingSeries a ha = mk fun n ↦ coeff (n + 1) (cyclotomicSeries a) := by
  rw [smoothingSeries, mul_left_comm, (isUnit_cyclotomicSeries_iff.2 ha).mul_val_inv, mul_one]

/-- The smoothing series is the unique solution `F` of `X f_a F = f_a - a`. -/
theorem eq_smoothingSeries_iff {a : ℕ} (ha : IsUnit (a : R)) {F : R⟦X⟧} :
    F = smoothingSeries a ha ↔ X * cyclotomicSeries a * F = cyclotomicSeries a - C (a : R) := by
  refine ⟨fun h ↦ h ▸ smoothingSeries_spec a ha, fun h ↦ ?_⟩
  rw [← smoothingSeries_spec a ha, mul_assoc, mul_assoc] at h
  exact (isUnit_cyclotomicSeries_iff.2 ha).mul_left_cancel (X_mul_injective h)

@[simp]
theorem smoothingSeries_one (ha : IsUnit ((1 : ℕ) : R)) : smoothingSeries 1 ha = 0 := by
  rw [eq_comm, eq_smoothingSeries_iff]
  simp

/-- The constant coefficient of the smoothing series satisfies `2 F_a[0] = a - 1`, with no
division by `2`. -/
theorem two_mul_constantCoeff_smoothingSeries (a : ℕ) (ha : IsUnit (a : R)) :
    2 * constantCoeff (smoothingSeries a ha) = a - 1 := by
  have h := congrArg (coeff 1) (smoothingSeries_spec a ha)
  simp only [mul_assoc, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, map_mul,
    constantCoeff_cyclotomicSeries, map_sub, coeff_cyclotomicSeries, coeff_C, one_ne_zero,
    ↓reduceIte, sub_zero] at h
  refine ha.mul_left_cancel ?_
  rcases a with _ | a
  · simp
  · have hc : (a + 1) * a = (a + 1).choose 2 * 2 := by
      simpa using Nat.add_one_mul_choose_eq a 1
    have hc' : (((a + 1) * a : ℕ) : R) = ((a + 1).choose 2 * 2 : ℕ) := congrArg _ hc
    push_cast at h hc' ⊢
    linear_combination 2 * h - hc'

/-- When `2` is a unit, the constant coefficient of the smoothing series is `(a - 1) / 2`. -/
theorem constantCoeff_smoothingSeries_of_isUnit_two (a : ℕ) (ha : IsUnit (a : R))
    (h2 : IsUnit (2 : R)) : constantCoeff (smoothingSeries a ha) = ↑h2.unit⁻¹ * (a - 1) := by
  rw [← two_mul_constantCoeff_smoothingSeries, ← mul_assoc, h2.val_inv_mul, one_mul]

/-- The smoothing series commutes with every change of coefficients. -/
@[simp]
theorem map_smoothingSeries (f : R →+* S) {a : ℕ} (ha : IsUnit (a : R)) :
    map f (smoothingSeries a ha) = smoothingSeries a (by simpa using ha.map f) := by
  rw [eq_smoothingSeries_iff]
  simpa using congrArg (map f) (smoothingSeries_spec a ha)

end CommRing

end PowerSeries
