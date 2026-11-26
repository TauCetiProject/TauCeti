/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The integral formal coordinate of the modular lambda function

With `E(q) = ∏_{n ≥ 1} (1 - q^n)`, the normalized modular lambda series is
`q (E(q) E(q⁴)² / E(q²)³)⁸`. Its linear coefficient is one, so this defines a strict
`FormalCoordinate ℤ`. The coordinate inverse represents `q` as a series in `λ / 16`,
and `FormalCoordinate.substAlgEquiv` gives the change of variables over any commutative
ring after base change.

## Main results

* `TauCeti.ModularForm.modularLambdaCoordinate`: the strict integral coordinate.
* `TauCeti.ModularForm.modularLambdaCoordinate_toPowerSeries`: its Euler-product formula.
* `TauCeti.ModularForm.modularLambdaCoordinate_coeff_one` and
  `TauCeti.ModularForm.modularLambdaCoordinate_coeff_two`: its coefficients in degrees one and two.
-/

public noncomputable section

open PowerSeries

namespace TauCeti.ModularForm

/-- The strict integral coordinate underlying the normalized modular lambda function. -/
def modularLambdaCoordinate : FormalCoordinate ℤ where
  toPowerSeries := X * (pentagonalSeries ℤ * ((pentagonalSeries ℤ).expand 4 (by decide)) ^ 2 *
    ((pentagonalSeries ℤ).expand 2 two_ne_zero).invOfUnit 1 ^ 3) ^ 8
  constantCoeff_toPowerSeries := by simp
  isUnit_coeff_one := by simp [constantCoeff_invOfUnit]

/-- The normalized series is the integral Euler quotient, expressed using the inverse of its
unit denominator. -/
theorem modularLambdaCoordinate_toPowerSeries :
    modularLambdaCoordinate.toPowerSeries = X *
      ((pentagonalSeries ℤ) * ((pentagonalSeries ℤ).expand 4 (by decide)) ^ 2 *
        ((pentagonalSeries ℤ).expand 2 two_ne_zero).invOfUnit 1 ^ 3) ^ 8 := by
  rw [modularLambdaCoordinate]

/-- The normalized modular lambda series has linear coefficient one. -/
@[simp]
theorem modularLambdaCoordinate_coeff_one :
    coeff 1 modularLambdaCoordinate.toPowerSeries = 1 := by
  simp [modularLambdaCoordinate_toPowerSeries, constantCoeff_invOfUnit]

/-- The quadratic coefficient of the normalized modular lambda series is `-8`. -/
@[simp]
theorem modularLambdaCoordinate_coeff_two :
    coeff 2 modularLambdaCoordinate.toPowerSeries = -8 := by
  let E := pentagonalSeries ℤ
  let E₂ := E.expand 2 two_ne_zero
  let E₄ := E.expand 4 (by decide)
  have h₀ : constantCoeff E = 1 := constantCoeff_pentagonalSeries ℤ
  have h₁ : coeff 1 E = -1 := coeff_one_pentagonalSeries ℤ
  have h₂ : coeff 1 E₂ = 0 := coeff_expand_of_not_dvd _ _ _ (by decide)
  have h₄ : coeff 1 E₄ = 0 := coeff_expand_of_not_dvd _ _ _ (by decide)
  have hi : coeff 1 (E₂.invOfUnit 1) = 0 := by
    have h := congrArg (coeff 1) (mul_invOfUnit (φ := E₂) (u := 1) (by simp [E₂, h₀]))
    rw [coeff_one_mul, h₂, zero_mul, zero_add] at h
    simpa [E₂, h₀] using h
  have hmain : modularLambdaCoordinate.toPowerSeries =
      X * (E * E₄ ^ 2 * (E₂.invOfUnit 1) ^ 3) ^ 8 :=
    modularLambdaCoordinate_toPowerSeries
  rw [hmain, coeff_succ_X_mul]
  norm_num [coeff_one_pow, coeff_one_mul, h₀, h₁, hi, h₄, E₄, constantCoeff_invOfUnit]

end TauCeti.ModularForm
