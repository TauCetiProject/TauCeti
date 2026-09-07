/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.NumberTheory.NumberField.Index.Basic
import Mathlib.RingTheory.Adjoin.PowerBasis
import TauCeti.NumberTheory.NumberField.Minpoly
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# The power basis of an integral primitive element and its discriminant

An integral primitive element `θ` of a number field `K` generates `K` over `ℚ`, so its powers
`1, θ, …, θ ^ (n - 1)` form a `ℚ`-basis of `K`, where `n = [K : ℚ]`. This file packages that
basis as a `PowerBasis ℚ K` and identifies its discriminant with the discriminant of the minimal
polynomial of `θ` over `ℤ`, cast to `ℚ`.

## Main definitions

* `TauCeti.NumberField.IntegralPrimitiveElement.powerBasis`: the power basis
  `1, θ, …, θ ^ (n - 1)` of `K` over `ℚ`.

## Main results

* `TauCeti.NumberField.IntegralPrimitiveElement.discr_powerBasis_eq_minpoly_discr`: the
  discriminant of the power basis of `θ` is the polynomial discriminant of `minpoly ℤ θ`, cast to
  `ℚ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2.
-/

public section

open scoped NumberField

namespace TauCeti.NumberField.IntegralPrimitiveElement

variable {K : Type*} [Field K] [NumberField K]

/-- The power basis `1, θ, …, θ ^ (n - 1)` of `K` over `ℚ` attached to an integral primitive
element `θ`, where `n = [K : ℚ]`. -/
noncomputable def powerBasis (θ : IntegralPrimitiveElement K) : PowerBasis ℚ K :=
  PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite ℚ (θ.1 : K)) θ.2

/-- The generator of the power basis of `θ` is `θ`. -/
@[simp]
theorem powerBasis_gen (θ : IntegralPrimitiveElement K) : θ.powerBasis.gen = (θ.1 : K) := by
  rw [powerBasis, PowerBasis.ofAdjoinEqTop_gen]

/-- **The discriminant of the power basis of an integral primitive element** is the polynomial
discriminant of its minimal polynomial over `ℤ`, cast to `ℚ`. -/
theorem discr_powerBasis_eq_minpoly_discr (θ : IntegralPrimitiveElement K) :
    Algebra.discr ℚ θ.powerBasis.basis = algebraMap ℤ ℚ (minpoly ℤ θ.1).discr := by
  rw [Algebra.discr_powerBasis_eq_minpoly_discr, powerBasis_gen,
    _root_.NumberField.RingOfIntegers.minpoly_rat_coe,
    Polynomial.Monic.discr_map (minpoly.monic θ.1.isIntegral)]

end TauCeti.NumberField.IntegralPrimitiveElement
