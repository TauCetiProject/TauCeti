/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Minimal polynomials of algebraic integers

An algebraic integer `x` of a number field `K` has a minimal polynomial over `ℤ`, as an element of
`𝓞 K`, and a minimal polynomial over `ℚ`, as an element of `K`. Since `ℤ` is integrally closed,
the second is the first with its coefficients cast to `ℚ`.

## Main results

* `NumberField.RingOfIntegers.minpoly_rat_coe`:
  `minpoly ℚ (x : K) = (minpoly ℤ x).map (algebraMap ℤ ℚ)`.
* `TauCeti.NumberField.minpoly_rat_eq_of_aeval_eq_zero`: a root of `minpoly ℚ x` in a nontrivial
  `ℚ`-algebra has the same minimal polynomial over `ℚ` as `x`.
* `TauCeti.NumberField.minpoly_int_eq_of_aeval_eq_zero`: a root of `minpoly ℚ x` in a commutative
  `ℚ`-algebra that is a domain has the same minimal polynomial over `ℤ` as `x`.
* `TauCeti.NumberField.minpoly_two_mul_sub_one_of_minpoly_eq_X_sq_sub_X_add`: an algebraic
  integer `ω` with minimal polynomial `X² - X + c` has `2ω - 1` with minimal polynomial
  `X² - (1 - 4c)`.
-/

public section

open scoped NumberField

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

/-- The minimal polynomial over `ℚ` of an algebraic integer `x`, viewed in `K`, is its minimal
polynomial over `ℤ` with the coefficients cast to `ℚ`. -/
theorem minpoly_rat_coe (x : 𝓞 K) :
    minpoly ℚ (x : K) = (minpoly ℤ x).map (algebraMap ℤ ℚ) := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ x.isIntegral_coe, minpoly_coe]

end NumberField.RingOfIntegers

namespace TauCeti.NumberField

open Polynomial

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

section RingTarget

variable {M : Type*} [Ring M] [Algebra ℚ M]

/-- In any `ℚ`-algebra, `minpoly ℚ θ` and `minpoly ℤ θ` take the same value at every element. -/
theorem aeval_minpoly_rat_eq_aeval_minpoly_int (β : M) :
    aeval β (minpoly ℚ (θ : K)) = aeval β (minpoly ℤ θ) := by
  rw [_root_.NumberField.RingOfIntegers.minpoly_rat_coe, aeval_map_algebraMap]

/-- A root of `minpoly ℚ θ` in a `ℚ`-algebra is an algebraic integer. -/
theorem isIntegral_of_aeval_eq_zero {β : M}
    (hβ : aeval β (minpoly ℚ (θ : K)) = 0) : IsIntegral ℤ β :=
  ⟨minpoly ℤ θ, minpoly.monic θ.isIntegral, by
    rwa [aeval_minpoly_rat_eq_aeval_minpoly_int] at hβ⟩

/-- A root of `minpoly ℚ θ` in a nontrivial `ℚ`-algebra has that polynomial as its minimal
polynomial over `ℚ`. -/
theorem minpoly_rat_eq_of_aeval_eq_zero [Nontrivial M] {β : M}
    (hβ : aeval β (minpoly ℚ (θ : K)) = 0) : minpoly ℚ β = minpoly ℚ (θ : K) :=
  (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (IsIntegral.of_finite ℚ _)) hβ
    (minpoly.monic (IsIntegral.of_finite ℚ _))).symm

end RingTarget

/-- A root of `minpoly ℚ θ` in a commutative `ℚ`-algebra that is a domain has the same minimal
polynomial over `ℤ` as `θ`. -/
theorem minpoly_int_eq_of_aeval_eq_zero {M : Type*} [CommRing M] [IsDomain M] [Algebra ℚ M]
    {β : M} (hβ : aeval β (minpoly ℚ (θ : K)) = 0) : minpoly ℤ β = minpoly ℤ θ := by
  have h := minpoly_rat_eq_of_aeval_eq_zero hβ
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (isIntegral_of_aeval_eq_zero hβ),
    _root_.NumberField.RingOfIntegers.minpoly_rat_coe] at h
  exact Polynomial.map_injective _ (algebraMap ℤ ℚ).injective_int h

/-- For an algebraic integer `ω` with minimal polynomial `X² - X + c` over `ℤ`, the element
`2ω - 1` is a square root of `1 - 4c`: its minimal polynomial over `ℤ` is `X² - (1 - 4c)`. This
converts the half-integer presentation of a quadratic field back into the radicand
presentation. -/
theorem minpoly_two_mul_sub_one_of_minpoly_eq_X_sq_sub_X_add {ω : 𝓞 K} {c : ℤ}
    (hmin : minpoly ℤ ω = X ^ 2 - X + C c) :
    minpoly ℤ (2 * ω - 1) = X ^ 2 - C (1 - 4 * c) := by
  -- Scaling the roots of `X² - X + c` by `2` gives the minimal polynomial `X² - 2X + 4c` of `2ω`.
  have hscale : minpoly ℤ ((2 : ℤ) • ω) = X ^ 2 - C 2 * X + C (4 * c) := by
    rw [IsIntegrallyClosed.minpoly_smul two_ne_zero ω.isIntegral, hmin]
    ext i
    rw [coeff_scaleRoots, show (X ^ 2 - X + C c : ℤ[X]).natDegree = 2 by compute_degree!]
    rcases i with _ | _ | _ | i <;> simp [coeff_X, coeff_C, -eq_intCast]
    ring
  -- Over `ℚ`, subtracting `1` composes the minimal polynomial with `X + 1`; the coefficient map
  -- `ℤ → ℚ` is injective.
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  rw [← _root_.NumberField.RingOfIntegers.minpoly_rat_coe,
    show ((2 * ω - 1 : 𝓞 K) : K) = (((2 : ℤ) • ω : 𝓞 K) : K) - algebraMap ℚ K 1 by simp,
    minpoly.sub_algebraMap, _root_.NumberField.RingOfIntegers.minpoly_rat_coe, hscale]
  simp
  ring

end TauCeti.NumberField
