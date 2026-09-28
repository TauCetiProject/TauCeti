/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Minimal polynomials of algebraic integers

An algebraic integer `x` of a number field `K` has a minimal polynomial over `ℤ`, as an element of
`𝓞 K`, and a minimal polynomial over `ℚ`, as an element of `K`. Since `ℤ` is integrally closed,
the second is the first with its coefficients cast to `ℚ`.

## Main results

* `NumberField.RingOfIntegers.minpoly_rat_coe`:
  `minpoly ℚ (x : K) = (minpoly ℤ x).map (algebraMap ℤ ℚ)`.
* `TauCeti.NumberField.minpoly_rat_eq_of_mem_rootSet`: a root in a commutative domain over `ℚ`
  has the same minimal polynomial over `ℚ` as `x`.
* `TauCeti.NumberField.minpoly_two_mul_sub_one_of_minpoly_eq_X_sq_sub_X_add`: an algebraic
  integer `ω` with minimal polynomial `X² - X + c` has `2ω - 1` with minimal polynomial
  `X² - (1 - 4c)`.
* `TauCeti.NumberField.minpoly_int_eq_of_coe_mem_rootSet`: an algebraic integer in another
  number field that is a root has the same minimal polynomial over `ℤ` as `x`.
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

section DomainTarget

variable {M : Type*} [CommRing M] [IsDomain M] [Algebra ℚ M]

/-- A root in `M` of `minpoly ℚ θ` is a root of `minpoly ℤ θ`. -/
theorem aeval_minpoly_int_eq_zero_of_mem_rootSet {β : M}
    (hβ : β ∈ (minpoly ℚ (θ : K)).rootSet M) : aeval β (minpoly ℤ θ) = 0 := by
  have h := (mem_rootSet.mp hβ).2
  rwa [_root_.NumberField.RingOfIntegers.minpoly_rat_coe, aeval_map_algebraMap] at h

/-- A root in `M` of `minpoly ℚ θ` is an algebraic integer. -/
theorem isIntegral_of_mem_rootSet {β : M}
    (hβ : β ∈ (minpoly ℚ (θ : K)).rootSet M) :
    IsIntegral ℤ β :=
  ⟨minpoly ℤ θ, minpoly.monic θ.isIntegral, aeval_minpoly_int_eq_zero_of_mem_rootSet hβ⟩

/-- A root in `M` of `minpoly ℚ θ` has that polynomial as its minimal polynomial over `ℚ`. -/
theorem minpoly_rat_eq_of_mem_rootSet {β : M}
    (hβ : β ∈ (minpoly ℚ (θ : K)).rootSet M) :
    minpoly ℚ β = minpoly ℚ (θ : K) :=
  (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (IsIntegral.of_finite ℚ _))
    (mem_rootSet.mp hβ).2 (minpoly.monic (IsIntegral.of_finite ℚ _))).symm

end DomainTarget

/-- An algebraic integer of a number field `M` that is a root of `minpoly ℚ θ` has the same
minimal polynomial over `ℤ` as `θ`. -/
theorem minpoly_int_eq_of_coe_mem_rootSet {M : Type*} [Field M] [NumberField M] {β : 𝓞 M}
    (hβ : (β : M) ∈ (minpoly ℚ (θ : K)).rootSet M) : minpoly ℤ β = minpoly ℤ θ := by
  have h := minpoly_rat_eq_of_mem_rootSet hβ
  rw [_root_.NumberField.RingOfIntegers.minpoly_rat_coe,
    _root_.NumberField.RingOfIntegers.minpoly_rat_coe] at h
  exact Polynomial.map_injective _ (algebraMap ℤ ℚ).injective_int h

/-- For an algebraic integer `ω` with minimal polynomial `X² - X + c` over `ℤ`, the element
`2ω - 1` is a square root of `1 - 4c`: its minimal polynomial over `ℤ` is `X² - (1 - 4c)`. This
converts the half-integer presentation of a quadratic field back into the radicand
presentation. -/
theorem minpoly_two_mul_sub_one_of_minpoly_eq_X_sq_sub_X_add {ω : 𝓞 K} {c : ℤ}
    (hmin : minpoly ℤ ω = X ^ 2 - X + C c) :
    minpoly ℤ (2 * ω - 1) = X ^ 2 - C (1 - 4 * c) := by
  have hdeg : (X ^ 2 - X + C c : ℤ[X]).natDegree = 2 := by
    simpa using (isMonicOfDegree_sub_add_two (R := ℤ) 1 c).natDegree_eq
  -- Scaling the roots of `X² - X + c` by `2` gives the minimal polynomial `X² - 2X + 4c` of `2ω`.
  have hscale : minpoly ℤ ((2 : ℤ) • ω) = X ^ 2 - C 2 * X + C (4 * c) := by
    rw [IsIntegrallyClosed.minpoly_smul two_ne_zero ω.isIntegral, hmin]
    ext i
    rw [coeff_scaleRoots, hdeg]
    rcases i with _ | _ | _ | i <;>
      simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul] <;> norm_num
    ring
  -- Over `ℚ`, subtracting `1` composes the minimal polynomial with `X + 1`; the coefficient map
  -- `ℤ → ℚ` is injective.
  have h2ω : (2 * ω - 1 : 𝓞 K) = (2 : ℤ) • ω - algebraMap ℤ (𝓞 K) 1 := by simp
  have hcoe : (((2 : ℤ) • ω - algebraMap ℤ (𝓞 K) 1 : 𝓞 K) : K) =
      (((2 : ℤ) • ω : 𝓞 K) : K) - algebraMap ℚ K 1 := by
    push_cast
    simp
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  rw [← _root_.NumberField.RingOfIntegers.minpoly_rat_coe, h2ω, hcoe, minpoly.sub_algebraMap,
    _root_.NumberField.RingOfIntegers.minpoly_rat_coe, hscale]
  simp
  ring

end TauCeti.NumberField
