/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
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
* `TauCeti.NumberField.minpoly_rat_eq_of_mem_rootSet`,
  `TauCeti.NumberField.minpoly_int_eq_of_coe_mem_rootSet`: a root, in another number field, of
  the minimal polynomial of `x` has the same minimal polynomials over `ℚ` and over `ℤ` as `x`.
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

variable {K : Type*} [Field K] [NumberField K] {M : Type*} [Field M] [NumberField M] {θ : 𝓞 K}

/-- A root in `M` of `minpoly ℚ θ` is a root of `minpoly ℤ θ`. -/
theorem aeval_minpoly_int_eq_zero_of_mem_rootSet {β : M}
    (hβ : β ∈ (minpoly ℚ (θ : K)).rootSet M) : aeval β (minpoly ℤ θ) = 0 := by
  have h := (mem_rootSet.mp hβ).2
  rwa [_root_.NumberField.RingOfIntegers.minpoly_rat_coe, aeval_map_algebraMap] at h

/-- A root in `M` of `minpoly ℚ θ` is an algebraic integer. -/
theorem isIntegral_of_mem_rootSet {β : M} (hβ : β ∈ (minpoly ℚ (θ : K)).rootSet M) :
    IsIntegral ℤ β :=
  ⟨minpoly ℤ θ, minpoly.monic θ.isIntegral, aeval_minpoly_int_eq_zero_of_mem_rootSet hβ⟩

/-- A root in `M` of `minpoly ℚ θ` has that polynomial as its minimal polynomial over `ℚ`. -/
theorem minpoly_rat_eq_of_mem_rootSet {β : M} (hβ : β ∈ (minpoly ℚ (θ : K)).rootSet M) :
    minpoly ℚ β = minpoly ℚ (θ : K) :=
  (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (IsIntegral.of_finite ℚ _))
    (mem_rootSet.mp hβ).2 (minpoly.monic (IsIntegral.of_finite ℚ _))).symm

/-- An algebraic integer of `M` that is a root of `minpoly ℚ θ` has the same minimal polynomial
over `ℤ` as `θ`. -/
theorem minpoly_int_eq_of_coe_mem_rootSet {β : 𝓞 M}
    (hβ : (β : M) ∈ (minpoly ℚ (θ : K)).rootSet M) : minpoly ℤ β = minpoly ℤ θ := by
  have h := minpoly_rat_eq_of_mem_rootSet hβ
  rw [_root_.NumberField.RingOfIntegers.minpoly_rat_coe,
    _root_.NumberField.RingOfIntegers.minpoly_rat_coe] at h
  exact Polynomial.map_injective _ (algebraMap ℤ ℚ).injective_int h

end TauCeti.NumberField
