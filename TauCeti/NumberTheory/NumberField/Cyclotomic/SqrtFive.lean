/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Subfields
public import TauCeti.RingTheory.RootsOfUnity.Fifth
import TauCeti.NumberTheory.NumberField.IntegralSqrt
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic.NormNum.IsSquare

/-!
# The quadratic subfield of the fifth cyclotomic field is `ℚ(√5)`

Every square root of five in a fifth cyclotomic field generates its unique quadratic
subfield. Such a root is given explicitly by `1 + 2 * (ζ + ζ⁻¹)` for any primitive fifth
root of unity `ζ`. Thus the intrinsic fixed-field description agrees with the familiar
square-root presentation, independently of the chosen model of the cyclotomic field.

## Reference

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 1.
-/

public section

open IntermediateField Polynomial
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]

/-- Either square root of five generates the unique quadratic subfield of a fifth
cyclotomic field. -/
theorem adjoin_sqrt_five_eq_fifthCyclotomicQuadraticSubfield {x : K} (hx : x ^ 2 = 5) :
    ℚ⟮x⟯ = fifthCyclotomicQuadraticSubfield := by
  apply IntermediateField.eq_fifthCyclotomicQuadraticSubfield_of_finrank_eq_two
  have hx' : x ^ 2 = algebraMap ℤ K 5 := by simpa using hx
  have hmin := _root_.NumberField.minpoly_integralSqrt hx' (by norm_num)
  have hfrac := minpoly.isIntegrallyClosed_eq_field_fractions ℚ K
    (IsIntegralClosure.isIntegral ℤ K (_root_.NumberField.integralSqrt hx'))
  rw [_root_.NumberField.algebraMap_integralSqrt, hmin] at hfrac
  rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ x), hfrac]
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.natDegree_X_pow_sub_C]

/-- The explicit square root `1 + 2 * (ζ + ζ⁻¹)` generates the quadratic subfield of
the fifth cyclotomic field. -/
theorem fifthCyclotomicQuadraticSubfield_eq_adjoin {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    fifthCyclotomicQuadraticSubfield = ℚ⟮1 + 2 * (ζ + ζ⁻¹)⟯ :=
  (adjoin_sqrt_five_eq_fifthCyclotomicQuadraticSubfield
    hζ.one_add_two_mul_add_inv_sq_of_five).symm

end TauCeti.NumberField
