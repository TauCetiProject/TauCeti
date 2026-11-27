/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Norm
import TauCeti.RingTheory.Norm.Quadratic

/-!
# Integral norms in imaginary quadratic fields

The integral norm in an imaginary quadratic field is the product with the complex conjugate.
This converts an integral norm witness into a witness for a prescribed conjugate product.
-/

public section

open scoped NumberField

open NumberField.IsCMField

namespace NumberField.RingOfIntegers

/-- In an imaginary quadratic field, the product of an algebraic integer with its conjugate
is the image of its integral norm. -/
theorem intCast_norm_eq_mul_complexConj {K : Type*} [Field K] [NumberField K]
    [IsCMField K] [Algebra.IsQuadraticExtension ℚ K] (z : 𝓞 K) :
    (Algebra.norm ℤ z : 𝓞 K) = z * ringOfIntegersComplexConj K z := by
  let σ : K ≃ₐ[ℚ] K := (complexConj K).restrictScalars ℚ
  have hσ : σ ≠ 1 := by
    intro h
    apply complexConj_ne_one K
    ext x
    simpa only [σ, AlgEquiv.restrictScalars_apply, AlgEquiv.one_apply] using
      DFunLike.congr_fun h x
  apply RingOfIntegers.coe_injective
  have hnorm := Algebra.IsQuadraticExtension.algebraMap_norm_eq_mul ℚ K hσ (z : K)
  rw [← Algebra.coe_norm_int, map_intCast] at hnorm
  rw [map_mul, map_intCast, ← coe_eq_algebraMap, ← coe_eq_algebraMap,
    coe_ringOfIntegersComplexConj]
  simpa only [σ, AlgEquiv.restrictScalars_apply] using hnorm

end NumberField.RingOfIntegers
