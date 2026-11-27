/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
public import TauCeti.NumberTheory.LFunctions.Hecke.RieszRemainder

/-!
# Dirichlet and rational ray class Riesz remainders

Under the rational character comparison, the twisted von Mangoldt coefficients and the
main-term corrections agree. In particular, at conductor one the Euler–Kronecker constant
of `ℚ` is Euler's constant.
-/

public section

open ArithmeticFunction TauCeti.LFunctions

namespace TauCeti.PrimitiveDirichletCharacter

/-- The ray class remainder of the rational character corresponding to a primitive
Dirichlet character is its Dirichlet remainder, including at conductor one. -/
@[simp] theorem rieszRemainder_toPrimitiveRayClassCharacter (ψ : PrimitiveDirichletCharacter)
    (y : ℝ) : (toPrimitiveRayClassCharacter ψ).rieszRemainder y = ψ.rieszRemainder y := by
  have hcoeff : (toPrimitiveRayClassCharacter ψ).rieszCoeff = fun n : ℕ ↦ ψ.character n * Λ n := by
    rw [PrimitiveRayClassCharacter.rieszCoeff_def]
    exact funext (normCoeff_vonMangoldtTransform_toPrimitiveRayClassCharacter ψ)
  by_cases hψ : ψ = 1
  · subst ψ
    simp only [toPrimitiveRayClassCharacter_one, PrimitiveRayClassCharacter.rieszCoeff_one,
      character_one_apply, one_mul] at hcoeff
    rw [toPrimitiveRayClassCharacter_one, PrimitiveRayClassCharacter.rieszRemainder_one,
      hcoeff, rieszRemainder_one, NumberField.eulerKroneckerConstant_rat]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one]
  · have hη : toPrimitiveRayClassCharacter ψ ≠ 1 :=
      (toPrimitiveRayClassCharacter.injective.eq_iff' toPrimitiveRayClassCharacter_one).not.mpr hψ
    have hχ : ψ.character ≠ 1 := (character_eq_one_iff ψ).not.mpr hψ
    have hL : heckeLFunctionC (toPrimitiveRayClassCharacter ψ).character = ψ.character.LFunction :=
      funext fun _ ↦ ψ.heckeLFunctionC_toPrimitiveRayClassCharacter_apply (.inr hχ)
    rw [PrimitiveRayClassCharacter.rieszRemainder_of_ne_one _ hη, hcoeff, hL,
      rieszRemainder_of_ne_one hψ]

end TauCeti.PrimitiveDirichletCharacter
