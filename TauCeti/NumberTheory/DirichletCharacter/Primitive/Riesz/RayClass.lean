/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
public import TauCeti.NumberTheory.LFunctions.Hecke.RieszRemainder

/-!
# Riesz remainders of rational ray class characters

The rational character dictionary identifies the Dirichlet and ideal-theoretic first Riesz
remainders, including the constant in the conductor-one main term. This lets explicit formulas
for Dirichlet characters apply to prime-ideal sums over `ℚ`. The remainder normalization is that
of Levent Alpöge's `Deduction.Gchi`.
-/

public section

open ArithmeticFunction TauCeti.LFunctions
open scoped LSeries.notation

namespace TauCeti.PrimitiveDirichletCharacter

/-- The first Riesz remainder is preserved by the rational ray class character dictionary. -/
@[simp] theorem rieszRemainder_toPrimitiveRayClassCharacter (ψ : PrimitiveDirichletCharacter)
    (y : ℝ) : (toPrimitiveRayClassCharacter ψ).rieszRemainder y = ψ.rieszRemainder y := by
  have hc (n : ℕ) : (toPrimitiveRayClassCharacter ψ).rieszCoeff n = ψ.character n * Λ n := by
    rw [PrimitiveRayClassCharacter.rieszCoeff_def,
      ψ.normCoeff_vonMangoldtTransform_toPrimitiveRayClassCharacter]
  by_cases hψ : ψ = 1
  · subst ψ
    have hcoeff : normCoeff ℚ IdealArithmeticFunction.vonMangoldt = fun n ↦ (Λ n : ℂ) := by
      funext n
      simpa only [toPrimitiveRayClassCharacter_one, PrimitiveRayClassCharacter.rieszCoeff_one,
        character_one_apply, one_mul] using hc n
    rw [toPrimitiveRayClassCharacter_one, PrimitiveRayClassCharacter.rieszRemainder_one,
      rieszRemainder_one, NumberField.eulerKroneckerConstant_rat, hcoeff]
    push_cast
    rfl
  · have hne : toPrimitiveRayClassCharacter ψ ≠ 1 := fun h ↦
      hψ (toPrimitiveRayClassCharacter.injective (h.trans toPrimitiveRayClassCharacter_one.symm))
    have hL : heckeLFunctionC (toPrimitiveRayClassCharacter ψ).character = ψ.character.LFunction :=
      funext fun _ ↦ ψ.heckeLFunctionC_toPrimitiveRayClassCharacter_apply
        (.inr ((character_eq_one_iff ψ).not.mpr hψ))
    rw [PrimitiveRayClassCharacter.rieszRemainder_of_ne_one _ hne, rieszRemainder_of_ne_one hψ,
      funext hc, hL]

end TauCeti.PrimitiveDirichletCharacter
