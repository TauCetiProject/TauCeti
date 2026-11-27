/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.NumberTheory.LFunctions.Hecke.RieszRemainder.Family
import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz.ExplicitFormula
import TauCeti.NumberTheory.LSeries.RiemannZeta.FirstRieszSum

/-!
# Bounds for rational ray class Riesz remainders

The zeta and nonprincipal Dirichlet explicit formulas bound the individual first Riesz
remainders in terms of a zero-free half-plane. Over `ℚ`, the rational character dictionary
therefore gives the corresponding bound for an arbitrary finitely supported weighted family
of primitive ray class characters. The bound extends to signed real weights.
-/

public section

namespace TauCeti.LFunctions

/-- A primitive ray class character of `ℚ` that is zero-free right of `max σ (1 / 2)`
has first Riesz remainder bounded by `C * y ^ max σ (1 / 2)` for every `y ≥ 1`. -/
theorem PrimitiveRayClassCharacter.exists_norm_rieszRemainder_le_of_zeroFreeRightOf_rat
    (η : PrimitiveRayClassCharacter ℚ) {σ : ℝ}
    (hη : ZeroFreeRightOf (max σ (1 / 2)) (heckeLFunctionC η.character)) :
    ∃ C : ℝ, ∀ y ≥ 1, ‖η.rieszRemainder y‖ ≤ C * y ^ max σ (1 / 2) := by
  obtain ⟨ψ, rfl⟩ := PrimitiveDirichletCharacter.toPrimitiveRayClassCharacter.surjective η
  have hψ := (ψ.zeroFreeRightOf_heckeLFunctionC_toPrimitiveRayClassCharacter_iff _).mp hη
  simp only [PrimitiveDirichletCharacter.rieszRemainder_toPrimitiveRayClassCharacter]
  by_cases h : ψ = 1
  · subst ψ
    have hL : (1 : PrimitiveDirichletCharacter).character.LFunction = riemannZeta := by
      rw [PrimitiveDirichletCharacter.character_one]
      exact DirichletCharacter.LFunction_modOne_eq
    rw [hL] at hψ
    have h₀ : (0 : ℝ) ≤ max σ (1 / 2) := le_max_of_le_right (by norm_num)
    simpa only [max_eq_left h₀] using
      PrimitiveDirichletCharacter.exists_norm_rieszRemainder_one_le_rpow hψ
  · obtain ⟨C, hC⟩ := ψ.exists_norm_rieszRemainder_le_of_zeroFreeRightOf h
    refine ⟨C, ?_⟩
    simpa only [max_eq_left (le_max_right σ (1 / 2))] using hC hψ

/-- If each member of a weighted rational ray class family is zero-free right of
`max σ (1 / 2)`, its real first Riesz remainder has a power bound with that exponent.
No sign condition on the weights is needed. -/
theorem exists_norm_finsuppRieszRemainder_le_of_zeroFreeRightOf_rat
    (w : PrimitiveRayClassCharacter ℚ →₀ ℝ) {σ : ℝ}
    (h : ∀ η ∈ w.support, ZeroFreeRightOf (max σ (1 / 2)) (heckeLFunctionC η.character)) :
    ∃ C : ℝ, ∀ y ≥ 1, ‖finsuppRieszRemainder w y‖ ≤ C * y ^ max σ (1 / 2) :=
  exists_norm_finsuppRieszRemainder_le_rpow_of_forall_mem_support w fun η hmem ↦
    η.exists_norm_rieszRemainder_le_of_zeroFreeRightOf_rat (h η hmem)

end TauCeti.LFunctions
