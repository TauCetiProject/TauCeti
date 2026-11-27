/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.NumberTheory.LFunctions.Hecke.FamilyRieszRemainder
import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz.ExplicitFormula
import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz.RayClass
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

/-- A primitive ray class character of `ℚ` that is zero-free right of `σ` has first Riesz
remainder bounded by `C * y ^ max σ (1 / 2)` for every `y ≥ 1`. -/
theorem PrimitiveRayClassCharacter.exists_norm_rieszRemainder_le_of_zeroFreeRightOf_rat
    (η : PrimitiveRayClassCharacter ℚ) {σ : ℝ}
    (hη : ZeroFreeRightOf σ (heckeLFunctionC η.character)) :
    ∃ C : ℝ, ∀ y ≥ 1, ‖η.rieszRemainder y‖ ≤ C * y ^ max σ (1 / 2) := by
  obtain ⟨ψ, rfl⟩ := PrimitiveDirichletCharacter.toPrimitiveRayClassCharacter.surjective η
  have hψ := (zeroFreeRightOf_congr
    (fun s _ ↦ ψ.heckeLFunctionC_toPrimitiveRayClassCharacter_eventuallyEq s)).mp hη
  simp only [PrimitiveDirichletCharacter.rieszRemainder_toPrimitiveRayClassCharacter]
  by_cases h : ψ = 1
  · subst ψ
    have hL : (1 : PrimitiveDirichletCharacter).character.LFunction = riemannZeta := by
      rw [PrimitiveDirichletCharacter.character_one]
      exact DirichletCharacter.LFunction_modOne_eq
    rw [hL] at hψ
    obtain ⟨C, hC⟩ := PrimitiveDirichletCharacter.exists_norm_rieszRemainder_one_le_rpow hψ
    have hC₀ : 0 ≤ C := (norm_nonneg _).trans (by simpa using hC 1 le_rfl)
    have hmax : max σ 0 ≤ max σ (1 / 2) := max_le_max_left σ (by norm_num)
    exact ⟨C, fun y hy ↦ (hC y hy).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hy hmax) hC₀)⟩
  · obtain ⟨C, hC⟩ := ψ.exists_norm_rieszRemainder_le_of_zeroFreeRightOf h
    exact ⟨C, hC hψ⟩

/-- If each member of a weighted rational ray class family is zero-free right of `σ`, its
real first Riesz remainder has a power bound with exponent `max σ (1 / 2)`. No sign condition
on the weights is needed. -/
theorem exists_abs_familyRieszRemainder_le_of_zeroFreeRightOf_rat
    (w : PrimitiveRayClassCharacter ℚ →₀ ℝ) {σ : ℝ}
    (h : ∀ η ∈ w.support, ZeroFreeRightOf σ (heckeLFunctionC η.character)) :
    ∃ C : ℝ, ∀ y ≥ 1, |familyRieszRemainder ℚ w y| ≤ C * y ^ max σ (1 / 2) :=
  exists_abs_familyRieszRemainder_le_rpow_of_forall ℚ w fun η hmem ↦
    η.exists_norm_rieszRemainder_le_of_zeroFreeRightOf_rat (h η hmem)

end TauCeti.LFunctions
