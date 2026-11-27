/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.ZeroSide
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
import TauCeti.Analysis.MellinTransform.Uniqueness
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Growth
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros

/-!
# The first Riesz explicit formula for nonprincipal Dirichlet characters

For a primitive nonprincipal character and cutoffs `y ≥ 1`, the smoothed prime remainder is equal to
the sum over the zeros of the entire completion together with the negative gamma-pole and origin
corrections. If the L-function has no zeros in `Re s > σ`, the norm of the remainder is bounded by
`C y ^ max σ (1 / 2)` for `y ≥ 1`, with `C` independent of `σ`.

The prime-side normalization is that of Levent Alpöge's `Deduction.Gchi`. The formula
uses `DirichletCharacter.rieszZeroSide`, with the completion and Hadamard expansion
normalized as in Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
-/

public section

open Complex Set TauCeti.LFunctions

namespace TauCeti.PrimitiveDirichletCharacter

/-- The first Riesz remainder of a nonprincipal primitive character equals its completed zero
sum with the gamma-pole and origin corrections, including at the lower cutoff `1`. -/
theorem rieszRemainder_eq_rieszZeroSide (χ : PrimitiveDirichletCharacter) (hχ : χ ≠ 1)
    {y : ℝ} (hy : 1 ≤ y) :
    χ.rieszRemainder y = χ.character.rieszZeroSide χ.isPrimitive y := by
  have hne := (character_eq_one_iff χ).not.mpr hχ
  have ht : 1 < (2 : ℂ).re := by norm_num
  refine eqOn_Ici_of_mellin_integral_Ioi_eq_on_verticalLine (c := 2) (by norm_num)
    χ.continuous_rieszRemainder.continuousOn (χ.character.continuousOn_rieszZeroSide χ.isPrimitive)
    ?_ ?_ ?_ hy
  · simpa only [ofReal_ofNat, smul_eq_mul, mul_comm] using
      χ.integrableOn_rieszRemainder_mul_cpow ht
  · simpa only [ofReal_ofNat, smul_eq_mul, mul_comm] using
      (χ.character.integrableOn_rieszZeroSide_mul_cpow_and_setIntegral_eq_rieszRemainderMellin
        χ.isPrimitive hne ht).1
  · intro s hs
    have hs' : 1 < s.re := hs.symm ▸ (by norm_num : (1 : ℝ) < 2)
    simpa only [smul_eq_mul, mul_comm] using (χ.integral_rieszRemainder_mul_cpow hs').trans
      (χ.character.integrableOn_rieszZeroSide_mul_cpow_and_setIntegral_eq_rieszRemainderMellin
        χ.isPrimitive hne hs').2.symm

/-- For a nonprincipal primitive character, a zero-free half-plane `Re s > σ` bounds the first
Riesz remainder by `C y ^ max σ (1 / 2)` on `y ≥ 1`. The constant depends only on the character.
In particular the bound has exponent `σ` when `1 / 2 ≤ σ`. -/
theorem exists_norm_rieszRemainder_le_of_zeroFreeRightOf (χ : PrimitiveDirichletCharacter)
    (hχ : χ ≠ 1) : ∃ C : ℝ, ∀ {σ : ℝ}, ZeroFreeRightOf σ χ.character.LFunction →
      ∀ y ≥ 1, ‖χ.rieszRemainder y‖ ≤ C * y ^ max σ (1 / 2) := by
  let F := (dirichletData χ.character χ.isPrimitive).entireCompletion
  let A := ∑' ρ : (MeromorphicOn.divisor F univ).support,
    ‖((MeromorphicOn.divisor F univ ρ).toNat : ℂ) / (ρ * (1 - ρ))‖
  let a := χ.character.gammaPoleOffset
  let c := logDerivFinitePart χ.character.LFunction 0
  let m : ℂ := (meromorphicOrderAt χ.character.LFunction 0).untop₀
  have hne := (character_eq_one_iff χ).not.mpr hχ
  have ha : 0 < a := χ.character.gammaPoleOffset_pos
  obtain ⟨B, hB⟩ := exists_norm_rieszGammaCorrection_le ha (by norm_num : (0 : ℝ) < 2)
  have hB₀ : 0 ≤ B := by simpa using (norm_nonneg _).trans (hB 1 le_rfl)
  refine ⟨A + B + (‖c‖ + 3 * ‖m‖), fun {σ} hσ y hy ↦ ?_⟩
  have hzeros : ∀ ρ, F ρ = 0 → ρ.re ≤ max σ (1 / 2) := by
    intro ρ hρ
    have hρ₀ := re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ.character χ.isPrimitive hρ
    have hcompare := dirichletData_entireCompletion_eq_zero_iff χ.character χ.isPrimitive hne hρ₀.1
    have hL := hcompare.mp hρ
    have hpos := χ.character.meromorphicOrderAt_LFunction_pos_iff.mpr ⟨hL, .inr hne⟩
    exact le_max_of_le_left (not_lt.mp fun h ↦ ((zeroFreeRightOf_iff.mp hσ) ρ h).not_gt hpos)
  have hF := (dirichletData_hasMeromorphicContinuation χ.character
    χ.isPrimitive).differentiable_entireCompletion
  have hZ : ‖rieszZeroSeries F y‖ ≤ A * y ^ max σ (1 / 2) :=
    (dirichletData_entireCompletion_orderLE_one χ.character χ.isPrimitive).norm_rieszZeroSeries_le
      hF (by norm_num) hzeros hy
  -- The negative gamma-pole sum decays; the origin term grows at most logarithmically.
  have h₁ : 1 ≤ y ^ max σ (1 / 2) := Real.one_le_rpow hy (le_max_of_le_right (by norm_num))
  have hG : ‖rieszGammaCorrection a 2 y‖ ≤ B * y ^ max σ (1 / 2) :=
    (hB y hy).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hy (le_max_of_le_right (by linarith))) hB₀)
  have hlog : Real.log y ≤ 2 * y ^ max σ (1 / 2) := by
    calc Real.log y ≤ y ^ (1 / 2 : ℝ) / (1 / 2) :=
          Real.log_le_rpow_div (zero_le_one.trans hy) (by norm_num)
      _ = 2 * y ^ (1 / 2 : ℝ) := by ring
      _ ≤ 2 * y ^ max σ (1 / 2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy (le_max_right _ _))
          (by norm_num)
  have hE : ‖c + m * (1 + (Real.log y : ℂ))‖ ≤ (‖c‖ + 3 * ‖m‖) * y ^ max σ (1 / 2) := by
    refine (norm_add_le _ _).trans ?_
    have hlog₀ : 0 ≤ 1 + Real.log y := by linarith [Real.log_nonneg hy]
    have hnorm : ‖(1 : ℂ) + (Real.log y : ℂ)‖ = 1 + Real.log y := by
      simpa only [ofReal_add, ofReal_one] using Complex.norm_of_nonneg hlog₀
    rw [norm_mul, hnorm]
    calc ‖c‖ + ‖m‖ * (1 + Real.log y)
        ≤ ‖c‖ * y ^ max σ (1 / 2) + ‖m‖ * (3 * y ^ max σ (1 / 2)) := by
          exact add_le_add (le_mul_of_one_le_right (norm_nonneg _) h₁)
            (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _))
      _ = _ := by ring
  rw [χ.rieszRemainder_eq_rieszZeroSide hχ hy, χ.character.rieszZeroSide_def χ.isPrimitive]
  simpa only [add_mul] using norm_add₃_le.trans (add_le_add (add_le_add hZ hG) hE)

end TauCeti.PrimitiveDirichletCharacter
