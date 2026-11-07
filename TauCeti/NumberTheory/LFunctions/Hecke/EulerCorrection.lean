/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.NumberTheory.LFunctions.Hecke.Primitive
public import TauCeti.NumberTheory.NumberField.Ideal.LogNorm
public import TauCeti.Analysis.SpecialFunctions.Pow.EulerFactor

/-!
# Zeros and logarithmic derivatives of imprimitive Hecke Euler corrections

The native finite correction `RayClassCharacter.eulerCorrection` can vanish only on
`Re s = 0`. On `Re s ≥ 1` its logarithmic derivative is bounded in norm by
`log N(𝔫₀)`, where `𝔫₀` is the finite part of the presentation modulus.
The bound is uniform in the field and character. It controls the error contributed
by deleted Euler factors in logarithmic-derivative zero-free-region arguments.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 5.
-/

public section

open IsDedekindDomain Complex
open scoped NumberField

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- Every zero of the finite Euler correction lies on the imaginary axis. -/
theorem re_eq_zero_of_eulerCorrection_eq_zero (χ : RayClassCharacter 𝔪)
    (𝔫 : Modulus K) {s : ℂ} (hs : χ.eulerCorrection 𝔫 s = 0) : s.re = 0 := by
  classical
  rw [eulerCorrection_eq_prod_support] at hs
  obtain ⟨P, _, hP⟩ := Finset.prod_eq_zero_iff.mp hs
  have hane : χ.toMultiplicativeIdealWeight P.asIdeal ≠ 0 := by
    intro ha
    simp [ha] at hP
  have hgood : χ.toUnitaryIdealWeight.1.IsGood P.asIdeal := by
    apply (MultiplicativeIdealWeight.apply_ne_zero_iff_isGood _ _).mp
    simpa using hane
  have hnorm : ‖χ.toMultiplicativeIdealWeight P.asIdeal‖ = 1 := by
    simpa using χ.toUnitaryIdealWeight.norm_eq_one hgood
  have hz : 1 - χ.toMultiplicativeIdealWeight P.asIdeal *
      ((Ideal.absNorm P.asIdeal : ℝ) : ℂ) ^ (-s) = 0 := by simpa using hP
  exact re_eq_zero_of_one_sub_mul_ofReal_cpow_neg_eq_zero
    (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P) hnorm hz

/-- The finite Euler correction is nonzero off the imaginary axis. -/
theorem eulerCorrection_ne_zero_of_re_ne_zero (χ : RayClassCharacter 𝔪)
    (𝔫 : Modulus K) {s : ℂ} (hs : s.re ≠ 0) : χ.eulerCorrection 𝔫 s ≠ 0 :=
  fun hz ↦ hs (re_eq_zero_of_eulerCorrection_eq_zero χ 𝔫 hz)

/-- The logarithmic derivative of the Euler correction is the sum of its weighted local
logarithmic derivatives. -/
theorem logDeriv_eulerCorrection (χ : RayClassCharacter 𝔪) (𝔫 : Modulus K)
    {s : ℂ} (hs : 0 < s.re) :
    logDeriv (χ.eulerCorrection 𝔫) s = ∑ P ∈ 𝔫.support,
      χ.toMultiplicativeIdealWeight P.asIdeal * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s) *
        Complex.log (Ideal.absNorm P.asIdeal) /
          (1 - χ.toMultiplicativeIdealWeight P.asIdeal *
            (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) := by
  classical
  have heq : χ.eulerCorrection 𝔫 = fun z ↦ ∏ P ∈ 𝔫.support,
      (1 - χ.toMultiplicativeIdealWeight P.asIdeal *
        (Ideal.absNorm P.asIdeal : ℂ) ^ (-z)) := funext (eulerCorrection_eq_prod_support χ 𝔫)
  rw [heq, logDeriv_fun_prod]
  · exact Finset.sum_congr rfl fun P _ ↦ logDeriv_one_sub_mul_cpow_neg P.natCast_absNorm_ne_zero _ _
  · intro P _
    have h := one_sub_mul_ofReal_cpow_neg_ne_zero
      (q := (Ideal.absNorm P.asIdeal : ℝ))
      (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P)
      (by simpa using χ.toUnitaryIdealWeight.norm_le_one P.asIdeal) hs
    simpa using h
  · intro P _
    exact ((differentiable_const 1).sub ((differentiable_const _).mul
      (differentiable_neg.const_cpow (.inl P.natCast_absNorm_ne_zero)))).differentiableAt

/-- On real part at least one, the correction's logarithmic derivative is bounded by the
logarithmic norm of the presentation modulus, uniformly in the character. -/
theorem norm_logDeriv_eulerCorrection_le (χ : RayClassCharacter 𝔪) (𝔫 : Modulus K)
    {s : ℂ} (hs : 1 ≤ s.re) :
    ‖logDeriv (χ.eulerCorrection 𝔫) s‖ ≤ Real.log (Ideal.absNorm 𝔫.finitePart) := by
  classical
  rw [logDeriv_eulerCorrection χ 𝔫 (zero_lt_one.trans_le hs)]
  calc
    _ ≤ ∑ P ∈ 𝔫.support,
        ‖χ.toMultiplicativeIdealWeight P.asIdeal * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s) *
          Complex.log (Ideal.absNorm P.asIdeal) /
            (1 - χ.toMultiplicativeIdealWeight P.asIdeal *
              (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))‖ := norm_sum_le _ _
    _ ≤ ∑ P ∈ 𝔫.support, Real.log (Ideal.absNorm P.asIdeal) := by
      apply Finset.sum_le_sum
      intro P _
      rw [← logDeriv_one_sub_mul_cpow_neg P.natCast_absNorm_ne_zero]
      have h := norm_logDeriv_one_sub_mul_ofReal_cpow_neg_le
        (q := (Ideal.absNorm P.asIdeal : ℝ))
        (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P)
        (by simpa using χ.toUnitaryIdealWeight.norm_le_one P.asIdeal) hs
      simpa using h
    _ ≤ _ := sum_log_absNorm_le_log_absNorm 𝔫.finitePart_ne_bot 𝔫.support
      (fun P hP ↦ (Modulus.mem_support_iff 𝔫 P).mp hP)

end TauCeti.GlobalNumberFields.RayClassCharacter
