/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EichlerIntegral.Integral
public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Period.Integral
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The transformation law of the Eichler integral

Let `f` be a cusp form of weight `k = n + 2` and `E_f = E_{n+1} f` its Eichler integral
(`TauCeti.eichlerIntegral`), which by `TauCeti.CuspFormClass.eichlerIntegral_eq_integral` is

`E_f(τ) = (-2πi)ⁿ⁺¹ / n! · ∫_τ^{i∞} f(z) (z - τ)ⁿ dz`.

This file proves that `E_f` transforms in weight `2 - k = -n` up to a **period polynomial**: for
`σ ∈ SL(2, ℤ)`,

`(E_f ∣[-n] σ)(τ) = E_{f ∣[k] σ}(τ) - (-2πi)ⁿ⁺¹ / n! · ∫_{σ⁻¹ • ∞}^{i∞} (f ∣[k] σ)(z) (z - τ)ⁿ dz`,

where the last integral is a period of `f ∣[k] σ` along the geodesic between two cusps, and so,
by `TauCeti.ModularSymbols.cuspIntegral_mul_sub_pow`, a polynomial in `τ` of degree at most `n`
whose coefficients are the periods `∫ (f ∣[k] σ)(z) zʲ dz`. The proof substitutes `z ↦ σ • z` in
the integral from `σ • τ` to `i∞`: since
`σ • z - σ • τ = (z - τ) / ((cz + d)(cτ + d))`, this turns `f(z) (z - σ • τ)ⁿ dz` into
`(cτ + d)⁻ⁿ (f ∣[k] σ)(z) (z - τ)ⁿ dz`, and moves the path to one from `τ` to the cusp `σ⁻¹ • ∞`,
which is compared with the vertical ray from `τ` by
`TauCeti.integral_Ioi_slash_eq_add_cuspIntegral`.

For `σ` in the level of `f` the form `f ∣[k] σ` is `f` itself, and the law reads
`E_f ∣[-n] σ - E_f = (period polynomial of f at σ)`. In particular, if the periods of `f` vanish
then `E_f` is invariant in weight `-n` under the level. This is the first step of the proof that
a cusp form of weight `k ≥ 2` with vanishing periods is zero (the injectivity of the
Eichler–Shimura period map): such an `E_f` is then a holomorphic form of nonpositive weight. For
`σ` outside the level, `f ∣[k] σ` is a cusp form for a conjugate subgroup, and the general law
compares `E_f ∣[-n] σ` with its Eichler integral, which is what controls `E_f` at the cusp
`σ • ∞`.

## Main results

* `TauCeti.CuspFormClass.eichlerIntegral_slash_apply`: the transformation law under
  `σ ∈ SL(2, ℤ)`, for a cusp form `f'` with `f' = f ∣[k] σ`.
* `TauCeti.CuspFormClass.eichlerIntegral_slash_apply_of_mem`: the transformation law for `σ` in
  the level of `f`.
* `TauCeti.CuspFormClass.eichlerIntegral_slash_eq_of_cuspIntegral_eq_zero`: if the periods
  `∫_{σ⁻¹ • ∞}^{i∞} f(z) zʲ dz`, `j ≤ n`, vanish, then `E_f ∣[-n] σ = E_f`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §8.2.
* M. Eichler, *Eine Verallgemeinerung der Abelschen Integrale*, Math. Z. **67** (1957), 267–298.
* The AINTLIB `LeanModularForms` project, `ModularSymbols/EichlerInjective.lean`
  (`eichler_slash_invariant`), where the transformation law is proved for the `q`-expansion
  Eichler integral.
-/

public noncomputable section

open Complex Filter Function MeasureTheory MvPolynomial Set
open Matrix.SpecialLinearGroup ModularGroup OnePoint TauCeti.ModularSymbols
open UpperHalfPlane hiding I
open scoped Real Nat Manifold MatrixGroups ModularForm

namespace TauCeti

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ] {k : ℤ} {n : ℕ} {h : ℝ}

/-- The binary form `(X₀ - τ X₁)ⁿ`, whose period integrand is `f(z) (z - τ)ⁿ`. -/
private def eichlerForm (n : ℕ) (τ : ℂ) : homogeneousSubmodule (Fin 2) ℂ n :=
  ⟨(X 0 - C τ * X 1) ^ n, by
    simpa using ((isHomogeneous_X ℂ (0 : Fin 2)).sub (isHomogeneous_C_mul_X τ 1)).pow n⟩

private lemma periodIntegrand_eichlerForm (f : ℍ → ℂ) (n : ℕ) (τ : ℂ) :
    periodIntegrand f (eichlerForm n τ) = fun z ↦ f z * ((z : ℂ) - τ) ^ n := by
  funext z
  simp [eichlerForm]

/-- Slashing the integrand `f(z) (z - σ • τ)ⁿ` in weight `2` by `σ ∈ SL(2, ℤ)` gives
`(cτ + d)⁻ⁿ (f ∣[n + 2] σ)(z) (z - τ)ⁿ`. -/
private lemma periodIntegrand_eichlerForm_slash (hk : k = n + 2) (f : ℍ → ℂ) (σ : SL(2, ℤ))
    (τ z : ℍ) :
    (periodIntegrand f (eichlerForm n (σ • τ : ℍ)) ∣[(2 : ℤ)] mapGL ℚ σ) z =
      denom σ τ ^ (-(n : ℤ)) * ((f ∣[k] σ) z * ((z : ℂ) - τ) ^ n) := by
  rw [periodIntegrand_slash_apply hk f _ (det_coe_mapGL_pos ℚ σ), ModularForm.rat_slash_mapGL,
    ← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash,
    Matrix.SpecialLinearGroup.map_mapGL, ← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]
  simp only [det_coe_mapGL, Rat.cast_one, one_zpow, one_mul, eichlerForm, map_pow, map_sub, aeval_X,
    map_mul, aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Algebra.algebraMap_self, RingHom.id_apply]
  have hσ : ((σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.det_coe]
  rw [sl_moeb, num_sub_smul_mul_denom (hσ ▸ one_pos), hσ, Complex.ofReal_one, one_mul, div_pow,
    zpow_neg, zpow_natCast, div_eq_inv_mul]
  ring

/-- Slashing the integrand `f(z) (z - σ • τ)ⁿ` in weight `2` by `σ ∈ SL(2, ℤ)`, when
`f' = f ∣[n + 2] σ`, gives `(cτ + d)⁻ⁿ f'(z) (z - τ)ⁿ`. -/
private lemma periodIntegrand_eichlerForm_slash_eq (hk : k = n + 2) {f f' : ℍ → ℂ}
    {σ : SL(2, ℤ)} (hf' : f' = f ∣[k] σ) (τ : ℍ) :
    periodIntegrand f (eichlerForm n (σ • τ : ℍ)) ∣[(2 : ℤ)] mapGL ℚ σ =
      denom σ τ ^ (-(n : ℤ)) • fun z : ℍ ↦ f' z * ((z : ℂ) - τ) ^ n := by
  funext z
  rw [periodIntegrand_eichlerForm_slash hk, hf', Pi.smul_apply, smul_eq_mul]

/-- The cusp integral of `f(z) (z - σ • τ)ⁿ` from `i∞` to `σ • i∞` is `(cτ + d)⁻ⁿ` times the cusp
integral of `f'(z) (z - τ)ⁿ` from `σ⁻¹ • i∞` to `i∞`, when `f' = f ∣[n + 2] σ`. -/
private lemma cuspIntegral_eichlerForm_smul (hk : k = n + 2) {f f' : ℍ → ℂ} {σ : SL(2, ℤ)}
    (hf' : f' = f ∣[k] σ) (τ : ℍ) :
    cuspIntegral (fun z : ℍ ↦ f z * ((z : ℂ) - (σ • τ : ℍ)) ^ n) ∞ (mapGL ℚ σ • ∞) =
      denom σ τ ^ (-(n : ℤ)) *
        cuspIntegral (fun z ↦ f' z * ((z : ℂ) - τ) ^ n) (mapGL ℚ σ⁻¹ • ∞) ∞ := by
  rw [← cuspIntegral_smul, ← periodIntegrand_eichlerForm_slash_eq hk hf',
    cuspIntegral_slash _ (det_coe_mapGL_pos ℚ σ), smul_smul, ← map_mul, mul_inv_cancel, map_one,
    one_smul, periodIntegrand_eichlerForm]

/-- **The transformation law of the Eichler integral.** Let `f` be a cusp form of weight
`k = n + 2` on an arithmetic subgroup, `σ ∈ SL(2, ℤ)`, and `f'` a cusp form (for any subgroup
with a positive strict period `h'`) with `f' = f ∣[k] σ`. Then the Eichler integrals
`E_f = E_{n+1} f` and `E_{f'}` satisfy

`(E_f ∣[-n] σ)(τ) = E_{f'}(τ) - (-2πi)ⁿ⁺¹ / n! · ∫_{σ⁻¹ • ∞}^{i∞} f'(z) (z - τ)ⁿ dz`,

the integral taken along the geodesic between the two cusps. By
`TauCeti.ModularSymbols.cuspIntegral_mul_sub_pow` the correction term is a polynomial in `τ` of
degree at most `n` whose coefficients are periods of `f'`. -/
theorem CuspFormClass.eichlerIntegral_slash_apply [Γ.IsArithmetic] [CuspFormClass F Γ k]
    (hk : k = n + 2) (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    {Γ' : Subgroup (GL (Fin 2) ℝ)} {F' : Type*} [FunLike F' ℍ ℂ] [CuspFormClass F' Γ' k]
    (f' : F') {h' : ℝ} (hh' : 0 < h') (hΓ' : h' ∈ Γ'.strictPeriods) (σ : SL(2, ℤ))
    (hf' : ⇑f' = ⇑f ∣[k] σ) (τ : ℍ) :
    (eichlerIntegral h (n + 1) f ∣[-(n : ℤ)] σ) τ =
      eichlerIntegral h' (n + 1) f' τ - (-2 * π * I) ^ (n + 1) / n ! *
        cuspIntegral (fun z ↦ f' z * ((z : ℂ) - τ) ^ n) (mapGL ℚ σ⁻¹ • ∞) ∞ := by
  set c : ℂ := (-2 * π * I) ^ (n + 1) / (n ! : ℂ)
  set j : ℂ := denom σ τ
  have hsmul : (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (mapGL ℚ σ) • τ : ℍ) =
      σ • τ := by
    rw [Matrix.SpecialLinearGroup.map_mapGL, ← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
      ← sl_moeb]
  -- the substitution `z ↦ σ • z`, by `TauCeti.integral_Ioi_slash_eq_add_cuspIntegral`
  have key := integral_Ioi_slash_eq_add_cuspIntegral
    (mdifferentiable_periodIntegrand (ModularFormClass.holo f) (eichlerForm n (σ • τ : ℍ)))
    (fun _ hg ↦ integrableOn_resToImagAxis_periodIntegrand_slash_Ici f hk _ hg)
    (fun _ hg ↦ tendsto_periodIntegrand_slash f hk _ hg) (det_coe_mapGL_pos ℚ σ) τ ?_ ?_
  · have hB := integral_ray_smul_eichlerIntegrand f n (σ • τ) 1
    simp only [one_smul, one_mul] at hB
    rw [periodIntegrand_eichlerForm_slash_eq hk hf', hsmul, periodIntegrand_eichlerForm,
      integral_ray_smul_eichlerIntegrand, hB, cuspIntegral_eichlerForm_smul hk hf', zpow_neg,
      zpow_natCast] at key
    rw [ModularForm.SL_slash_apply, neg_neg, zpow_natCast,
      CuspFormClass.eichlerIntegral_eq_integral f hh hΓ,
      CuspFormClass.eichlerIntegral_eq_integral f' hh' hΓ']
    have hj : j ^ n * (j ^ n)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero n (denom_ne_zero σ τ))
    have key' := congrArg (j ^ n * ·) key
    rw [mul_add, ← mul_assoc, hj, one_mul, ← mul_assoc, hj, one_mul] at key'
    linear_combination (-c) * key'
  · rw [periodIntegrand_eichlerForm_slash_eq hk hf']
    exact CuspFormClass.integrableOn_ray_smul_eichlerIntegrand f' hh' hΓ' n τ _
  · rw [hsmul, periodIntegrand_eichlerForm]
    simpa using CuspFormClass.integrableOn_ray_smul_eichlerIntegrand f hh hΓ n (σ • τ) 1

/-- **The transformation law of the Eichler integral in the level.** For a cusp form `f` of
weight `k = n + 2` on an arithmetic subgroup `Γ` and `σ ∈ SL(2, ℤ)` with `σ ∈ Γ`, the Eichler
integral `E_f = E_{n+1} f` transforms in weight `-n` up to the period polynomial of `f` at `σ`:

`(E_f ∣[-n] σ)(τ) = E_f(τ) - (-2πi)ⁿ⁺¹ / n! · ∫_{σ⁻¹ • ∞}^{i∞} f(z) (z - τ)ⁿ dz`. -/
theorem CuspFormClass.eichlerIntegral_slash_apply_of_mem [Γ.IsArithmetic] [CuspFormClass F Γ k]
    (hk : k = n + 2) (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {σ : SL(2, ℤ)}
    (hσ : mapGL ℝ σ ∈ Γ) (τ : ℍ) :
    (eichlerIntegral h (n + 1) f ∣[-(n : ℤ)] σ) τ =
      eichlerIntegral h (n + 1) f τ - (-2 * π * I) ^ (n + 1) / n ! *
        cuspIntegral (fun z ↦ f z * ((z : ℂ) - τ) ^ n) (mapGL ℚ σ⁻¹ • ∞) ∞ :=
  eichlerIntegral_slash_apply hk f hh hΓ f hh hΓ σ (by
    rw [ModularForm.SL_slash, Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
      SlashInvariantFormClass.slash_action_eq f _ hσ]) τ

/-- **Vanishing periods make the Eichler integral invariant.** For a cusp form `f` of weight
`k = n + 2` on an arithmetic subgroup `Γ` and `σ ∈ SL(2, ℤ)` with `σ ∈ Γ`, if the periods
`∫_{σ⁻¹ • ∞}^{i∞} f(z) zʲ dz` vanish for `j ≤ n`, then the Eichler integral `E_f = E_{n+1} f` is
invariant under `σ` in weight `-n`: `E_f ∣[-n] σ = E_f`. -/
theorem CuspFormClass.eichlerIntegral_slash_eq_of_cuspIntegral_eq_zero [Γ.IsArithmetic]
    [CuspFormClass F Γ k] (hk : k = n + 2) (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    {σ : SL(2, ℤ)} (hσ : mapGL ℝ σ ∈ Γ)
    (hper : ∀ j ≤ n, cuspIntegral (fun z ↦ f z * (z : ℂ) ^ j) (mapGL ℚ σ⁻¹ • ∞) ∞ = 0) :
    eichlerIntegral h (n + 1) f ∣[-(n : ℤ)] σ = eichlerIntegral h (n + 1) f := by
  funext τ
  rw [eichlerIntegral_slash_apply_of_mem hk f hh hΓ hσ, cuspIntegral_mul_sub_pow f hk,
    Finset.sum_eq_zero fun j hj ↦ by rw [hper j (Finset.mem_range_succ_iff.mp hj), mul_zero],
    mul_zero, sub_zero]

end TauCeti
