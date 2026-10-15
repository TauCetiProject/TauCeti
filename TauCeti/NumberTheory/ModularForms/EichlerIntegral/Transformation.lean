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

/-- The image of `σ ∈ SL(2, ℤ)` in `GL(2, ℚ)` has determinant `1`. -/
private lemma det_mapGL_rat (σ : SL(2, ℤ)) :
    ((mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]

/-- Slashing the integrand `f(z) (z - σ • τ)ⁿ` in weight `2` by `σ ∈ SL(2, ℤ)` gives
`(cτ + d)⁻ⁿ (f ∣[n + 2] σ)(z) (z - τ)ⁿ`. -/
private lemma periodIntegrand_eichlerForm_slash (hk : k = n + 2) (f : ℍ → ℂ) (σ : SL(2, ℤ))
    (τ z : ℍ) :
    (periodIntegrand f (eichlerForm n (σ • τ : ℍ)) ∣[(2 : ℤ)] mapGL ℚ σ) z =
      denom σ τ ^ (-(n : ℤ)) * ((f ∣[k] σ) z * ((z : ℂ) - τ) ^ n) := by
  have hdet : 0 < ((mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [det_mapGL_rat]
    exact one_pos
  rw [periodIntegrand_slash_apply hk f _ hdet, ModularForm.rat_slash_mapGL,
    ← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash,
    Matrix.SpecialLinearGroup.map_mapGL, ← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]
  simp only [det_mapGL_rat, Rat.cast_one, one_zpow, one_mul, eichlerForm, map_pow, map_sub, aeval_X,
    map_mul, aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Algebra.algebraMap_self, RingHom.id_apply]
  have hσ : ((σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.det_coe]
  rw [sl_moeb, num_sub_smul_mul_denom (hσ ▸ one_pos), hσ, Complex.ofReal_one, one_mul, div_pow,
    zpow_neg, zpow_natCast, div_eq_inv_mul]
  ring

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
  have hdet : 0 < ((mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [det_mapGL_rat]
    exact one_pos
  have hslash : periodIntegrand f (eichlerForm n (σ • τ : ℍ)) ∣[(2 : ℤ)] mapGL ℚ σ =
      j ^ (-(n : ℤ)) • fun z : ℍ ↦ f' z * ((z : ℂ) - τ) ^ n := by
    funext z
    rw [periodIntegrand_eichlerForm_slash hk, hf', Pi.smul_apply, smul_eq_mul]
  have hsmul : (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (mapGL ℚ σ) • τ : ℍ) =
      σ • τ := by
    rw [Matrix.SpecialLinearGroup.map_mapGL, ← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
      ← sl_moeb]
  -- along the vertical ray from `τ₀`, `z - τ₀ = t i`
  have hcoe (τ₀ : ℍ) {t : ℝ} (ht : t ∈ Ioi 0) :
      ((ofComplex ((τ₀ : ℂ) + t * I) : ℍ) : ℂ) - τ₀ = t * I := by
    rw [ofComplex_apply_of_im_pos (by simpa using add_pos τ₀.im_pos (show (0 : ℝ) < t from ht)),
      coe_mk, add_sub_cancel_left]
  have hA : ∫ t in Ioi (0 : ℝ),
      (j ^ (-(n : ℤ)) • fun z : ℍ ↦ f' z * ((z : ℂ) - τ) ^ n) (ofComplex (τ + t * I)) * I =
        j ^ (-(n : ℤ)) * ∫ t in Ioi (0 : ℝ), f' (ofComplex (τ + t * I)) * (t * I) ^ n * I := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul, hcoe τ ht]
    ring
  have hB : ∫ t in Ioi (0 : ℝ), (fun z : ℍ ↦ f z * ((z : ℂ) - (σ • τ : ℍ)) ^ n)
      (ofComplex ((σ • τ : ℍ) + t * I)) * I =
        ∫ t in Ioi (0 : ℝ), f (ofComplex ((σ • τ : ℍ) + t * I)) * (t * I) ^ n * I :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ by simp only [hcoe (σ • τ) ht]
  have hC : cuspIntegral (fun z : ℍ ↦ f z * ((z : ℂ) - (σ • τ : ℍ)) ^ n) ∞ (mapGL ℚ σ • ∞) =
      j ^ (-(n : ℤ)) * cuspIntegral (fun z ↦ f' z * ((z : ℂ) - τ) ^ n) (mapGL ℚ σ⁻¹ • ∞) ∞ := by
    rw [← cuspIntegral_smul, ← hslash, cuspIntegral_slash _ hdet, smul_smul, ← map_mul,
      mul_inv_cancel, map_one, one_smul, periodIntegrand_eichlerForm]
  -- the substitution `z ↦ σ • z`, by `TauCeti.integral_Ioi_slash_eq_add_cuspIntegral`
  have key := integral_Ioi_slash_eq_add_cuspIntegral
    (mdifferentiable_periodIntegrand (ModularFormClass.holo f) (eichlerForm n (σ • τ : ℍ)))
    (fun _ hg ↦ integrableOn_resToImagAxis_periodIntegrand_slash_Ici f hk _ hg)
    (fun _ hg ↦ tendsto_periodIntegrand_slash f hk _ hg) hdet τ ?_ ?_
  · rw [hslash, hsmul, periodIntegrand_eichlerForm, hA, hB, hC, zpow_neg, zpow_natCast] at key
    rw [ModularForm.SL_slash_apply, neg_neg, zpow_natCast,
      CuspFormClass.eichlerIntegral_eq_integral f hh hΓ,
      CuspFormClass.eichlerIntegral_eq_integral f' hh' hΓ']
    have hj : j ^ n * (j ^ n)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero n (denom_ne_zero σ τ))
    have key' := congrArg (j ^ n * ·) key
    rw [mul_add, ← mul_assoc, hj, one_mul, ← mul_assoc, hj, one_mul] at key'
    linear_combination (-c) * key'
  -- the two vertical integrands are integrable, by `CuspFormClass.integrableOn_eichlerIntegrand`
  · rw [hslash]
    refine IntegrableOn.congr_fun ((CuspFormClass.integrableOn_eichlerIntegrand f' hh' hΓ' n
      τ).const_mul (j ^ (-(n : ℤ)) * I⁻¹)) (fun t ht ↦ ?_) measurableSet_Ioi
    simp only [Pi.smul_apply, smul_eq_mul, hcoe τ ht]
    field_simp
  · rw [hsmul, periodIntegrand_eichlerForm]
    refine IntegrableOn.congr_fun ((CuspFormClass.integrableOn_eichlerIntegrand f hh hΓ n
      (σ • τ)).const_mul I⁻¹) (fun t ht ↦ ?_) measurableSet_Ioi
    simp only [hcoe (σ • τ) ht]
    field_simp

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
