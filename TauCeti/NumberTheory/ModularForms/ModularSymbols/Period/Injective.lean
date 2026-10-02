/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Period.Map
import TauCeti.NumberTheory.ModularForms.EichlerIntegral.Transformation
import Mathlib.NumberTheory.ModularForms.NormTrace
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Injectivity of the period map

For a finite-index subgroup `Γ ≤ SL(2, ℤ)`, the periods of a cusp form of weight `k = w + 2`
determine the form. This holds for the period map with coefficients in any commutative ring
`R` equipped with an algebra map to `ℂ`, in particular for the integral modular symbols.

If the period functional vanishes, all monomial periods vanish, including those of each
translate of the form. The transformation law of the Eichler integral then identifies its
weight-`-w` slash at every cusp with the Eichler integral of the translated cusp form. Thus it
vanishes at every cusp and is a modular form of nonpositive weight. Mathlib's negative-weight
vanishing and weight-zero constancy force it to vanish. Differentiating `w + 1` times recovers
the original cusp form.

Together with Hecke equivariance, injectivity allows relations among integral operators on
modular symbols to be transferred to operators on cusp forms.

## Main results

* `TauCeti.ModularSymbols.periodMap_injective`: the period map is injective for `k = w + 2`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §8.2.
* M. Eichler, *Eine Verallgemeinerung der Abelschen Integrale*, Math. Z. **67** (1957), 267–298.
* The AINTLIB `LeanModularForms` project, `ModularSymbols/EichlerInjective.lean`
  (`periodMap'_injective_eichler`), for the Eichler-integral route to injectivity. No code is
  transcribed; the proof uses the Eichler-integral and period APIs already in Tau Ceti.
-/

public noncomputable section

open Complex ConjAct Filter Function Matrix.SpecialLinearGroup MulOpposite MvPolynomial OnePoint
open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups ModularForm Pointwise

namespace TauCeti.ModularSymbols

variable {R : Type*} [CommRing R] [Algebra R ℂ]
variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {w : ℕ}

private lemma monomial_period_eq_zero (hk : k = w + 2)
    {f : CuspForm (Γ.map (mapGL ℝ)) k} (hf : periodMap R Γ hk f = 0)
    (σ : SL(2, ℤ)) {j : ℕ} (hj : j ≤ w) (α β : OnePoint ℚ) :
    cuspIntegral (fun z ↦ (⇑f ∣[k] σ) z * (z : ℂ) ^ j) β α = 0 := by
  let P : homogeneousSubmodule (Fin 2) R w := ⟨X 0 ^ j * X 1 ^ (w - j), by
    simpa [Nat.add_sub_cancel' hj] using
      (isHomogeneous_X_pow (R := R) (0 : Fin 2) j).mul (isHomogeneous_X_pow 1 (w - j))⟩
  have hP : periodIntegrand (⇑f ∣[k] σ) P =
      fun z ↦ (⇑f ∣[k] σ) z * (z : ℂ) ^ j := by
    funext z
    simp [P]
  have hdet : 0 < ((mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]
    exact one_pos
  have hper := congrArg
    (fun L ↦ L (symbol Γ (mapGL ℚ σ • α) (mapGL ℚ σ • β)
      (binaryFormRep R w (op (Matrix.adjugate (σ : Matrix (Fin 2) (Fin 2) ℤ))) P))) hf
  rw [periodMap_symbol] at hper
  rw [← hP, ModularForm.SL_slash, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
    ← ModularForm.rat_slash_mapGL,
    cuspIntegral_periodIntegrand_slash hk f P (mapGL_coe_matrix σ) hdet]
  exact hper

private lemma isZeroAtImInfty_eichlerIntegral_slash (hk : k = w + 2)
    {f : CuspForm (Γ.map (mapGL ℝ)) k} (hf : periodMap R Γ hk f = 0)
    {h : ℝ} (hh : 0 < h) (hΓ : h ∈ (Γ.map (mapGL ℝ)).strictPeriods)
    (σ : SL(2, ℤ)) :
    IsZeroAtImInfty (eichlerIntegral h (w + 1) f ∣[-(w : ℤ)] σ) := by
  let Γ' := toConjAct (mapGL ℝ σ)⁻¹ • Γ.map (mapGL ℝ)
  have : Γ'.IsArithmetic := by
    simpa [Γ', ← (Rat.castHom ℝ).algebraMap_toAlgebra, map_inv, map_mapGL]
      using Subgroup.IsArithmetic.conj (Γ.map (mapGL ℝ)) (mapGL ℚ σ)⁻¹
  let f' := _root_.CuspForm.translate f (mapGL ℝ σ)
  have hf' : ⇑f' = ⇑f ∣[k] σ := by
    rw [CuspForm.coe_translate, ModularForm.SL_slash,
      TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]
  -- Every period of the translate is a period of the original form against an integral
  -- change of variables of a binary form, and hence vanishes.
  have hper (j : ℕ) (hj : j ≤ w) (α β : OnePoint ℚ) :
      cuspIntegral (fun z ↦ f' z * (z : ℂ) ^ j) β α = 0 := by
    rw [hf']
    exact monomial_period_eq_zero hk hf σ hj α β
  have hE : eichlerIntegral h (w + 1) f ∣[-(w : ℤ)] σ =
      eichlerIntegral Γ'.strictWidthInfty (w + 1) f' := by
    funext τ
    rw [TauCeti.CuspFormClass.eichlerIntegral_slash_apply hk f hh hΓ f'
      Γ'.strictWidthInfty_pos Γ'.strictWidthInfty_mem_strictPeriods σ hf',
      cuspIntegral_mul_sub_pow f' hk,
      Finset.sum_eq_zero fun j hj ↦ by
        rw [hper j (Finset.mem_range_succ_iff.mp hj), mul_zero], mul_zero, sub_zero]
  rw [hE]
  exact isZeroAtImInfty_eichlerIntegral Γ'.strictWidthInfty_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f' Γ'.strictWidthInfty_mem_strictPeriods)
    (ModularFormClass.holo f') (ModularFormClass.bdd_at_infty f') w

private lemma eichlerIntegral_eq_zero (hk : k = w + 2)
    {f : CuspForm (Γ.map (mapGL ℝ)) k} (hf : periodMap R Γ hk f = 0)
    {h : ℝ} (hh : 0 < h) (hΓ : h ∈ (Γ.map (mapGL ℝ)).strictPeriods) :
    eichlerIntegral h (w + 1) f = 0 := by
  let E : ModularForm (Γ.map (mapGL ℝ)) (-(w : ℤ)) := {
    toFun := eichlerIntegral h (w + 1) f
    slash_action_eq' := by
      rintro γ ⟨σ, hσ, rfl⟩
      rw [← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash]
      apply TauCeti.CuspFormClass.eichlerIntegral_slash_eq_of_cuspIntegral_eq_zero
        hk f hh hΓ (Subgroup.mem_map_of_mem _ hσ)
      intro j hj
      simpa using monomial_period_eq_zero hk hf 1 hj
        (∞ : OnePoint ℚ) (mapGL ℚ σ⁻¹ • ∞)
    holo' := mdifferentiable_eichlerIntegral hh
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) _
    bdd_at_cusps' := by
      intro c hc
      have hc' := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc
      obtain ⟨σ, hσ⟩ := isCusp_SL2Z_iff'.mp hc'
      exact (isBoundedAt_iff_exists_SL2Z hc').mpr
        ⟨σ, hσ.symm, (isZeroAtImInfty_eichlerIntegral_slash hk hf hh hΓ σ).isBoundedAtImInfty⟩ }
  have hE : ⇑E = eichlerIntegral h (w + 1) f := (rfl)
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero E
    have hz := isZeroAtImInfty_eichlerIntegral hh
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) 0
    rw [← hE, hc] at hz
    have hc0 : c = 0 := tendsto_nhds_unique tendsto_const_nhds hz
    simpa only [hc0, Function.const_zero] using hE.symm.trans hc
  · rw [← hE, ModularForm.isZero_of_neg_weight (by omega) E]
    exact FunLike.coe_zero

/-- **Periods determine a cusp form.** For a finite-index subgroup of `SL(2, ℤ)` and weight
`k = w + 2 ≥ 2`, the period map into the dual of the modular symbols over `R` is injective.
In particular this applies to the integral modular symbols (`R = ℤ`). -/
theorem periodMap_injective (hk : k = w + 2) :
    Function.Injective (periodMap R Γ hk) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro f hf
  let h := (Γ.map (mapGL ℝ)).strictWidthInfty
  have hh : 0 < h := (Γ.map (mapGL ℝ)).strictWidthInfty_pos
  have hΓ : h ∈ (Γ.map (mapGL ℝ)).strictPeriods :=
    (Γ.map (mapGL ℝ)).strictWidthInfty_mem_strictPeriods
  have hderiv := TauCeti.CuspFormClass.iterate_normalizedDerivOfComplex_eichlerIntegral
    f hh hΓ w
  rw [eichlerIntegral_eq_zero hk hf hh hΓ] at hderiv
  have hzero : Derivative.normalizedDerivOfComplex (0 : ℍ → ℂ) = 0 :=
    Derivative.normalizedDerivOfComplex_const 0
  rw [Function.iterate_fixed hzero] at hderiv
  exact DFunLike.coe_injective hderiv.symm

end TauCeti.ModularSymbols
