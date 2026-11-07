/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp

/-!
# Absolute continuity of the logarithm of a shifted quotient

For two absolutely continuous complex curves `γ₀, γ₁` and a point `z` such that the quotient
`(γ₁ t - z) / (γ₀ t - z)` stays in the slit plane, the principal logarithm of that quotient is
absolutely continuous, and almost everywhere its derivative is the difference of the two
logarithmic derivatives. The slit-plane hypothesis already forces both `γ₀ t - z` and
`γ₁ t - z` to be nonzero, since `0` is not in the slit plane.

## Main results

* `AbsolutelyContinuousOnInterval.log_div_sub`: the logarithm of the shifted quotient is
  absolutely continuous.
* `AbsolutelyContinuousOnInterval.ae_hasDerivAt_log_div_sub`: its almost-everywhere derivative.
-/

public section

open Complex MeasureTheory Set

/-- The principal logarithm of the quotient of two absolutely continuous curves, shifted by `z`,
is absolutely continuous when the quotient stays in the slit plane (which forces the denominator
to avoid zero). -/
theorem AbsolutelyContinuousOnInterval.log_div_sub
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (h₀ : AbsolutelyContinuousOnInterval γ₀ a b)
    (h₁ : AbsolutelyContinuousOnInterval γ₁ a b)
    (hslit : ∀ t ∈ uIcc a b, (γ₁ t - z) / (γ₀ t - z) ∈ slitPlane) :
    AbsolutelyContinuousOnInterval (Complex.log ∘ fun t ↦ (γ₁ t - z) / (γ₀ t - z)) a b := by
  have h₀ne : ∀ t ∈ uIcc a b, γ₀ t - z ≠ 0 := fun t ht h ↦ by
    simpa [h] using hslit t ht
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ z) a b :=
    (LipschitzWith.const z).lipschitzOnWith.absolutelyContinuousOnInterval
  have hα₀ := h₀.fun_sub hconst
  have hα₁ := h₁.fun_sub hconst
  have hinv : AbsolutelyContinuousOnInterval (fun t ↦ (γ₀ t - z)⁻¹) a b := by
    apply hα₀.comp_of_contDiffAt
    rintro _ ⟨t, ht, rfl⟩
    exact contDiffAt_inv ℝ (h₀ne t ht)
  have hσ : AbsolutelyContinuousOnInterval (fun t ↦ (γ₁ t - z) / (γ₀ t - z)) a b := by
    simpa only [div_eq_mul_inv, smul_eq_mul] using hα₁.fun_smul hinv
  apply hσ.comp_of_contDiffAt
  rintro _ ⟨t, ht, rfl⟩
  exact (Complex.contDiffAt_log (hslit t ht)).restrict_scalars ℝ

/-- Almost everywhere, the logarithm of the shifted quotient of two absolutely continuous curves
has the difference of the two logarithmic derivatives as derivative. -/
theorem AbsolutelyContinuousOnInterval.ae_hasDerivAt_log_div_sub
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (h₀ : AbsolutelyContinuousOnInterval γ₀ a b)
    (h₁ : AbsolutelyContinuousOnInterval γ₁ a b)
    (hslit : ∀ t ∈ uIcc a b, (γ₁ t - z) / (γ₀ t - z) ∈ slitPlane) :
    ∀ᵐ t, t ∈ uIoc a b →
      HasDerivAt (Complex.log ∘ fun t ↦ (γ₁ t - z) / (γ₀ t - z))
        ((γ₁ t - z)⁻¹ * deriv γ₁ t - (γ₀ t - z)⁻¹ * deriv γ₀ t) t := by
  have h₀ne : ∀ t ∈ uIcc a b, γ₀ t - z ≠ 0 := fun t ht h ↦ by
    simpa [h] using hslit t ht
  have h₁ne : ∀ t ∈ uIcc a b, γ₁ t - z ≠ 0 := fun t ht h ↦ by
    simpa [h] using hslit t ht
  filter_upwards [h₀.boundedVariationOn.ae_differentiableAt_of_mem_uIcc,
    h₁.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht₀ ht₁ ht
  have ht' := uIoc_subset_uIcc ht
  have hd : HasDerivAt (fun t ↦ (γ₁ t - z) / (γ₀ t - z))
      ((deriv γ₁ t * (γ₀ t - z) - (γ₁ t - z) * deriv γ₀ t) / (γ₀ t - z) ^ 2) t :=
    ((ht₁ ht').hasDerivAt.sub_const z).div
      ((ht₀ ht').hasDerivAt.sub_const z) (h₀ne t ht')
  convert hd.clog_real (hslit t ht') using 1
  · rfl
  field_simp [h₀ne t ht', h₁ne t ht']
