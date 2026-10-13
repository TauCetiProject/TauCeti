/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.AbsolutelyContinuous
import TauCeti.Analysis.Contour.Winding.Proximity
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Proximity invariance for absolutely continuous curves

Two closed absolutely continuous curves have equal winding numbers about a point when their
pointwise separation is smaller than the first curve's distance to that point. Their comparison
quotient lies in the right half-plane, where the principal logarithm is smooth. The fundamental
theorem for its absolutely continuous logarithm evaluates the difference of their index integrals.
-/

public section

open Complex MeasureTheory Set

namespace TauCeti.Contour

/-- Proximity invariance for closed absolutely continuous curves: a pointwise leash shorter than
the base curve's distance to `z` preserves its winding number about `z`. -/
theorem windingNumber_eq_of_dist_lt_dist_of_absolutelyContinuousOnInterval
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (h₀ : AbsolutelyContinuousOnInterval γ₀ a b)
    (h₁ : AbsolutelyContinuousOnInterval γ₁ a b)
    (h₀closed : γ₀ a = γ₀ b) (h₁closed : γ₁ a = γ₁ b)
    (hlt : ∀ t ∈ uIcc a b, dist (γ₁ t) (γ₀ t) < dist (γ₀ t) z) :
    windingNumber γ₁ a b z = windingNumber γ₀ a b z := by
  have h₀ne : ∀ t ∈ uIcc a b, γ₀ t - z ≠ 0 := by
    intro t ht
    exact sub_ne_zero.mpr (ne_of_dist_lt_dist (hlt t ht))
  have h₁ne : ∀ t ∈ uIcc a b, γ₁ t - z ≠ 0 := by
    intro t ht
    exact sub_ne_zero.mpr (ne_of_dist_lt_dist' (hlt t ht))
  have h₀off : z ∉ γ₀ '' uIcc a b := by
    rintro ⟨t, ht, heq⟩
    exact h₀ne t ht (sub_eq_zero.mpr heq)
  have h₁off : z ∉ γ₁ '' uIcc a b := by
    rintro ⟨t, ht, heq⟩
    exact h₁ne t ht (sub_eq_zero.mpr heq)
  let σ : ℝ → ℂ := compRatio γ₀ γ₁ z
  have hσeq : σ = fun t ↦ (γ₁ t - z) / (γ₀ t - z) := funext (compRatio_apply γ₀ γ₁ z)
  have hσslit : ∀ t ∈ uIcc a b, σ t ∈ slitPlane := by
    intro t ht
    exact compRatio_mem_slitPlane (hlt t ht)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ z) a b :=
    (LipschitzWith.const z).lipschitzOnWith.absolutelyContinuousOnInterval
  have hα₀ := h₀.fun_sub hconst
  have hα₁ := h₁.fun_sub hconst
  have hinv : AbsolutelyContinuousOnInterval (fun t ↦ (γ₀ t - z)⁻¹) a b := by
    apply hα₀.comp_of_contDiffAt
    rintro _ ⟨t, ht, rfl⟩
    exact contDiffAt_inv ℝ (h₀ne t ht)
  have hσ : AbsolutelyContinuousOnInterval σ a b := by
    simpa only [hσeq, div_eq_mul_inv, smul_eq_mul] using hα₁.fun_smul hinv
  have hlog : AbsolutelyContinuousOnInterval (Complex.log ∘ σ) a b := by
    apply hσ.comp_of_contDiffAt
    rintro _ ⟨t, ht, rfl⟩
    exact (Complex.contDiffAt_log (hσslit t ht)).restrict_scalars ℝ
  have hlogderiv : ∀ᵐ t, t ∈ uIoc a b →
      HasDerivAt (Complex.log ∘ σ)
        ((γ₁ t - z)⁻¹ * deriv γ₁ t - (γ₀ t - z)⁻¹ * deriv γ₀ t) t := by
    filter_upwards [h₀.boundedVariationOn.ae_differentiableAt_of_mem_uIcc,
      h₁.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht₀ ht₁ ht
    have ht' := uIoc_subset_uIcc ht
    have hd : HasDerivAt σ
        ((deriv γ₁ t * (γ₀ t - z) - (γ₁ t - z) * deriv γ₀ t) / (γ₀ t - z) ^ 2) t := by
      rw [hσeq]
      exact ((ht₁ ht').hasDerivAt.sub_const z).div
        ((ht₀ ht').hasDerivAt.sub_const z) (h₀ne t ht')
    convert hd.clog_real (hσslit t ht') using 1
    · rfl
    rw [hσeq]
    dsimp only
    field_simp [h₀ne t ht', h₁ne t ht']
  have hσclosed : σ a = σ b := by simp only [hσeq, h₀closed, h₁closed]
  have hint := hlog.integral_eq_sub_of_ae_hasDerivAt hlogderiv
  simp only [Function.comp_apply, hσclosed, sub_self] at hint
  have hint₀ := intervalIntegrable_inv_sub_mul_deriv_of_absolutelyContinuousOnInterval h₀ h₀off
  have hint₁ := intervalIntegrable_inv_sub_mul_deriv_of_absolutelyContinuousOnInterval h₁ h₁off
  rw [intervalIntegral.integral_sub hint₁ hint₀] at hint
  rw [windingNumber_eq_integral_of_absolutelyContinuousOnInterval h₁ h₁off,
    windingNumber_eq_integral_of_absolutelyContinuousOnInterval h₀ h₀off]
  exact congrArg ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ·) (sub_eq_zero.mp hint)

end TauCeti.Contour
