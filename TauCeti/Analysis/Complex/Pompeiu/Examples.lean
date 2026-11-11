/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Normalisation checks for the Cauchy transform

`TauCeti.cauchyTransform f w = π⁻¹ ∫ (w - z)⁻¹ • f z` is normalised to invert
`\bar∂ = (∂ₛ + i ∂ₜ) / 2`. The Cauchy–Pompeiu formula of `Pompeiu/Basic.lean` is instead written
with the constant `(2π)⁻¹` and the operator `D = ∂ₛ + i ∂ₜ = 2 \bar∂`. This file checks that the
two normalisations agree, and that the sign of the kernel matters.

* The doubled operator: `D u = 2 \bar∂ u` pointwise, for every `u`, and the Cauchy–Pompeiu integral
  `(2π)⁻¹ ∫ (w - z)⁻¹ • D u z` is literally `cauchyTransform (\bar∂ u) w`, with no hypothesis on
  `u`. On compactly supported `C¹` maps the transform of `D u = 2 \bar∂ u` is `2 u`.
* The transposed kernel: `π⁻¹ ∫ (z - w)⁻¹ • f z = -cauchyTransform f w`, so for compactly supported
  `C¹` data `\bar∂` of it is `-f`, and it is not a right inverse of `\bar∂`, as witnessed by a
  smooth bump function.

## Main results

* `TauCeti.fderiv_apply_one_add_I_smul_fderiv_apply_I`: `D u = 2 \bar∂ u`.
* `TauCeti.two_pi_inv_smul_integral_sub_inv_smul_fderiv_apply_one_add_I_smul_apply_I_eq`: the
  Cauchy–Pompeiu normalisation `(2π)⁻¹` with `D` is the normalisation `π⁻¹` with `\bar∂`.
* `HasCompactSupport.cauchyTransform_two_smul_conjWirtingerDeriv`: the transform of `2 \bar∂ u` is
  `2 u`.
* `TauCeti.pi_inv_smul_integral_swap_sub_inv_smul_eq_neg_cauchyTransform` and
  `HasCompactSupport.conjWirtingerDeriv_pi_inv_smul_integral_swap_sub_inv_smul`: the transposed
  kernel `(z - w)⁻¹` gives `\bar∂ T' = -id`.
* `TauCeti.exists_conjWirtingerDeriv_pi_inv_smul_integral_swap_sub_inv_smul_ne`: the transposed
  kernel is not a right inverse of `\bar∂`.
-/

public section

open MeasureTheory Complex
open scoped ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The operator `D = ∂ₛ + i ∂ₜ` of the Cauchy–Pompeiu formula is twice the conjugate Wirtinger
derivative. This holds for the totalized derivative, with no differentiability assumption. -/
theorem fderiv_apply_one_add_I_smul_fderiv_apply_I (u : ℂ → F) (z : ℂ) :
    fderiv ℝ u z 1 + I • fderiv ℝ u z I = (2 : ℂ) • conjWirtingerDeriv u z 1 := by
  rw [conjWirtingerDeriv_apply, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul, smul_eq_mul,
    mul_one]

/-- **The two normalisations agree.** The Cauchy–Pompeiu integral `(2π)⁻¹ ∫ (w - z)⁻¹ • D u z`,
with `D = 2 \bar∂`, is the normalised Cauchy transform `π⁻¹ ∫ (w - z)⁻¹ • \bar∂ u z` of `\bar∂ u`.
No hypothesis on `u` is needed: the identity holds for the integrals themselves. -/
theorem two_pi_inv_smul_integral_sub_inv_smul_fderiv_apply_one_add_I_smul_apply_I_eq
    (u : ℂ → F) (w : ℂ) :
    (2 * Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • (fderiv ℝ u z 1 + I • fderiv ℝ u z I) =
      cauchyTransform (fun z ↦ conjWirtingerDeriv u z 1) w := by
  simp_rw [fderiv_apply_one_add_I_smul_fderiv_apply_I, smul_comm _ (2 : ℂ)]
  rw [integral_smul, smul_smul, cauchyTransform_apply]
  congr 1
  field_simp

/-- On compactly supported `C¹` maps the Cauchy transform of `D u = 2 \bar∂ u` is `2 u`: the
transform inverts `\bar∂`, so it inverts `D` only up to the factor `2`, which the Cauchy–Pompeiu
formula absorbs in its constant `(2π)⁻¹`. -/
theorem _root_.HasCompactSupport.cauchyTransform_two_smul_conjWirtingerDeriv [CompleteSpace F]
    {u : ℂ → F} (hc : HasCompactSupport u) (hu : ContDiff ℝ 1 u) :
    cauchyTransform (fun z ↦ (2 : ℂ) • conjWirtingerDeriv u z 1) = (2 : ℂ) • u := by
  rw [show (fun z ↦ (2 : ℂ) • conjWirtingerDeriv u z 1) =
      (2 : ℂ) • fun z ↦ conjWirtingerDeriv u z 1 from rfl, cauchyTransform_smul]
  exact congrArg _ (funext (hc.cauchyTransform_conjWirtingerDeriv hu))

/-- The transposed kernel `(z - w)⁻¹` gives the negative of the Cauchy transform. -/
theorem pi_inv_smul_integral_swap_sub_inv_smul_eq_neg_cauchyTransform (f : ℂ → F) (w : ℂ) :
    (Real.pi : ℂ)⁻¹ • ∫ z, (z - w)⁻¹ • f z = -cauchyTransform f w := by
  simp_rw [← neg_sub w, inv_neg, neg_smul]
  rw [integral_neg, smul_neg, cauchyTransform_apply]

/-- **The plausible wrong kernel.** For compactly supported `C¹` data `f`, the transform with the
transposed kernel `(z - w)⁻¹` satisfies `\bar∂ T' f = -f`, not `f`. -/
theorem _root_.HasCompactSupport.conjWirtingerDeriv_pi_inv_smul_integral_swap_sub_inv_smul
    [CompleteSpace F] {f : ℂ → F} (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (w : ℂ) :
    conjWirtingerDeriv (fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (z - w)⁻¹ • f z) w 1 = -f w := by
  rw [show (fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (z - w)⁻¹ • f z) =
      (-1 : ℂ) • cauchyTransform f from funext fun w ↦ by
        rw [pi_inv_smul_integral_swap_sub_inv_smul_eq_neg_cauchyTransform, Pi.smul_apply,
          neg_one_smul],
    conjWirtingerDeriv_const_smul, smul_apply,
    hc.conjWirtingerDeriv_cauchyTransform hf, neg_one_smul]

/-- **The transposed kernel is not a right inverse of `\bar∂`.** There is a smooth compactly
supported `f : ℂ → ℂ`, a bump function equal to `1` at the origin, for which `\bar∂` of
`π⁻¹ ∫ (z - w)⁻¹ • f z` differs from `f` at the origin. -/
theorem exists_conjWirtingerDeriv_pi_inv_smul_integral_swap_sub_inv_smul_ne :
    ∃ f : ℂ → ℂ, HasCompactSupport f ∧ ContDiff ℝ ∞ f ∧
      conjWirtingerDeriv (fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (z - w)⁻¹ • f z) 0 1 ≠ f 0 := by
  let b : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hc : HasCompactSupport fun z ↦ (b z : ℂ) := b.hasCompactSupport.comp_left ofReal_zero
  have hs : ContDiff ℝ ∞ fun z ↦ (b z : ℂ) := ofRealCLM.contDiff.comp b.contDiff
  have h0 : (b 0 : ℂ) = 1 := by rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self
    zero_le_one), ofReal_one]
  refine ⟨fun z ↦ (b z : ℂ), hc, hs, ?_⟩
  rw [hc.conjWirtingerDeriv_pi_inv_smul_integral_swap_sub_inv_smul (hs.of_le (by norm_num))]
  simp only [h0]
  norm_num

end TauCeti
