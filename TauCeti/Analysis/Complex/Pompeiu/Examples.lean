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
with the constant `(2π)⁻¹` and the operator `D = ∂ₛ + i ∂ₜ = 2 \bar∂`. The identities comparing
the two normalisations, `TauCeti.fderiv_apply_one_add_I_smul_fderiv_apply_I` and
`TauCeti.two_pi_inv_smul_integral_sub_inv_smul_fderiv_apply_one_add_I_smul_apply_I_eq`, and those
for the transposed kernel `(z - w)⁻¹`, live beside the underlying APIs. This file checks the
consequences.

* The doubled operator: on compactly supported `C¹` maps the transform of `D u = 2 \bar∂ u` is
  `2 u`, so the transform inverts `D` only up to the factor `2` absorbed by `(2π)⁻¹`.
* The transposed kernel is not a right inverse of `\bar∂`, as witnessed by a smooth bump function.

## Main results

* `TauCeti.exists_conjWirtingerDeriv_pi_inv_smul_integral_swap_sub_inv_smul_ne`: the transposed
  kernel is not a right inverse of `\bar∂`.
-/

public section

open MeasureTheory Complex
open scoped ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- On compactly supported `C¹` maps the Cauchy transform of `D u = 2 \bar∂ u` is `2 u`: the
transform inverts `\bar∂`, so it inverts `D` only up to the factor `2`, which the Cauchy–Pompeiu
formula absorbs in its constant `(2π)⁻¹`. -/
example [CompleteSpace F] {u : ℂ → F} (hc : HasCompactSupport u) (hu : ContDiff ℝ 1 u) :
    cauchyTransform ((2 : ℂ) • fun z ↦ conjWirtingerDeriv u z 1) = (2 : ℂ) • u := by
  rw [cauchyTransform_smul, funext (hc.cauchyTransform_conjWirtingerDeriv hu)]

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
