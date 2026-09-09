/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# A segment estimate for Poincaré--Wirtinger

This file supplies a bounded Lane A.5 prerequisite: the change along a straight segment is
controlled by the integral of the norm of the derivative.  For a `C¹` function `u` between normed
real vector spaces, it proves

`‖u x - u y‖ ≤ ∫ t in (0)..‖x - y‖, ‖fderiv ℝ u (x + t • (‖x - y‖⁻¹ • (y - x)))‖`.

The statement is the segment lemma used by Scott Armstrong and Julia Kempe in the Apache-2.0
`scottnarmstrong/DeGiorgi` development, `DeGiorgi/Poincare.lean` at commit
`4c1b3077d3782b24065184df4ba59501b2e56fc7`.  This file packages the same estimate through
Mathlib's `norm_sub_le_integral_of_norm_deriv_le_of_le`; it is a small, self-contained prerequisite
for the later bounded-domain Poincaré--Wirtinger argument, and imports no whole-space or Sobolev
foundation.  The adapted source is
`https://github.com/scottnarmstrong/DeGiorgi/blob/4c1b3077d3782b24065184df4ba59501b2e56fc7/DeGiorgi/Poincare.lean#L382-L431`;
the original repository is Apache-2.0 licensed.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory

/-- The oscillation of a smooth function along a segment is bounded by the integrated norm of its
Fréchet derivative along that segment.  The zero-length segment is included. -/
theorem norm_sub_le_integral_fderiv_along_segment
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} (hu : ContDiff ℝ 1 u) (x y : E) :
    ‖u x - u y‖ ≤ ∫ t in (0 : ℝ)..‖x - y‖,
      ‖fderiv ℝ u (x + t • (‖x - y‖⁻¹ • (y - x)))‖ := by
  by_cases hxy : x = y
  · simp [hxy]
  set ω : E := ‖x - y‖⁻¹ • (y - x)
  set γ : ℝ → E := fun t => x + t • ω
  have hγ : ∀ t, HasDerivAt γ ω t := by
    intro t
    have hline : HasDerivAt (fun t => t • ω) ω t := by
      simpa using (hasDerivAt_id' (𝕜 := ℝ) t).smul_const ω
    exact hline.const_add x
  have hγ0 : γ 0 = x := by simp [γ]
  have hγ1 : γ ‖x - y‖ = y := by
    simp only [γ, ω, smul_smul]
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)), one_smul]
    abel
  have hfderiv_cont : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hγ_cont : Continuous γ := by fun_prop
  have hγ_differentiable : Differentiable ℝ γ := fun t => (hγ t).differentiableAt
  have hB_cont : Continuous (fun t => ‖fderiv ℝ u (γ t)‖) :=
    continuous_norm.comp (hfderiv_cont.comp hγ_cont)
  have hω_norm : ‖ω‖ = 1 := by
    -- Unfolding `ω` exposes the scalar multiple whose norm can be normalized.
    change ‖‖x - y‖⁻¹ • (y - x)‖ = 1
    rw [norm_smul, norm_inv, norm_norm, norm_sub_rev y x,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))]
  have hmain :
      ‖(u ∘ γ) ‖x - y‖ - (u ∘ γ) 0‖ ≤
        ∫ t in (0 : ℝ)..‖x - y‖, ‖fderiv ℝ u (γ t)‖ := by
    apply norm_sub_le_integral_of_norm_deriv_le_of_le (f := u ∘ γ)
      (B := fun t => ‖fderiv ℝ u (γ t)‖) (a := 0) (b := ‖x - y‖)
    · exact norm_nonneg _
    · exact (hu.continuous.comp hγ_cont).continuousOn
    · exact (hu.differentiable (by norm_num)).comp hγ_differentiable |>.differentiableOn
    · filter_upwards with t ht
      have hderiv : deriv (u ∘ γ) t = (fderiv ℝ u (γ t)) ω :=
        ((hu.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
          (hγ t)).deriv
      rw [hderiv]
      calc
        ‖(fderiv ℝ u (γ t)) ω‖ ≤ ‖fderiv ℝ u (γ t)‖ * ‖ω‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ u (γ t)‖ := by rw [hω_norm, mul_one]
    · exact hB_cont.intervalIntegrable _ _
  rw [norm_sub_rev]
  simpa only [Function.comp_apply, hγ0, hγ1, γ, ω] using hmain

end TauCeti
