/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# The increment of a function along a segment

This file bounds the increment of a function between `x` and `x + h` by the integral of its
directional derivative along the segment joining them. It is the multi-dimensional form of
Mathlib's one-dimensional `enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc`, obtained by
composing with the affine parametrization `t ↦ x + t • h` of the segment.

The hypotheses of the first estimate are local to the segment: differentiability at each of its
points and continuity of the directional derivative along it. The real-valued estimate uses the
same local hypotheses on the normalized segment.

## Main declarations

* `TauCeti.enorm_sub_le_lintegral_enorm_fderiv_apply`: the segment increment estimate.
* `TauCeti.norm_sub_le_integral_fderiv_along_segment`: the corresponding normalized real-integral
  estimate.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, where this is the starting point of the
difference-quotient characterization of Sobolev functions.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F}

/-- **The segment increment estimate**: the norm of `u (x + h) - u x` is at most the integral
along the segment from `x` to `x + h` of the norm of the directional derivative
`Du(x + t • h) h`. -/
theorem enorm_sub_le_lintegral_enorm_fderiv_apply (x h : E)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ u (x + t • h))
    (hc : ContinuousOn (fun t : ℝ => fderiv ℝ u (x + t • h) h) (Icc 0 1)) :
    ‖u (x + h) - u x‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ := by
  have hline : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fun s : ℝ => u (x + s • h)) t := by
    intro t ht
    simpa [Function.comp_def] using (hd t ht).comp t
      (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => x + s • h) t)
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      derivWithin (fun s : ℝ => u (x + s • h)) (Icc 0 1) t =
        fderiv ℝ u (x + t • h) h := by
    intro t ht
    rw [(hline t ht).derivWithin ((uniqueDiffOn_Icc zero_lt_one).uniqueDiffWithinAt ht),
      (hd t ht).deriv_comp_add_smul]
  have hC1 : ContDiffOn ℝ 1 (fun s : ℝ => u (x + s • h)) (Icc 0 1) := by
    rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc zero_lt_one)]
    exact ⟨fun t ht => (hline t ht).differentiableWithinAt,
      hc.congr hderiv⟩
  have h01 := enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hC1 zero_le_one
  calc
    ‖u (x + h) - u x‖ₑ ≤
        ∫⁻ t in Icc (0 : ℝ) 1,
          ‖derivWithin (fun s : ℝ => u (x + s • h)) (Icc 0 1) t‖ₑ := by
      simpa using h01
    _ = ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ :=
      setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [hderiv t ht]

/-- The oscillation of a function along a segment is bounded by the integrated norm of its
Fréchet derivative along that segment. The hypotheses are differentiability on the segment and
continuity of the derivative there; the zero-length segment is included.

This is adapted from Scott Armstrong and Julia Kempe's Apache-2.0
`scottnarmstrong/DeGiorgi/DeGiorgi/Poincare.lean`, commit
`4c1b3077d3782b24065184df4ba59501b2e56fc7`, lines 382--431. -/
theorem norm_sub_le_integral_fderiv_along_segment
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} (x y : E)
    (hd : ∀ t ∈ Icc (0 : ℝ) ‖x - y‖,
      DifferentiableAt ℝ u (x + t • (‖x - y‖⁻¹ • (y - x))))
    (hc : ContinuousOn
      (fun t => fderiv ℝ u (x + t • (‖x - y‖⁻¹ • (y - x))))
      (Icc 0 ‖x - y‖)) :
    ‖u x - u y‖ ≤ ∫ t in (0 : ℝ)..‖x - y‖,
      ‖fderiv ℝ u (x + t • (‖x - y‖⁻¹ • (y - x)))‖ := by
  by_cases hxy : x = y
  · simp [hxy]
  let L : ℝ := ‖x - y‖
  let ω : E := L⁻¹ • (y - x)
  let γ : ℝ → E := fun t => x + t • ω
  have hγ : ∀ t, HasDerivAt γ ω t := by
    intro t
    have hline : HasDerivAt (fun t => t • ω) ω t := by
      simpa using (hasDerivAt_id' (𝕜 := ℝ) t).smul_const ω
    exact hline.const_add x
  have hγ0 : γ 0 = x := by simp [γ]
  have hγ1 : γ L = y := by
    simp only [γ, ω, smul_smul]
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)), one_smul]
    abel
  have hω_norm : ‖ω‖ = 1 := by
    dsimp [ω]
    rw [norm_smul, norm_inv, norm_norm, norm_sub_rev y x,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))]
  have hd' : ∀ t ∈ Icc (0 : ℝ) L, DifferentiableAt ℝ u (γ t) := by
    intro t ht
    apply hd t
    simpa [L, γ, ω] using ht
  have hc' : ContinuousOn (fun t => fderiv ℝ u (γ t)) (Icc 0 L) := by
    simpa [L, γ, ω] using hc
  have hγ_cont : Continuous γ := by fun_prop
  have hmain :
      ‖(u ∘ γ) L - (u ∘ γ) 0‖ ≤
        ∫ t in (0 : ℝ)..L, ‖fderiv ℝ u (γ t)‖ := by
    apply norm_sub_le_integral_of_norm_deriv_le_of_le (f := u ∘ γ)
      (B := fun t => ‖fderiv ℝ u (γ t)‖) (a := 0) (b := L)
    · exact norm_nonneg _
    · intro t ht
      exact ((hd' t ht).continuousAt.comp (hγ_cont.continuousAt)).continuousWithinAt
    · intro t ht
      exact (hd' t (⟨le_of_lt ht.1, le_of_lt ht.2⟩)).comp t
        (hγ t).differentiableAt |>.differentiableWithinAt
    · filter_upwards with t ht
      have hderiv : deriv (u ∘ γ) t = (fderiv ℝ u (γ t)) ω :=
        ((hd' t (by exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩)).hasFDerivAt.comp_hasDerivAt t
          (hγ t)).deriv
      rw [hderiv]
      calc
        ‖(fderiv ℝ u (γ t)) ω‖ ≤ ‖fderiv ℝ u (γ t)‖ * ‖ω‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ u (γ t)‖ := by rw [hω_norm, mul_one]
    · exact hc'.norm.intervalIntegrable_of_Icc (by simp [L])
  rw [norm_sub_rev]
  simpa only [Function.comp_apply, hγ0, hγ1] using hmain

end TauCeti
