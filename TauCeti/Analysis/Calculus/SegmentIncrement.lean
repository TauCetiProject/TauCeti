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
* `TauCeti.norm_sub_le_integral_norm_fderiv_along_segment`: the corresponding normalized
  real-integral estimate.

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
theorem norm_sub_le_integral_norm_fderiv_along_segment
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
  have hL : 0 < L := by simp [L, norm_pos_iff.mpr (sub_ne_zero.mpr hxy)]
  have hω : L • ω = y - x := by
    simp [ω, hL.ne', smul_smul]
  have hω_norm : ‖ω‖ = 1 := by
    dsimp [ω]
    rw [norm_smul, norm_inv, norm_norm, norm_sub_rev y x,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))]
  have hγ_cont : Continuous γ := by fun_prop
  have hfc : ContinuousOn (fun t : ℝ => u (γ t)) (Icc 0 L) := by
    intro t ht
    have hcomp := (hd t ht).continuousAt.comp (x := t) hγ_cont.continuousAt
    simpa only [Function.comp_def] using hcomp.continuousWithinAt
  have hfd : DifferentiableOn ℝ (fun t : ℝ => u (γ t)) (Ioo 0 L) := by
    intro t ht
    exact ((hd t (Ioo_subset_Icc_self ht)).comp t
      (by fun_prop : DifferentiableAt ℝ γ t)).differentiableWithinAt
  have hfB : ∀ᵐ t : ℝ, t ∈ Ioo 0 L →
      ‖deriv (fun s : ℝ => u (γ s)) t‖ ≤ ‖fderiv ℝ u (γ t)‖ :=
    .of_forall fun t ht => by
      have ht' := Ioo_subset_Icc_self ht
      have hdu : DifferentiableAt ℝ u (x + t • ω) := by
        simpa [ω, L] using hd t ht'
      have hderiv : deriv (fun s : ℝ => u (γ s)) t =
          fderiv ℝ u (γ t) ω := by
        simpa only [γ] using hdu.deriv_comp_add_smul
      rw [hderiv]
      simpa only [hω_norm, mul_one] using
        (ContinuousLinearMap.le_opNorm (fderiv ℝ u (γ t)) ω)
  have hBi : IntervalIntegrable (fun t : ℝ => ‖fderiv ℝ u (γ t)‖) volume 0 L :=
    hc.norm.intervalIntegrable_of_Icc hL.le
  have hkey := norm_sub_le_integral_of_norm_deriv_le_of_le hL.le hfc hfd hfB hBi
  have hγL : γ L = y := by
    dsimp [γ]
    rw [hω, add_sub_cancel]
  have hγ0 : γ 0 = x := by simp [γ]
  rw [hγL, hγ0] at hkey
  rw [norm_sub_rev]
  simpa only [L, γ, ω] using hkey

end TauCeti
