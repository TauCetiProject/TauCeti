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
  have hc' : ContinuousOn (fun t => fderiv ℝ u (γ t)) (Icc 0 L) := by
    simpa [L, γ, ω] using hc
  have hscale : ContinuousOn (fun s : ℝ => s * L) (Icc 0 1) :=
    (continuous_id.mul continuous_const).continuousOn
  have hscale_maps : MapsTo (fun s : ℝ => s * L) (Icc 0 1) (Icc 0 L) := by
    intro s hs
    exact ⟨mul_nonneg hs.1 hL.le,
      (mul_le_mul_of_nonneg_right hs.2 hL.le).trans_eq (one_mul L)⟩
  have hpath (s : ℝ) : x + s • (y - x) = γ (s * L) := by
    simp only [γ]
    congr 1
    rw [← hω, smul_smul]
  have hc_unit : ContinuousOn
      (fun s : ℝ => fderiv ℝ u (x + s • (y - x)) (y - x)) (Icc 0 1) := by
    have hcomp := (hc'.comp hscale hscale_maps).clm_apply
      (continuousOn_const : ContinuousOn (fun _ : ℝ => y - x) (Icc 0 1))
    simpa only [Function.comp_apply, hpath] using hcomp
  have hd_unit : ∀ s ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ u (x + s • (y - x)) := by
    intro s hs
    have hsL : s * L ∈ Icc (0 : ℝ) L := hscale_maps hs
    rw [hpath]
    exact hd (s * L) hsL
  have hseg := enorm_sub_le_lintegral_enorm_fderiv_apply x (y - x) hd_unit hc_unit
  have hdir : ContinuousOn
      (fun s : ℝ => fderiv ℝ u (x + s • (y - x)) (y - x)) (Icc 0 1) := hc_unit
  have hdir_int : IntegrableOn
      (fun s : ℝ => fderiv ℝ u (x + s • (y - x)) (y - x)) (Icc 0 1) :=
    hdir.integrableOn_Icc
  have hnorm :
      (∫ s in (0 : ℝ)..1, ‖fderiv ℝ u (x + s • (y - x)) (y - x)‖) =
        (∫⁻ s in Icc (0 : ℝ) 1,
          ‖fderiv ℝ u (x + s • (y - x)) (y - x)‖ₑ).toReal := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    rw [← MeasureTheory.integral_norm_eq_lintegral_enorm]
    · rw [MeasureTheory.setIntegral_congr_set Ioc_ae_eq_Icc]
    · exact hdir_int.aestronglyMeasurable
  have hdir_int' : Integrable
      (fun s : ℝ => fderiv ℝ u (x + s • (y - x)) (y - x))
      (volume.restrict (Icc 0 1)) := hdir_int
  have hreal := ENNReal.toReal_mono
    ((hasFiniteIntegral_iff_enorm.mp hdir_int'.hasFiniteIntegral).ne) hseg
  rw [← hnorm] at hreal
  have hf : ContinuousOn (fun t : ℝ => ‖fderiv ℝ u (γ t)‖) (Icc 0 L) := hc'.norm
  have hfs : ContinuousOn (fun s : ℝ => ‖fderiv ℝ u (γ (s * L))‖) (Icc 0 1) := by
    simpa [Function.comp_def] using hf.comp hscale hscale_maps
  have hchange :
      (∫ s in (0 : ℝ)..1, ‖fderiv ℝ u (x + s • (y - x)) (y - x)‖) ≤
        ∫ t in (0 : ℝ)..L, ‖fderiv ℝ u (γ t)‖ := by
    calc
      _ ≤ ∫ s in (0 : ℝ)..1, L * ‖fderiv ℝ u (γ (s * L))‖ := by
        apply intervalIntegral.integral_mono_ae_restrict zero_le_one
        · exact hdir.norm.intervalIntegrable_of_Icc zero_le_one
        · exact (hfs.const_mul L).intervalIntegrable_of_Icc zero_le_one
        · refine Filter.Eventually.of_forall ?_
          intro s
          change ‖fderiv ℝ u (x + s • (y - x)) (y - x)‖ ≤
            L * ‖fderiv ℝ u (γ (s * L))‖
          rw [hpath]
          calc
            ‖fderiv ℝ u (γ (s * L)) (y - x)‖ =
                L * ‖fderiv ℝ u (γ (s * L)) ω‖ := by
              rw [← hω, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hL]
            _ ≤ L * (‖fderiv ℝ u (γ (s * L))‖ * ‖ω‖) :=
              mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hL.le
            _ = L * ‖fderiv ℝ u (γ (s * L))‖ := by rw [hω_norm, mul_one]
      _ = L * ∫ s in (0 : ℝ)..1, ‖fderiv ℝ u (γ (s * L))‖ := by
        rw [intervalIntegral.integral_const_mul]
      _ = ∫ t in (0 : ℝ)..L, ‖fderiv ℝ u (γ t)‖ := by
        simpa only [smul_eq_mul, zero_mul, one_mul] using
          (intervalIntegral.smul_integral_comp_mul_right
            (a := 0) (b := 1) (fun t => ‖fderiv ℝ u (γ t)‖) L)
  rw [norm_sub_rev]
  simpa only [L, γ, ω, add_sub_cancel, ← ofReal_norm,
    ENNReal.toReal_ofReal (norm_nonneg _)] using
    hreal.trans hchange

end TauCeti
