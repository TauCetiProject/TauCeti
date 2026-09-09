/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The increment of a function along a segment

This file bounds the increment of a function between `x` and `x + h` by the integral of its
directional derivative along the segment joining them. It is the multi-dimensional form of
Mathlib's one-dimensional `enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc`, obtained by
composing with the affine parametrization `t ↦ x + t • h` of the segment.

The hypotheses are local to the segment: differentiability at each of its points and continuity
of the directional derivative along it.

## Main declarations

* `TauCeti.enorm_sub_le_lintegral_enorm_fderiv_apply`: the segment increment estimate.
* `TauCeti.ContDiff.norm_sub_le_integral_fderiv_along_segment`: the corresponding normalized
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

/-- The norm form of the segment increment estimate on the unit interval. -/
theorem ContDiff.norm_sub_le_integral_fderiv_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} (hu : ContDiff ℝ 1 u) (x h : E) :
    ‖u (x + h) - u x‖ ≤ ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (x + t • h) h‖ := by
  have hf : Continuous (fun t : ℝ => fderiv ℝ u (x + t • h) h) :=
    ((hu.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply continuous_const
  have hfi : IntegrableOn (fun t : ℝ => fderiv ℝ u (x + t • h) h) (Icc 0 1) :=
    hf.integrableOn_Icc
  have hnorm :
      (∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (x + t • h) h‖) =
        (∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ).toReal := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    rw [← MeasureTheory.integral_norm_eq_lintegral_enorm]
    · rw [MeasureTheory.setIntegral_congr_set Ioc_ae_eq_Icc]
    · exact hfi.aestronglyMeasurable
  have hseg := enorm_sub_le_lintegral_enorm_fderiv_apply x h
    (fun t ht => (hu.differentiable (by norm_num)) (x + t • h))
    (((hu.continuous_fderiv (by norm_num)).comp_continuousOn (by fun_prop)).clm_apply
      continuousOn_const)
  have hfi' : Integrable (fun t : ℝ => fderiv ℝ u (x + t • h) h)
      (volume.restrict (Icc 0 1)) := hfi
  have hreal := ENNReal.toReal_mono
    ((hasFiniteIntegral_iff_enorm.mp hfi'.hasFiniteIntegral).ne) hseg
  rw [← hnorm] at hreal
  simpa only [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] using hreal

/-- The oscillation of a smooth function along a segment is bounded by the integrated norm of its
Fréchet derivative along that segment. The zero-length segment is included.

This is adapted from Scott Armstrong and Julia Kempe's Apache-2.0
`scottnarmstrong/DeGiorgi/DeGiorgi/Poincare.lean`, commit
`4c1b3077d3782b24065184df4ba59501b2e56fc7`, lines 382--431. The proof reuses
`enorm_sub_le_lintegral_enorm_fderiv_apply`, whose one-dimensional core is Mathlib's
`enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc`. -/
theorem ContDiff.norm_sub_le_integral_fderiv_along_segment
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} (hu : ContDiff ℝ 1 u) (x y : E) :
    ‖u x - u y‖ ≤ ∫ t in (0 : ℝ)..‖x - y‖,
      ‖fderiv ℝ u (x + t • (‖x - y‖⁻¹ • (y - x)))‖ := by
  by_cases hxy : x = y
  · simp [hxy]
  let L : ℝ := ‖x - y‖
  let ω : E := L⁻¹ • (y - x)
  let f : ℝ → ℝ := fun t => ‖fderiv ℝ u (x + t • ω)‖
  have hL : 0 < L := by simp [L, norm_pos_iff.mpr (sub_ne_zero.mpr hxy)]
  have hfderiv_cont : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hg : Continuous (fun s : ℝ => x + s • (y - x)) := by fun_prop
  have hfs : Continuous (fun s : ℝ => f (s * L)) :=
    hf.comp (continuous_id.mul continuous_const)
  have hω : L • ω = y - x := by
    simp [ω, hL.ne', smul_smul]
  have hω_norm : ‖ω‖ = 1 := by
    rw [show ‖ω‖ = |L|⁻¹ * ‖x - y‖ by simp [ω, norm_smul, norm_sub_rev y x]]
    rw [abs_of_pos hL]
    simp [L, hL.ne']
  have hchange :
      (∫ s in (0 : ℝ)..1, ‖fderiv ℝ u (x + s • (y - x)) (y - x)‖) ≤
        ∫ t in (0 : ℝ)..L, f t := by
    calc
      _ ≤ ∫ s in (0 : ℝ)..1, L * f (s * L) := by
        apply intervalIntegral.integral_mono_ae_restrict zero_le_one
        · exact (hfderiv_cont.comp hg).clm_apply continuous_const |>.norm.intervalIntegrable _ _
        · exact (continuous_const.mul hfs).intervalIntegrable _ _
        · refine Filter.Eventually.of_forall ?_
          intro s
          simp only [f]
          rw [← hω]
          simp only [smul_smul, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hL]
          calc
            L * ‖(fderiv ℝ u (x + (s * L) • ω)) ω‖ ≤
                L * (‖fderiv ℝ u (x + (s * L) • ω)‖ * ‖ω‖) :=
              mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hL.le
            _ = L * ‖fderiv ℝ u (x + (s * L) • ω)‖ := by rw [hω_norm, mul_one]
      _ = L * ∫ s in (0 : ℝ)..1, f (s * L) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ∫ t in (0 : ℝ)..L, f t := by
        simpa only [smul_eq_mul, zero_mul, one_mul] using
          (intervalIntegral.smul_integral_comp_mul_right (a := 0) (b := 1) f L)
  have hbase := TauCeti.ContDiff.norm_sub_le_integral_fderiv_apply hu x (y - x)
  have hbound := hbase.trans hchange
  rw [norm_sub_rev]
  simpa [L, ω, f, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hbound

end TauCeti
