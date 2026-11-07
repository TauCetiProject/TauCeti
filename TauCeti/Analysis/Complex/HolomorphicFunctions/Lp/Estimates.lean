/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Local integral and L² bounds for holomorphic functions

Holomorphic functions with values in a complete complex normed space satisfy the mean-value
norm bound and a local evaluation estimate in terms of their actual native `L²` class.
The open domain need not have finite measure.

## References

* J. B. Conway, *Functions of One Complex Variable II*, Chapter I.
-/

public noncomputable section

open MeasureTheory Filter Metric Set TopologicalSpace Topology InnerProductSpace
open scoped ENNReal

namespace TauCeti.HolomorphicFunctions

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {U : Opens ℂ}

/-- The norm at a point is bounded by the average norm on any ball whose closure lies in the
holomorphic domain. -/
theorem norm_le_ball_integral {f : ℂ → F} (hf : DifferentiableOn ℂ f U)
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hball : closedBall x r ⊆ U) :
    ‖f x‖ ≤ (volume.real (ball (0 : ℂ) r))⁻¹ * ∫ y in ball x r, ‖f y‖ := by
  have hh : HarmonicOnNhd f (closedBall x r) := fun y hy ↦
    (hf.analyticAt (U.isOpen.mem_nhds (hball hy))).harmonicAt
  have hpos : 0 < volume.real (ball x r) :=
    Metric.measureReal_ball_pos volume x hr
  have heq := hh.setIntegral_ball_eq (μ := volume)
  calc
    ‖f x‖ = (volume.real (ball x r))⁻¹ * ‖∫ y in ball x r, f y‖ := by
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hpos, ← mul_assoc,
        inv_mul_cancel₀ hpos.ne', one_mul]
    _ ≤ (volume.real (ball x r))⁻¹ * ∫ y in ball x r, ‖f y‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.2 hpos.le)
    _ = _ := by rw [Measure.addHaar_real_ball_center]

/-- Local evaluation of a holomorphic representative is controlled by its actual native `L²`
norm, with an explicit radius-dependent constant. -/
theorem norm_le_Lp_norm {u : Lp F 2 (volume.restrict (U : Set ℂ))}
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U)
    (hu : u =ᵐ[volume.restrict (U : Set ℂ)] f) {x : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : closedBall x r ⊆ U) :
    ‖f x‖ ≤ ((volume.real (ball (0 : ℂ) r))⁻¹ *
      ((volume (ball (0 : ℂ) r)) ^ (1 / 2 : ℝ)).toReal) * ‖u‖ := by
  have hle : volume.restrict (ball x r) ≤ volume.restrict (U : Set ℂ) :=
    Measure.restrict_mono_set volume (ball_subset_closedBall.trans hball)
  have hm := (Lp.aestronglyMeasurable u).mono_measure hle
  have hae := hu.filter_mono (ae_mono hle)
  have hfm := hm.congr hae
  have htwo : eLpNorm f 2 (volume.restrict (ball x r)) ≤
      eLpNorm u 2 (volume.restrict (U : Set ℂ)) := by
    rw [← eLpNorm_congr_ae hae]
    exact eLpNorm_mono_measure _ hle
  have hbound := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
    one_le_two hfm
  have hpow : ((volume.restrict (ball x r)) univ) ^
      (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) =
      volume (ball (0 : ℂ) r) ^ (1 / 2 : ℝ) := by
    simp [Measure.addHaar_ball_center]
    norm_num
  rw [hpow] at hbound
  have hfin : eLpNorm u 2 (volume.restrict (U : Set ℂ)) *
      volume (ball (0 : ℂ) r) ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top u)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne)
  have hone := ENNReal.toReal_mono hfin (hbound.trans
    (mul_le_mul htwo le_rfl (by positivity) (by positivity)))
  rw [ENNReal.toReal_mul, ← Lp.norm_def] at hone
  have hint : ∫ y in ball x r, ‖f y‖ =
      (eLpNorm f 1 (volume.restrict (ball x r))).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm hfm]
    exact integral_norm_eq_lintegral_enorm hfm
  refine (norm_le_ball_integral hf hr hball).trans ?_
  rw [hint, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by simpa [mul_comm] using hone) (by positivity)

end TauCeti.HolomorphicFunctions
