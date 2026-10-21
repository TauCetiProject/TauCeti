/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.MeasureTheory.Function.Lp.Translation

/-!
# Planar Cauchy kernel estimates

The complex reciprocal and its norm are locally integrable. Their integrals over a disk admit a
uniform bound in terms of the radius when the pole lies in that disk. Compact truncation of the
kernel also gives local `L¹` continuity as the pole varies.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Topology

namespace Complex

/-- The kernel `z ↦ (w - z)⁻¹` of the Cauchy transform is locally integrable on `ℂ`. -/
theorem locallyIntegrable_sub_inv (w : ℂ) :
    LocallyIntegrable (fun z : ℂ => (w - z)⁻¹) volume := by
  refine (TauCeti.locallyIntegrable_norm_sub_rpow (mu := volume) (s := -1) (by simp) w).mono
    (measurable_const.sub measurable_id).inv.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    Real.rpow_neg_one]

/-- The Cauchy kernel `z ↦ z⁻¹` is locally integrable on `ℂ`. -/
theorem locallyIntegrable_inv : LocallyIntegrable (fun z : ℂ => z⁻¹) volume := by
  convert (locallyIntegrable_sub_inv 0).neg using 1
  ext z
  simp

end Complex

namespace TauCeti

/-- The reciprocal kernel cut off outside the closed disk of radius `R`. -/
def truncatedCauchyKernel (R : ℝ) : ℂ → ℂ := (closedBall 0 R).indicator (fun z ↦ z⁻¹)

/-- The cutoff kernel is the indicator of the reciprocal on its closed disk. -/
theorem truncatedCauchyKernel_def (R : ℝ) :
    truncatedCauchyKernel R = (closedBall 0 R).indicator (fun z ↦ z⁻¹) := (rfl)

/-- The truncated Cauchy kernel is measurable. -/
theorem measurable_truncatedCauchyKernel (R : ℝ) : Measurable (truncatedCauchyKernel R) :=
  measurable_id.inv.indicator isClosed_closedBall.measurableSet

/-- The truncated Cauchy kernel is integrable. -/
theorem integrable_truncatedCauchyKernel (R : ℝ) : Integrable (truncatedCauchyKernel R) :=
  (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
    (Complex.locallyIntegrable_inv.integrableOn_isCompact (isCompact_closedBall 0 R))

/-- A pole in a disk of radius `R` contributes at most `4πR` to its inverse-distance integral. -/
theorem integral_norm_sub_inv_closedBall_le {w c : ℂ} {R : ℝ}
    (hw : w ∈ closedBall c R) :
    (∫ z in closedBall c R, ‖z - w‖⁻¹) ≤ 4 * Real.pi * R := by
  rw [Measure.restrict_congr_set (volume.addHaar_closedBall_ae_eq_ball c R)]
  have h := TauCeti.integral_norm_sub_rpow_one_sub_finrank_le (mu := volume) w hw
  norm_num [Complex.finrank_real_complex, measureReal_def, Complex.volume_ball] at h
  simpa only [Real.rpow_neg_one, norm_sub_rev] using
    h.trans_eq (by ring : _ = 4 * Real.pi * R)

/-- The inverse-distance integral over a disk centered at its pole is `2πR`. -/
theorem integral_norm_sub_inv_closedBall {R : ℝ} (hR : 0 ≤ R) (w : ℂ) :
    (∫ z in closedBall w R, ‖z - w‖⁻¹) = 2 * Real.pi * R := by
  rw [Measure.restrict_congr_set (volume.addHaar_closedBall_ae_eq_ball w R)]
  have h := TauCeti.integral_norm_sub_rpow_ball (mu := volume) (s := -1) (by simp) hR w
  norm_num [Complex.finrank_real_complex, measureReal_def, Complex.volume_ball] at h
  simpa only [Real.rpow_neg_one, norm_sub_rev, Real.rpow_one, div_one] using h

/-- The `L¹` norm of the truncated reciprocal kernel is `2πR`. -/
theorem integral_norm_truncatedCauchyKernel {R : ℝ} (hR : 0 ≤ R) :
    (∫ z : ℂ, ‖truncatedCauchyKernel R z‖) = 2 * Real.pi * R := by
  have heq : (fun z : ℂ ↦ ‖truncatedCauchyKernel R z‖) =
      (closedBall 0 R).indicator (fun z ↦ ‖z‖⁻¹) := by
    funext z
    simp only [truncatedCauchyKernel_def, norm_indicator_eq_indicator_norm, norm_inv]
  rw [heq, integral_indicator isClosed_closedBall.measurableSet]
  simpa only [sub_zero] using integral_norm_sub_inv_closedBall hR (0 : ℂ)

/-- Moving the pole continuously gives local `L¹` convergence of the complex reciprocal kernel. -/
theorem tendsto_integral_norm_sub_inv_sub_sub_inv_closedBall {ι : Type*} {l : Filter ι}
    {wn : ι → ℂ} {w : ℂ} (hw : Tendsto wn l (𝓝 w)) (c : ℂ) (R : ℝ) :
    Tendsto (fun n ↦ ∫ z in closedBall c R, ‖(z - wn n)⁻¹ - (z - w)⁻¹‖) l (𝓝 0) := by
  let T := ‖c‖ + R + ‖w‖ + 1
  have hk := integrable_truncatedCauchyKernel T
  have hlim := hk.tendsto_integral_norm_translate_sub hw
  apply squeeze_zero' (Eventually.of_forall fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) ?_
    hlim
  filter_upwards [hw.eventually (ball_mem_nhds w zero_lt_one)] with n hn
  have hnNorm : ‖wn n‖ ≤ ‖w‖ + 1 := norm_le_norm_add_const_of_dist_le (mem_ball.mp hn).le
  have heq : (∫ z in closedBall c R, ‖(z - wn n)⁻¹ - (z - w)⁻¹‖) =
      ∫ z in closedBall c R, ‖truncatedCauchyKernel T (z - wn n) -
        truncatedCauchyKernel T (z - w)‖ := by
    apply setIntegral_congr_fun isClosed_closedBall.measurableSet
    intro z hz
    have hzNorm : ‖z‖ ≤ ‖c‖ + R := norm_le_norm_add_const_of_dist_le (mem_closedBall.mp hz)
    have hzn : z - wn n ∈ closedBall 0 T :=
      mem_closedBall_zero_iff.mpr ((norm_sub_le z (wn n)).trans (by dsimp [T]; linarith))
    have hzw : z - w ∈ closedBall 0 T :=
      mem_closedBall_zero_iff.mpr ((norm_sub_le z w).trans (by dsimp [T]; linarith))
    simp only [truncatedCauchyKernel_def, Set.indicator_of_mem hzn, Set.indicator_of_mem hzw]
  rw [heq]
  exact setIntegral_le_integral ((hk.comp_sub_right (wn n)).sub (hk.comp_sub_right w)).norm
    (Eventually.of_forall fun _ ↦ norm_nonneg _)

end TauCeti
