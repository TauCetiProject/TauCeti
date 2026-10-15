/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.WindingWeight.Basic
public import TauCeti.Analysis.Complex.CauchyKernel
public import TauCeti.MeasureTheory.Function.MetricDerivative.Variation
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Trace
import TauCeti.MeasureTheory.Integral.KernelPotential
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# `L¹` bounds for winding weights

The winding weight of a curve contained in a disk has `L¹` norm bounded by twice the radius
multiplied by its total variation, equal to its integral speed. Differences of winding weights are
controlled by the associated
compactly truncated Cauchy potentials.
-/

public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace TauCeti.Green

variable {γ δ : ℝ → ℂ} {a b R : ℝ} {c : ℂ}

private theorem windingNumber_eq_cauchyPotential (hab : a ≤ b)
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hR : ∀ t ∈ uIcc a b, γ t ∈ closedBall c R) {z : ℂ}
    (hzR : z ∈ closedBall c R) (hz : z ∉ γ '' uIcc a b) :
    Contour.windingNumber γ a b z =
      -(2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ t in Ioc a b, truncatedCauchyKernel (2 * R) (z - γ t) * deriv γ t := by
  have heq : (∫ t in Ioc a b, (γ t - z)⁻¹ * deriv γ t) =
      -(∫ t in Ioc a b, truncatedCauchyKernel (2 * R) (z - γ t) * deriv γ t) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have hγR : dist c (γ t) ≤ R := by
      simpa only [dist_comm] using
        mem_closedBall.mp (hR t ((uIcc_of_le hab).symm ▸ Ioc_subset_Icc_self ht))
    have hball : z - γ t ∈ closedBall 0 (2 * R) := mem_closedBall_zero_iff.mpr (by
      rw [← dist_eq_norm]
      exact (dist_triangle z c (γ t)).trans (by linarith [mem_closedBall.mp hzR]))
    simp only [truncatedCauchyKernel_def, Set.indicator_of_mem hball]
    rw [← neg_sub z (γ t), inv_neg, neg_mul]
  rw [hγ.windingNumber_eq_integral hz,
    intervalIntegral.integral_of_le hab, heq, mul_neg, neg_mul]

/-- A winding-weight difference is controlled in `L¹` by the truncated Cauchy potentials. -/
theorem integral_norm_windingWeight_sub_le_cauchyPotential (hab : a ≤ b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hδ : AbsolutelyContinuousOnInterval δ a b)
    (hγclosed : γ a = γ b) (hδclosed : δ a = δ b)
    (hγR : ∀ t ∈ uIcc a b, γ t ∈ closedBall c R)
    (hδR : ∀ t ∈ uIcc a b, δ t ∈ closedBall c R) :
    (∫ z : ℂ, ‖windingWeight δ a b z - windingWeight γ a b z‖) ≤
      ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ *
        ∫ z : ℂ, ‖(∫ t in Ioc a b, truncatedCauchyKernel (2 * R) (z - δ t) * deriv δ t) -
          (∫ t in Ioc a b, truncatedCauchyKernel (2 * R) (z - γ t) * deriv γ t)‖ := by
  let P : (ℝ → ℂ) → ℂ → ℂ := fun ρ z ↦
    ∫ t in Ioc a b, truncatedCauchyKernel (2 * R) (z - ρ t) * deriv ρ t
  have hP {ρ : ℝ → ℂ} (hρ : AbsolutelyContinuousOnInterval ρ a b) : Integrable (P ρ) := by
    exact (integrable_truncatedCauchyKernel (2 * R)).integral_comp_sub_mul
      (measurable_truncatedCauchyKernel (2 * R)) (hρ.aemeasurable_restrict_Ioc hab)
      (hρ.integrableOn_deriv_Ioc hab)
  have hW := ((hδ.integrable_windingWeight hδclosed).sub
    (hγ.integrable_windingWeight hγclosed)).norm
  have hright := ((hP hδ).sub (hP hγ)).norm.const_mul
    ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖
  rw [← integral_const_mul]
  apply integral_mono_ae hW hright
  have hzγ := measure_eq_zero_iff_ae_notMem.mp
    (hγ.addHaar_image_uIcc_eq_zero volume (by simp [Complex.finrank_real_complex]))
  have hzδ := measure_eq_zero_iff_ae_notMem.mp
    (hδ.addHaar_image_uIcc_eq_zero volume (by simp [Complex.finrank_real_complex]))
  filter_upwards [hzγ, hzδ] with z hzγ hzδ
  simp only [Pi.sub_apply]
  by_cases hzR : z ∈ closedBall c R
  · rw [windingWeight_eq_of_notMem hzδ, windingWeight_eq_of_notMem hzγ,
      windingNumber_eq_cauchyPotential hab hδ hδR hzR hzδ,
      windingNumber_eq_cauchyPotential hab hγ hγR hzR hzγ,
      Real.norm_eq_abs, ← Complex.sub_re, ← mul_sub]
    exact (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, norm_neg])
  · have hwγ : windingWeight γ a b z = 0 := by
      by_contra h
      exact hzR (hγ.support_windingWeight_subset_closedBall hγclosed hγR h)
    have hwδ : windingWeight δ a b z = 0 := by
      by_contra h
      exact hzR (hδ.support_windingWeight_subset_closedBall hδclosed hδR h)
    rw [hwδ, hwγ, sub_self, norm_zero]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)


/-- A closed absolutely continuous curve in a disk of radius `R` has winding-weight `L¹` norm at
most `2R` times its total variation. -/
theorem integral_abs_windingWeight_le (hab : a ≤ b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hR : ∀ t ∈ uIcc a b, γ t ∈ closedBall c R) :
    (∫ z : ℂ, |windingWeight γ a b z|) ≤
      2 * R * (eVariationOn γ (uIcc a b)).toReal := by
  rw [← hγ.integral_norm_deriv_eq_eVariationOn_toReal hab]
  have hR0 : 0 ≤ R := dist_nonneg.trans (mem_closedBall.mp (hR a left_mem_uIcc))
  have hconstant : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ γ a) a b :=
    (LipschitzWith.const (α := ℝ) (γ a)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hW := integral_norm_windingWeight_sub_le_cauchyPotential hab hconstant hγ rfl hclosed
    (fun _ _ ↦ hR a left_mem_uIcc) hR
  have hW' : (∫ z : ℂ, |windingWeight γ a b z|) ≤
      ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ *
        ∫ z : ℂ, ‖∫ t in Ioc a b, truncatedCauchyKernel (2 * R) (z - γ t) *
          deriv γ t‖ := by
    simpa only [windingWeight_const, sub_zero, Real.norm_eq_abs, deriv_const,
      mul_zero, integral_zero] using hW
  have hγm := hγ.aemeasurable_restrict_Ioc hab
  have hv := hγ.integrableOn_deriv_Ioc hab
  have hP := (integrable_truncatedCauchyKernel (2 * R)).integral_norm_kernel_potential_sub_le
    (measurable_truncatedCauchyKernel (2 * R)) hγm hγm hv
    (integrable_zero ℝ ℂ (volume.restrict (Ioc a b)))
  have hP' : (∫ z : ℂ, ‖∫ t in Ioc a b,
      truncatedCauchyKernel (2 * R) (z - γ t) * deriv γ t‖) ≤
      (∫ z : ℂ, ‖truncatedCauchyKernel (2 * R) z‖) *
        ∫ t in Ioc a b, ‖deriv γ t‖ := by
    simpa only [Pi.zero_apply, mul_zero, integral_zero, sub_zero, sub_self, norm_zero, add_zero]
      using hP
  calc
    (∫ z : ℂ, |windingWeight γ a b z|) ≤
        ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ *
          ((∫ z : ℂ, ‖truncatedCauchyKernel (2 * R) z‖) *
            ∫ t in Ioc a b, ‖deriv γ t‖) :=
      hW'.trans (mul_le_mul_of_nonneg_left hP' (norm_nonneg _))
    _ = 2 * R * ∫ t in a..b, ‖deriv γ t‖ := by
      rw [integral_norm_truncatedCauchyKernel (mul_nonneg (by norm_num) hR0),
        intervalIntegral.integral_of_le hab]
      simp only [norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
      field_simp

end TauCeti.Green
