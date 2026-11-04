/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Prod
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Distributional differentiation of cumulative vector measures

The cumulative function `x ↦ ν (Iic x)` of a vector measure of finite variation has
measure-valued distributional derivative `ν`. We express this through integration by parts
against compactly supported continuously differentiable scalar functions. Atoms are included:
no continuity of the cumulative function or absolute continuity of `ν` is required.

The proof combines Mathlib's `VectorMeasure.integral_integral_smul_swap` with its
`HasCompactSupport.integral_Ioi_deriv_eq` fundamental theorem of calculus on a half-line.
This is the bridge between cumulative measures and weak derivatives for one-dimensional
functions of bounded variation.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.2 (functions of one variable).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Integration by parts for the cumulative function of a vector measure of finite variation.
The measure may have atoms or a singular continuous part. -/
theorem _root_.MeasureTheory.VectorMeasure.integral_deriv_smul_apply_Iic_eq_neg_integral
    (ν : VectorMeasure ℝ E) [IsFiniteMeasure ν.variation] {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    ∫ x, deriv φ x • ν (Iic x) = -∫ᵛ x, φ x ∂•ν := by
  -- Restrict Lebesgue measure to the derivative's support to apply finite-measure Fubini.
  let K := tsupport (deriv φ)
  let μ := volume.restrict K
  have hK : IsCompact K := hcφ.deriv.isCompact
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have : IsFiniteMeasure μ.toSignedMeasure.variation := by
    rw [Measure.variation_toSignedMeasure]
    infer_instance
  have hdφ : Integrable (deriv φ) :=
    (hφ.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcφ.deriv
  have hkernel : Integrable (Function.uncurry fun x y : ℝ ↦
      (Iic x).indicator (fun _ ↦ deriv φ x) y) (μ.prod ν.variation) := by
    convert (hdφ.integrableOn.comp_fst ν.variation).indicator
      (measurableSet_le measurable_snd measurable_fst) using 1
    ext p
    simp [Function.uncurry, indicator]
  have hswap := VectorMeasure.integral_integral_smul_swap
    (μ := μ.toSignedMeasure) (ν := ν) (B := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E))
    (f := fun x y : ℝ ↦ (Iic x).indicator (fun _ ↦ deriv φ x) y)
    (by simpa using hkernel)
  have hscalar : ContinuousLinearMap.lsmul ℝ ℝ = (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    ext
    simp
  have hinner (y : ℝ) :
      ∫ᵛ x, (Iic x).indicator (fun _ ↦ deriv φ x) y ∂•μ.toSignedMeasure = -φ y := by
    rw [hscalar, VectorMeasure.integral_toSignedMeasure]
    have heq : (fun x ↦ (Iic x).indicator (fun _ ↦ deriv φ x) y) =
        (Ici y).indicator (deriv φ) := by
      ext x
      simp only [indicator, mem_Iic, mem_Ici]
    rw [heq]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
      (fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]),
      integral_indicator measurableSet_Ici,
      integral_Ici_eq_integral_Ioi]
    exact hcφ.integral_Ioi_deriv_eq hφ y
  simp only [VectorMeasure.integral_toSignedMeasure, hinner,
    VectorMeasure.integral_fun_neg] at hswap
  simp only [VectorMeasure.integral_indicator_const _ measurableSet_Iic,
    ContinuousLinearMap.lsmul_apply] at hswap
  rw [← hswap]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun x hx ↦ by
    simp [image_eq_zero_of_notMem_tsupport hx]).symm

end TauCeti
