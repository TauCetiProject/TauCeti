/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LConvolution
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Young's inequality `L¹ ⋆ L² ⊆ L²` for the Lebesgue-integral convolution

Let `μ` be a left-invariant measure on a measurable additive group and let
`(f ⋆ₗ[μ] g) x = ∫⁻ y, f y * g (-y + x) ∂μ` be the convolution of extended nonnegative functions
(`MeasureTheory.lconvolution`). Young's inequality in the case `L¹ ⋆ L² ⊆ L²` reads

`∫⁻ (f ⋆ₗ[μ] g) ^ 2 ≤ (∫⁻ f) ^ 2 * ∫⁻ g ^ 2`

(`MeasureTheory.lintegral_lconvolution_sq_le`). It follows from the pointwise Cauchy–Schwarz
inequality for the measure with density `f`,

`(f ⋆ₗ[μ] g) x ^ 2 ≤ (∫⁻ f) * ∫⁻ y, f y * g (-y + x) ^ 2`

(`MeasureTheory.lconvolution_sq_le`), by integrating in `x`, exchanging the integrals and using
the left invariance of `μ`. Being stated for extended nonnegative functions, neither inequality
needs any integrability hypothesis.

The norm of a convolution of Bochner-integrable functions is bounded pointwise by the convolution
of their norms, so this inequality also bounds the `L²` norm of `f ⋆ g` for `f ∈ L¹` and `g ∈ L²`.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Graduate Studies in Mathematics 14, AMS, 2001,
  Theorem 4.2.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {G : Type*} {mG : MeasurableSpace G} [AddGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddLeftInvariant] {f g : G → ℝ≥0∞}

/-- **Pointwise Cauchy–Schwarz for a convolution.** Cauchy–Schwarz for the measure with density
`f` gives `(f ⋆ₗ[μ] g) x ^ 2 ≤ (∫⁻ f) * ∫⁻ y, f y * g (-y + x) ^ 2`. -/
theorem lconvolution_sq_le (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (x : G) :
    (f ⋆ₗ[μ] g) x ^ 2 ≤ (∫⁻ y, f y ∂μ) * ∫⁻ y, f y * g (-y + x) ^ 2 ∂μ := by
  have hgx : AEMeasurable (fun y => g (-y + x)) μ := by fun_prop
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.withDensity f) Real.HolderConjugate.two_two
    (f := fun _ => 1) aemeasurable_const (hgx.mono_ac (withDensity_absolutelyContinuous _ _))
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow] at hcs
  rw [lintegral_withDensity_eq_lintegral_mul₀ hf hgx, lintegral_one, withDensity_apply _
    MeasurableSet.univ, Measure.restrict_univ, lintegral_withDensity_eq_lintegral_mul₀ hf
    (hgx.pow_const 2)] at hcs
  calc (f ⋆ₗ[μ] g) x ^ 2
      ≤ ((∫⁻ y, f y ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ y, f y * g (-y + x) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ))
          ^ 2 := by
        rw [lconvolution_def]
        gcongr
        exact hcs
    _ = (∫⁻ y, f y ∂μ) * ∫⁻ y, f y * g (-y + x) ^ 2 ∂μ := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul]
      norm_num

/-- **Young's inequality `L¹ ⋆ L² ⊆ L²`.** For extended nonnegative functions on a group with a
left-invariant measure, `∫⁻ (f ⋆ₗ[μ] g) ^ 2 ≤ (∫⁻ f) ^ 2 * ∫⁻ g ^ 2`. -/
theorem lintegral_lconvolution_sq_le (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ x, (f ⋆ₗ[μ] g) x ^ 2 ∂μ ≤ (∫⁻ y, f y ∂μ) ^ 2 * ∫⁻ x, g x ^ 2 ∂μ := by
  calc ∫⁻ x, (f ⋆ₗ[μ] g) x ^ 2 ∂μ
      ≤ ∫⁻ x, (∫⁻ y, f y ∂μ) * ∫⁻ y, f y * g (-y + x) ^ 2 ∂μ ∂μ :=
        lintegral_mono fun x => lconvolution_sq_le hf hg x
    _ = (∫⁻ y, f y ∂μ) * ∫⁻ y, ∫⁻ x, f y * g (-y + x) ^ 2 ∂μ ∂μ := by
      rw [lintegral_const_mul'' _ (by fun_prop), lintegral_lintegral_swap (by fun_prop)]
    _ = (∫⁻ y, f y ∂μ) * ∫⁻ y, f y * ∫⁻ x, g x ^ 2 ∂μ ∂μ := by
      congr 1
      refine lintegral_congr fun y => ?_
      rw [lintegral_add_left_eq_self (fun x => f y * g x ^ 2) (-y),
        lintegral_const_mul'' _ (hg.pow_const 2)]
    _ = (∫⁻ y, f y ∂μ) ^ 2 * ∫⁻ x, g x ^ 2 ∂μ := by
      rw [lintegral_mul_const'' _ hf, sq, mul_assoc]

end MeasureTheory
