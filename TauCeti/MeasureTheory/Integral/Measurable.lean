/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Integrating against measurable families of measures

A measurable family of measures need not be an s-finite kernel. When its slices have finite
mass almost everywhere for an outer measure, integrating a jointly measurable function gives
an almost everywhere measurable function of the parameter. The Bochner version applies to
jointly strongly measurable functions with values in any normed real vector space.

The outer measure is arbitrary, and the finite-mass hypothesis is only almost everywhere:
exceptional slices may have infinite mass. In particular, no uniform mass bound or integrability
of the total mass is required. These results apply to spatial integrals of measure-valued curves
without requiring a continuity equation.

## Main results

* `Measurable.aemeasurable_lintegral_measure`: measurability of nonnegative integrals against a
  measurable family with almost everywhere finite slices.
* `MeasureTheory.StronglyMeasurable.aestronglyMeasurable_integral_measure`: strong measurability
  of Bochner integrals against such a family.
-/

public section

open MeasureTheory Set Function
open scoped ENNReal

namespace TauCeti

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : α → Measure β}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A measurable family of measures, rescaled by `(1 + μ a univ)⁻¹` to have mass at most one, as a
kernel. It lets the measurability results for finite kernels apply to `μ`. -/
private noncomputable def normalizedKernel (hμ : Measurable μ) : ProbabilityTheory.Kernel α β where
  toFun t := (1 + μ t univ)⁻¹ • μ t
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs ↦ by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ((measurable_const.add ((Measure.measurable_coe .univ).comp hμ)).inv).mul
      ((Measure.measurable_coe hs).comp hμ)

private lemma normalizedKernel_apply (hμ : Measurable μ) (t : α) :
    normalizedKernel hμ t = (1 + μ t univ)⁻¹ • μ t := rfl

private instance (hμ : Measurable μ) : ProbabilityTheory.IsFiniteKernel (normalizedKernel hμ) := by
  refine ⟨⟨1, ENNReal.one_lt_top, fun t ↦ ?_⟩⟩
  rw [normalizedKernel_apply, Measure.smul_apply, smul_eq_mul]
  rcases eq_or_ne (μ t univ) ∞ with h | h
  · simp [h]
  rw [ENNReal.inv_mul_le_iff (by simp) (by simp [h]), mul_one]
  exact le_add_self

private lemma lintegral_eq_mul_normalizedKernel (hμ : Measurable μ) {t : α} (ht : μ t univ ≠ ∞)
    (f : β → ℝ≥0∞) : ∫⁻ x, f x ∂μ t = (1 + μ t univ) * ∫⁻ x, f x ∂normalizedKernel hμ t := by
  rw [normalizedKernel_apply, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp [ht]), one_mul]

private lemma integral_eq_smul_normalizedKernel (hμ : Measurable μ) {t : α} (ht : μ t univ ≠ ∞)
    (f : β → F) : ∫ x, f x ∂μ t = (1 + μ t univ).toReal • ∫ x, f x ∂normalizedKernel hμ t := by
  have h0 : (1 + μ t univ).toReal ≠ 0 := (ENNReal.toReal_pos (by simp) (by simp [ht])).ne'
  rw [normalizedKernel_apply, integral_smul_measure, ENNReal.toReal_inv, smul_smul,
    mul_inv_cancel₀ h0, one_smul]

end TauCeti

/-- Integrating a jointly measurable nonnegative function against a measurable family of measures
with almost everywhere finite slices gives an almost everywhere measurable function. -/
theorem Measurable.aemeasurable_lintegral_measure
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : α → Measure β}
    {ν : Measure α} {f : α → β → ℝ≥0∞} (hf : Measurable (uncurry f)) (hμ : Measurable μ)
    (hμfin : ∀ᵐ a ∂ν, μ a univ ≠ ∞) :
    AEMeasurable (fun a ↦ ∫⁻ x, f a x ∂μ a) ν := by
  have hm : Measurable fun a ↦ 1 + μ a univ :=
    measurable_const.add ((Measure.measurable_coe .univ).comp hμ)
  have hκ := hf.lintegral_kernel_prod_right (κ := TauCeti.normalizedKernel hμ)
  refine (hm.mul hκ).aemeasurable.congr ?_
  filter_upwards [hμfin] with a ha
  exact (TauCeti.lintegral_eq_mul_normalizedKernel hμ ha _).symm

/-- Integrating a jointly strongly measurable function against a measurable family of measures
with almost everywhere finite slices gives an almost everywhere strongly measurable function.
The codomain needs no measurable-space, separability or completeness assumptions. -/
theorem MeasureTheory.StronglyMeasurable.aestronglyMeasurable_integral_measure
    {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : α → Measure β} {ν : Measure α}
    {f : α → β → F} (hf : StronglyMeasurable (uncurry f)) (hμ : Measurable μ)
    (hμfin : ∀ᵐ a ∂ν, μ a univ ≠ ∞) :
    AEStronglyMeasurable (fun a ↦ ∫ x, f a x ∂μ a) ν := by
  have hm : Measurable fun a ↦ 1 + μ a univ :=
    measurable_const.add ((Measure.measurable_coe .univ).comp hμ)
  have hκ := hf.integral_kernel_prod_right (κ := TauCeti.normalizedKernel hμ)
  refine (hm.ennreal_toReal.stronglyMeasurable.smul hκ).aestronglyMeasurable.congr ?_
  filter_upwards [hμfin] with a ha
  exact (TauCeti.integral_eq_smul_normalizedKernel hμ ha _).symm
