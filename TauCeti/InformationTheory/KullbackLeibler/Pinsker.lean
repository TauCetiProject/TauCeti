/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.KullbackLeibler.Variational
public import TauCeti.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Probability.Moments.SubGaussian

/-!
# Pinsker's inequality

Pinsker's inequality bounds total variation by relative entropy, with natural logarithms.
We use Mathlib's `InformationTheory.klDiv` and `SignedMeasure.totalVariation`.
The latter has total mass twice the usual total-variation distance for probability measures.
Thus `totalVariation_sq_le_two_mul_klDiv` states the classical bound
`dTV(μ, ν)² ≤ klDiv μ ν / 2`. For finite measures with common mass `M`,
`totalVariation_sq_le_two_mul_mass_mul_klDiv` gives the rescaled bound
`‖μ - ν‖² ≤ 2 * M * klDiv μ ν`. Both include infinite entropy and require only a measurable
space; the finite-measure version also covers zero mass.

The measurable-event versions are `two_mul_sq_measureReal_sub_le_klDiv` and
`two_mul_sq_measureReal_sub_le_mul_klDiv`. They use real subtraction before squaring, so
they control the absolute difference in both directions.

The proof combines `ofReal_integral_sub_log_integral_exp_le_klDiv` with Mathlib's
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` applied to an indicator function. The
eventwise characterization of total variation then gives the measure-level statement.
-/

public section

open MeasureTheory InformationTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- **Pinsker's inequality for events**, with natural logarithms. The extended-valued right
side includes infinite relative entropy, without an absolute-continuity hypothesis. -/
theorem two_mul_sq_measureReal_sub_le_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set α} (hs : MeasurableSet s) :
    ENNReal.ofReal (2 * (μ.real s - ν.real s) ^ 2) ≤ klDiv μ ν := by
  let X : α → ℝ := s.indicator (fun _ ↦ 1)
  have hX : Measurable X := measurable_const.indicator hs
  have hXint (ρ : Measure α) [IsFiniteMeasure ρ] : Integrable X ρ :=
    (integrable_const 1).indicator hs
  have hXmean (ρ : Measure α) : ∫ x, X x ∂ρ = ρ.real s := by
    simp [X, integral_indicator_const _ hs]
  have hsg := hasSubgaussianMGF_of_mem_Icc (μ := ν) hX.aemeasurable
    (a := 0) (b := 1) (ae_of_all _ fun x ↦ by
      by_cases hx : x ∈ s <;> simp [X, hx])
  let t := 4 * (μ.real s - ν.real s)
  have hcgf := hsg.cgf_le t
  have hDV := ofReal_integral_sub_log_integral_exp_le_klDiv
    (((hXint μ).sub (integrable_const (∫ x, X x ∂ν))).const_mul t)
    (hsg.integrable_exp_mul t)
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hDV
  simp only [Pi.sub_apply]
  rw [integral_const_mul, integral_sub (hXint μ) (integrable_const _),
    integral_const, probReal_univ, smul_eq_mul, one_mul, hXmean μ, hXmean ν]
  simp only [cgf, mgf, sub_zero, nnnorm_one, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_ofNat, hXmean ν] at hcgf
  dsimp [t] at *
  nlinarith

/-- The event form of **Pinsker's inequality** for finite measures of equal mass `M`:
`2 * (μ s - ν s)² ≤ M * klDiv μ ν`. This also covers zero mass and infinite entropy. -/
theorem two_mul_sq_measureReal_sub_le_mul_klDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ univ = ν univ) {s : Set α} (hs : MeasurableSet s) :
    ENNReal.ofReal (2 * (μ.real s - ν.real s) ^ 2) ≤ μ univ * klDiv μ ν := by
  by_cases hμ : μ univ = 0
  · have hν := hmass.symm.trans hμ
    simp [Measure.measure_univ_eq_zero.mp hμ, Measure.measure_univ_eq_zero.mp hν]
  let c : ℝ≥0 := (μ univ).toNNReal
  have hc : (c : ℝ≥0∞) = μ univ := ENNReal.coe_toNNReal (measure_ne_top _ _)
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by rwa [hc]
  have hcN : c ≠ 0 := by exact_mod_cast hc0
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc0
  have hprob (ρ : Measure α) (hρ : ρ univ = μ univ) :
      IsProbabilityMeasure (c⁻¹ • ρ) := by
    constructor
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv hcN, hρ, ← hc]
    exact ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top
  let := hprob μ rfl
  let := hprob ν hmass.symm
  have hp := two_mul_sq_measureReal_sub_le_klDiv (μ := c⁻¹ • μ) (ν := c⁻¹ • ν) hs
  simp only [measureReal_nnreal_smul_apply, NNReal.coe_inv, klDiv_smul_same] at hp
  calc
    ENNReal.ofReal (2 * (μ.real s - ν.real s) ^ 2) =
        (c : ℝ≥0∞) ^ 2 * ENNReal.ofReal
          (2 * ((c : ℝ)⁻¹ * μ.real s - (c : ℝ)⁻¹ * ν.real s) ^ 2) := by
      rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp only [NNReal.coe_pow]
      field_simp [hcR]
    _ ≤ (c : ℝ≥0∞) ^ 2 * ((c⁻¹ : ℝ≥0) * klDiv μ ν) := by gcongr
    _ = μ univ * klDiv μ ν := by
      rw [ENNReal.coe_inv hcN, pow_two, mul_assoc, ← mul_assoc (c : ℝ≥0∞) _ (klDiv μ ν),
        ENNReal.mul_inv_cancel hc0 ENNReal.coe_ne_top, one_mul, hc]

/-- **Pinsker's inequality** for finite measures of equal mass, using the canonical signed-measure
total variation. If their common mass is `M`, this says `‖μ - ν‖² ≤ 2 * M * klDiv μ ν`.
There is no finiteness assumption on relative entropy. -/
theorem totalVariation_sq_le_two_mul_mass_mul_klDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ univ = ν univ) :
    (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ ^ 2 ≤
      2 * μ univ * klDiv μ ν := by
  let C : ℝ≥0∞ := (μ univ * klDiv μ ν / 2) ^ (2 : ℝ)⁻¹
  have hTV : (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ ≤ 2 * C := by
    apply (Measure.totalVariation_toSignedMeasure_sub_univ_le_two_mul_iff hmass).2
    intro s hs
    apply tsub_le_iff_left.1
    dsimp [C]
    rw [ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 2), ENNReal.rpow_two,
      ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    by_cases hle : ν s ≤ μ s
    · have hnonneg : 0 ≤ μ.real s - ν.real s :=
        sub_nonneg.2 (ENNReal.toReal_mono (measure_ne_top μ s) hle)
      have h := two_mul_sq_measureReal_sub_le_mul_klDiv hmass hs
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_pow hnonneg, ENNReal.ofReal_sub _ measureReal_nonneg,
        ofReal_measureReal (measure_ne_top μ s), ofReal_measureReal (measure_ne_top ν s),
        mul_comm] using h
    · simp [tsub_eq_zero_of_le (le_of_not_ge hle)]
  calc
    (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ ^ 2 ≤ (2 * C) ^ 2 := by
      gcongr
    _ = 2 * μ univ * klDiv μ ν := by
      dsimp [C]
      rw [mul_pow, ← ENNReal.rpow_two ((μ univ * klDiv μ ν / 2) ^ (2 : ℝ)⁻¹),
        ENNReal.rpow_inv_rpow (by norm_num : (2 : ℝ) ≠ 0)]
      simp only [div_eq_mul_inv, pow_two]
      calc
        2 * 2 * (μ univ * klDiv μ ν * 2⁻¹) =
            2 * μ univ * klDiv μ ν * (2 * 2⁻¹) := by ring
        _ = 2 * μ univ * klDiv μ ν := by
          rw [ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]

/-- **Pinsker's inequality** for probability measures, with natural logarithms and no
absolute-continuity assumption. The total variation on the left is twice the usual distance
`dTV(μ, ν) = sup_s |μ s - ν s|`, so the bound is equivalently `2 * dTV(μ, ν)² ≤ klDiv μ ν`. -/
theorem totalVariation_sq_le_two_mul_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ ^ 2 ≤ 2 * klDiv μ ν := by
  simpa using totalVariation_sq_le_two_mul_mass_mul_klDiv (μ := μ) (ν := ν) (by simp)

end TauCeti
