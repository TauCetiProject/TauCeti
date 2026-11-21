/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integral log-sum inequality

The log-sum of two nonnegative functions' integrals is bounded by the integral of their log
difference, including zero values and zero total masses. The proof applies
`InformationTheory.mul_log_le_toReal_klDiv` to the corresponding density measures.
-/

public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- The log-sum of the total masses is bounded by the integrated log difference. Zero values and
zero total masses are allowed; almost everywhere, a zero of the second function must also be a
zero of the first. -/
theorem integral_log_sum_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f h : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hh : 0 ≤ᵐ[μ] h)
    (hzero : ∀ᵐ x ∂μ, h x = 0 → f x = 0)
    (hfi : Integrable f μ) (hhi : Integrable h μ)
    (hdiff : Integrable (fun x ↦ f x * Real.log (f x) - f x * Real.log (h x)) μ) :
    (∫ x, f x ∂μ) * Real.log ((∫ x, f x ∂μ) / (∫ x, h x ∂μ)) ≤
      ∫ x, f x * Real.log (f x) - f x * Real.log (h x) ∂μ := by
  let F : α → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (f x)
  let H : α → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (h x)
  let R : α → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (f x / h x)
  let ρ := μ.withDensity F
  let σ := μ.withDensity H
  have hFm : AEMeasurable F μ := hfi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hHm : AEMeasurable H μ := hhi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hRm : AEMeasurable R μ :=
    (hfi.aestronglyMeasurable.aemeasurable.div
      hhi.aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have : IsFiniteMeasure ρ := isFiniteMeasure_withDensity_ofReal hfi.hasFiniteIntegral
  have : IsFiniteMeasure σ := isFiniteMeasure_withDensity_ofReal hhi.hasFiniteIntegral
  have hmul : H * R =ᵐ[μ] F := by
    filter_upwards [hh, hzero] with x hhx hz
    by_cases h0 : h x = 0
    · simp [F, H, R, h0, hz h0]
    · simp only [Pi.mul_apply, F, H, R, ← ENNReal.ofReal_mul hhx]
      congr 1
      field_simp
  have heq : ρ = σ.withDensity R := by
    dsimp [ρ, σ]
    rw [← withDensity_mul₀ hHm hRm, withDensity_congr_ae hmul]
  have hac : ρ ≪ σ := by
    rw [heq]
    exact withDensity_absolutelyContinuous _ _
  have hrn : ρ.rnDeriv σ =ᵐ[σ] R := by
    rw [heq]
    exact Measure.rnDeriv_withDensity₀ σ (hRm.mono_ac (withDensity_absolutelyContinuous μ H))
  have hratio : llr ρ σ =ᵐ[ρ] fun x ↦ Real.log (f x / h x) := by
    filter_upwards [hac.ae_le hrn, (withDensity_absolutelyContinuous μ F).ae_le hf,
      (withDensity_absolutelyContinuous μ F).ae_le hh] with x hx hfx hhx
    simp only [llr_def, hx, R, ENNReal.toReal_ofReal (div_nonneg hfx hhx)]
  have hdiff_eq : (fun x ↦ f x * Real.log (f x / h x)) =ᵐ[μ]
      (fun x ↦ f x * Real.log (f x) - f x * Real.log (h x)) := by
    filter_upwards [hzero] with x hz
    by_cases hf0 : f x = 0
    · simp [hf0]
    · have hh0 : h x ≠ 0 := fun hh0 ↦ hf0 (hz hh0)
      rw [Real.log_div hf0 hh0]
      ring
  have hFtop : ∀ᵐ x ∂μ, F x < ∞ := by
    filter_upwards with x
    exact ENNReal.ofReal_lt_top
  have hweighted : Integrable (fun x ↦ Real.log (f x / h x)) ρ := by
    change Integrable (fun x ↦ Real.log (f x / h x)) (μ.withDensity F)
    rw [integrable_withDensity_iff_integrable_smul₀' hFm hFtop]
    apply hdiff.congr
    filter_upwards [hf, hdiff_eq] with x hfx hx
    simpa [F, ENNReal.toReal_ofReal hfx, smul_eq_mul] using hx.symm
  have hllr : Integrable (llr ρ σ) ρ := hweighted.congr hratio.symm
  have hmassf : ρ.real univ = ∫ x, f x ∂μ := by
    rw [Measure.real_def]
    change ((μ.withDensity F) univ).toReal = _
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    change (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal = _
    rw [← ofReal_integral_eq_lintegral_ofReal hfi hf,
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hf)]
  have hmassh : σ.real univ = ∫ x, h x ∂μ := by
    rw [Measure.real_def]
    change ((μ.withDensity H) univ).toReal = _
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    change (∫⁻ x, ENNReal.ofReal (h x) ∂μ).toReal = _
    rw [← ofReal_integral_eq_lintegral_ofReal hhi hh,
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hh)]
  have hint : (∫ x, llr ρ σ x ∂ρ) =
      ∫ x, f x * Real.log (f x) - f x * Real.log (h x) ∂μ := by
    calc
      _ = ∫ x, Real.log (f x / h x) ∂ρ := integral_congr_ae hratio
      _ = ∫ x, (F x).toReal • Real.log (f x / h x) ∂μ :=
        integral_withDensity_eq_integral_toReal_smul₀ hFm hFtop _
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hf, hdiff_eq] with x hfx hx
        simpa [F, ENNReal.toReal_ofReal hfx, smul_eq_mul] using hx
  have hkl := InformationTheory.mul_log_le_toReal_klDiv hac hllr
  rw [InformationTheory.toReal_klDiv hac hllr, hmassf, hmassh, hint] at hkl
  linarith

end MeasureTheory.Measure
