/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.TotalVariation
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Topology.Order.CountableSup
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-!
# A countable family of tests for total variation

For a separable measure, a fixed countable family of admissible smooth fields computes the
total variation of every integrable function. In particular the family does not depend on the
function being tested. This gives measurable dependence of variation on parameters without
assuming a uniform variation bound.
-/

public noncomputable section

open MeasureTheory TopologicalSpace TestFunction Filter
open scoped ENNReal Distributions Topology BoundedContinuousFunction

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {μ : Measure E} [IsSeparable μ] (Ω : Opens E)

/-- For a separable measure, one countable family of admissible test fields computes the
variation of every globally integrable function, including functions of infinite variation. -/
theorem exists_countable_totalVariationOn_eq_iSup :
    ∃ C : Set {φ : 𝓓(Ω, E) // ∀ x, ‖φ x‖ ≤ 1}, C.Countable ∧
      ∀ u : E → ℝ, Integrable u μ → totalVariationOn μ Ω u =
        ⨆ φ ∈ C, ENNReal.ofReal (∫ x, divergenceCLM φ.val x * u x ∂μ) := by
  let : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  let F (φ : {φ : 𝓓(Ω, E) // ∀ x, ‖φ x‖ ≤ 1}) (u : E →₁[μ] ℝ) :=
    ENNReal.ofReal (∫ x, divergenceCLM φ.val x * u x ∂μ)
  have hF (φ) : Continuous (F φ) := by
    apply ENNReal.continuous_ofReal.comp
    apply continuous_iff_continuousAt.mpr
    intro u
    have hlim : Tendsto (fun v : E →₁[μ] ℝ ↦ ∫⁻ x, ‖v x - u x‖ₑ ∂μ) (𝓝 u) (𝓝 0) := by
      simp_rw [← L1.ofReal_norm_sub_eq_lintegral]
      have hc : Continuous (fun v : E →₁[μ] ℝ ↦ ENNReal.ofReal ‖v - u‖) :=
        ENNReal.continuous_ofReal.comp (continuous_id.sub continuous_const).norm
      simpa using hc.tendsto u
    rw [ContinuousAt]
    simpa only [smul_eq_mul] using
      MeasureTheory.tendsto_integral_smul_of_tendsto_lintegral_enorm_sub
      (c := fun x ↦ divergenceCLM φ.val x) (s := Set.univ)
      (.of_forall fun x ↦ (divergenceCLM φ.val : E →ᵇ ℝ).norm_coe_le_norm x)
      (by simp) (.of_forall fun v ↦ (divergenceCLM φ.val).integrable_smul
        ((L1.integrable_coeFn v).locallyIntegrable.locallyIntegrableOn Ω))
      ((divergenceCLM φ.val).integrable_smul
        ((L1.integrable_coeFn u).locallyIntegrable.locallyIntegrableOn Ω)).aestronglyMeasurable
      (by simpa using hlim)
  obtain ⟨C, hC, hsup⟩ := exists_countable_iSup_eq_of_continuous hF
  refine ⟨C, hC, fun u hu ↦ ?_⟩
  have hpair (φ : {φ : 𝓓(Ω, E) // ∀ x, ‖φ x‖ ≤ 1}) :
      F φ (hu.toL1 u) = ENNReal.ofReal (∫ x, divergenceCLM φ.val x * u x ∂μ) := by
    exact congrArg ENNReal.ofReal (integral_congr_ae
      (hu.coeFn_toL1.mono fun x hx ↦ congrArg (divergenceCLM φ.val x * ·) hx))
  have h := hsup (hu.toL1 u)
  simp_rw [hpair] at h
  simpa only [totalVariationOn_def, iSup_subtype] using h

/-- The variation of integrable sections of a jointly a.e. measurable function is a.e.
measurable in the parameter. Only almost every section needs to be integrable. -/
theorem aemeasurable_totalVariationOn {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [SFinite μ] {f : X × E → ℝ} (hf : AEStronglyMeasurable f (ν.prod μ))
    (hint : ∀ᵐ y ∂ν, Integrable (fun x ↦ f (y, x)) μ) :
    AEMeasurable (fun y ↦ totalVariationOn μ Ω (fun x ↦ f (y, x))) ν := by
  obtain ⟨C, hC, hsup⟩ := exists_countable_totalVariationOn_eq_iSup (μ := μ) Ω
  have hm : AEMeasurable (fun y ↦ ⨆ φ ∈ C,
      ENNReal.ofReal (∫ x, divergenceCLM φ.val x * f (y, x) ∂μ)) ν := by
    apply AEMeasurable.biSup _ hC
    intro φ _
    apply ENNReal.measurable_ofReal.comp_aemeasurable
    have hw : AEStronglyMeasurable (fun p : X × E ↦ divergenceCLM φ.val p.2) (ν.prod μ) :=
      ((divergenceCLM φ.val).continuous.measurable.comp measurable_snd).aestronglyMeasurable
    exact (hw.mul hf).integral_prod_right'.aemeasurable
  exact hm.congr (hint.mono fun y hy ↦ (hsup _ hy).symm)

end TauCeti
