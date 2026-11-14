/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Uniform convergence in measure of random set integrals

L¹ convergence on a product space controls pathwise integrals simultaneously over any
family of sets in the first coordinate. The exceptional event is measured by outer measure:
there is no measurability assumption on the family or on its uncountable supremum.
This applies in particular to cumulative time integrals.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace MeasureTheory

variable {α Ω E J K : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {P : Measure Ω} [SFinite μ] [SFinite P]
  {f g : α × Ω → E}

/-- A single L¹ error controls all the pathwise set integrals, even for an arbitrary,
possibly uncountable family. The event on the left need not be measurable. -/
theorem mul_measure_exists_eNorm_setIntegral_sub_gt_le
    (hf : AEStronglyMeasurable f (μ.prod P)) (hg : AEStronglyMeasurable g (μ.prod P))
    (s : J → Set α) (ε : ℝ≥0∞) :
    ε * P {ω | ∃ j, ε < ‖(∫ x in s j, f (x, ω) ∂μ) - ∫ x in s j, g (x, ω) ∂μ‖ₑ} ≤
      ∫⁻ p, ‖f p - g p‖ₑ ∂μ.prod P := by
  have hm := (hf.sub hg).eNorm
  have hsub : {ω | ∃ j, ε < ‖(∫ x in s j, f (x, ω) ∂μ) -
      ∫ x in s j, g (x, ω) ∂μ‖ₑ} ≤ᵐ[P]
      {ω | ε ≤ ∫⁻ x, ‖f (x, ω) - g (x, ω)‖ₑ ∂μ} := by
    filter_upwards [hf.prodMk_right, hg.prodMk_right] with ω hfω hgω
    rintro ⟨j, hj⟩
    apply hj.le.trans
    exact (TauCeti.MeasureTheory.enorm_integral_sub_integral_le_lintegral_enorm_sub
      hfω.restrict hgω.restrict).trans
      (lintegral_mono' Measure.restrict_le_self le_rfl)
  refine (mul_le_mul' le_rfl (measure_mono_ae hsub)).trans ?_
  have hb := mul_meas_ge_le_lintegral₀ hm.lintegral_prod_left' ε
  rw [← lintegral_prod_symm _ hm] at hb
  exact hb

/-- Product-space L¹ convergence gives uniform convergence in outer probability of
pathwise integrals over every member of a fixed family of sets. -/
theorem tendsto_measure_exists_eNorm_setIntegral_sub_gt {F : K → α × Ω → E}
    {l : Filter K} (hf : AEStronglyMeasurable f (μ.prod P))
    (hF : ∀ k, AEStronglyMeasurable (F k) (μ.prod P)) (s : J → Set α)
    (hlim : Tendsto (fun k ↦ eLpNorm (F k - f) 1 (μ.prod P)) l (𝓝 0))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    Tendsto (fun k ↦ P {ω | ∃ j,
      ε < ‖(∫ x in s j, F k (x, ω) ∂μ) - ∫ x in s j, f (x, ω) ∂μ‖ₑ}) l (𝓝 0) := by
  by_cases hεtop : ε = ∞
  · simpa [hεtop] using (tendsto_const_nhds :
      Tendsto (fun _ : K ↦ (0 : ℝ≥0∞)) l (𝓝 0))
  have hb := ENNReal.Tendsto.div_const (b := ε) hlim (Or.inr hε)
  simp only [ENNReal.zero_div] at hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (.of_forall fun _ ↦ zero_le) (.of_forall fun k ↦ ?_)
  rw [eLpNorm_one_eq_lintegral_eNorm ((hF k).sub hf)]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hε) (Or.inl hεtop)).2
  rw [mul_comm]
  exact mul_measure_exists_eNorm_setIntegral_sub_gt_le (hF k) hf s ε

end MeasureTheory
