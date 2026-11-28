/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.MarkovChain.Filtered.Basic
import TauCeti.MeasureTheory.Integral.Bind

/-!
# Conditional event criteria for Markov chains

For an adapted process, the one-step conditional probabilities of measurable events
determine the Markov property relative to the given filtration. On a countable state space
with measurable singletons and a finite sample measure, it suffices to
test singletons. Integrating the conditional probabilities on each event of the history
identifies the restricted law of the next state with one kernel step from the restricted law
of the current state.

See Vincent Tassion, *Applied Stochastic Processes*, ETH Zürich, Spring 2025,
Proposition 1.4 and Remark 1.5 for the countable-state history-filtration formulation.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

variable {Ω S : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace S]
  {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → S} {κ : Kernel S S} {μ : Measure Ω}

/-- A one-step conditional event identity determines the mass of that event in the law
restricted to any history event. -/
private theorem map_restrict_apply_eq_comp_of_condExp_indicator [IsFiniteMeasure μ]
    [IsFiniteKernel κ] {n : ℕ} (hcurr : Measurable (X n)) (hnext : Measurable (X (n + 1)))
    {A : Set Ω} (hA : MeasurableSet[ℱ n] A)
    {B : Set S} (hB : MeasurableSet B)
    (h : μ[(X (n + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ)) | ℱ n] =ᵐ[μ]
      fun ω => (κ (X n ω)).real B) :
    (μ.restrict A).map (X (n + 1)) B = (κ ∘ₘ (μ.restrict A).map (X n)) B := by
  have hXB := hnext hB
  have hκB := (κ.measurable_coe hB).comp hcurr
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  calc
    _ = ∫ ω in A, (X (n + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω ∂μ := by
      rw [Measure.map_apply hnext hB, integral_indicator_const _ hXB,
        smul_eq_mul, mul_one, measureReal_def]
    _ = ∫ ω in A, μ[(X (n + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ)) | ℱ n] ω ∂μ :=
      (setIntegral_condExp (ℱ.le n) ((integrable_const _).indicator hXB) hA).symm
    _ = ∫ ω in A, (κ (X n ω)).real B ∂μ :=
      integral_congr_ae (ae_restrict_of_ae h)
    _ = _ := by
      rw [Measure.bind_apply hB κ.aemeasurable, lintegral_map (κ.measurable_coe hB) hcurr]
      exact integral_toReal hκB.aemeasurable (.of_forall fun _ => measure_lt_top _ _)

variable [IsMarkovKernel κ]

/-- The one-step law on history events gives the defining conditional expectations. -/
private theorem isMarkovChain_of_map_restrict_add_one [IsFiniteMeasure μ]
    (hX : Adapted ℱ X)
    (h : ∀ (n : ℕ) {A : Set Ω}, MeasurableSet[ℱ n] A →
      (μ.restrict A).map (X (n + 1)) = κ ∘ₘ (μ.restrict A).map (X n)) :
    IsMarkovChain ℱ X κ μ := by
  refine ⟨hX, fun n f hf ⟨C, hC⟩ => ?_⟩
  have hi (ν : Measure S) [IsFiniteMeasure ν] : Integrable f ν :=
    ⟨hf.aestronglyMeasurable, .of_bounded (.of_forall hC)⟩
  have hg : StronglyMeasurable[ℱ n] (fun ω => ∫ y, f y ∂κ (X n ω)) :=
    hf.stronglyMeasurable.integral_kernel.comp_measurable (hX n)
  have hgi : Integrable (fun ω => ∫ y, f y ∂κ (X n ω)) μ :=
    ⟨(hg.mono (ℱ.le n)).aestronglyMeasurable, .of_bounded (.of_forall fun ω => by
      simpa using norm_integral_le_of_norm_le_const (μ := κ (X n ω)) (.of_forall hC))⟩
  have hfi : Integrable (fun ω => f (X (n + 1) ω)) μ :=
    ⟨(hf.comp hX.measurable).aestronglyMeasurable, .of_bounded (.of_forall fun ω => hC _)⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le n) hfi
    (fun _ _ _ => hgi.integrableOn) ?_ hg.aestronglyMeasurable).symm
  intro A hA _
  symm
  rw [← integral_map hX.measurable.aemeasurable hf.aestronglyMeasurable, h n hA,
    Measure.integral_bind κ.aemeasurable (hi _),
    integral_map hX.measurable.aemeasurable
      hf.stronglyMeasurable.integral_kernel.aestronglyMeasurable]

/-- An adapted process is Markov exactly when the conditional probability of entering each
measurable set at the next step agrees with the transition kernel. Taking the whole state space
among the test events forces the sample measure to be finite. -/
theorem isMarkovChain_iff_condExp_indicator (hX : Adapted ℱ X) :
    IsMarkovChain ℱ X κ μ ↔ ∀ (n : ℕ) {B : Set S}, MeasurableSet B →
      μ[(X (n + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ)) | ℱ n] =ᵐ[μ]
        fun ω => (κ (X n ω)).real B := by
  refine ⟨fun h n B hB => ?_, fun h => ?_⟩
  · simpa only [pow_one] using h.condExp_indicator_add n 1 hB
  · have hc := h 0 MeasurableSet.univ
    simp only [preimage_univ, indicator_univ, probReal_univ] at hc
    have : IsFiniteMeasure μ := (integrable_const_iff_isFiniteMeasure one_ne_zero).mp
      (integrable_condExp.congr hc)
    exact isMarkovChain_of_map_restrict_add_one hX fun n A hA =>
      Measure.ext fun B hB =>
        map_restrict_apply_eq_comp_of_condExp_indicator hX.measurable hX.measurable hA hB (h n hB)

/-- For an adapted process with countably many measurable states and a finite sample measure,
the one-step conditional probabilities of singletons characterize the Markov property. -/
theorem isMarkovChain_iff_condExp_indicator_singleton [Countable S]
    [MeasurableSingletonClass S] [IsFiniteMeasure μ] (hX : Adapted ℱ X) :
    IsMarkovChain ℱ X κ μ ↔ ∀ (n : ℕ) (y : S),
      μ[(X (n + 1) ⁻¹' {y}).indicator (fun _ => (1 : ℝ)) | ℱ n] =ᵐ[μ]
        fun ω => (κ (X n ω)).real {y} := by
  refine ⟨fun h n y => (isMarkovChain_iff_condExp_indicator hX).mp h n (measurableSet_singleton y),
    fun h => isMarkovChain_of_map_restrict_add_one hX fun n A hA => ?_⟩
  exact Measure.ext_of_singleton fun y =>
    map_restrict_apply_eq_comp_of_condExp_indicator hX.measurable hX.measurable hA
      (measurableSet_singleton y) (h n y)

end TauCeti.Probability
