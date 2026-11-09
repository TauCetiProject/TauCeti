/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty

/-!
# Centering local martingales at their initial values

Native locality stops the process after multiplying by the indicator that the stopping time
is positive. Centering each stopped martingale therefore proves that a native local martingale
remains local after subtracting its initial value, even if that value is not integrable or
literally measurable for the raw initial sigma algebra.

Conversely, adding any strongly initial-measurable random variable preserves native locality
under a finite measure. The localizers are cut off at time zero on the events where the new
initial value is too large. Thus no initial moment assumption is needed. This gives the
centering dictionary used when constructing integrals against continuous local martingales;
no path regularity, completeness or right continuity of the filtration is required.

The construction uses Mathlib's `Locally`, `martingale_const_fun` and martingale indicator
restriction. See Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Chapter 1, §5.
-/

public section

open Filter MeasureTheory
open scoped Topology

namespace ProbabilityTheory.Locally

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ι mΩ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : ι → Ω → E}

omit [TopologicalSpace ι] [OrderTopology ι] [NormedSpace ℝ E] [CompleteSpace E] in
private lemma stopped_indicator_apply (τ : Ω → WithTop ι) (t : ι) (ω : Ω) :
    stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ t ω =
      if ⊥ < τ ω then X (min (t : WithTop ι) (τ ω)).untopA ω else 0 := by
  rw [stoppedProcess_indicator_comm]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, stoppedProcess]

omit [TopologicalSpace ι] [OrderTopology ι] [NormedSpace ℝ E] [CompleteSpace E] in
private lemma stopped_indicator_bot (τ : Ω → WithTop ι) :
    stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ ⊥ =
      {ω | ⊥ < τ ω}.indicator (X ⊥) := by
  ext ω
  exact stoppedProcess_eq_of_le (by simp)

/-- Subtracting the initial value preserves native local martingales, without an initial
integrability or measurability assumption. -/
theorem martingale_sub_initialValue [SigmaFiniteFiltration P ℱ]
    (hX : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ X t ω - X ⊥ ω) P := by
  refine ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  let Z := stoppedProcess (fun t ↦ {ω | ⊥ < hX.localSeq n ω}.indicator (X t))
    (hX.localSeq n)
  have hZ : Martingale Z ℱ P := hX.stoppedProcess_localSeq n
  have hinit := martingale_const_fun ℱ P (hZ.stronglyMeasurable ⊥) (hZ.integrable ⊥)
  convert hZ.sub hinit using 1
  ext t ω
  have hbot : Z ⊥ = {ω | ⊥ < hX.localSeq n ω}.indicator (X ⊥) :=
    stopped_indicator_bot _
  simp only [Pi.sub_apply, hbot, Z, stopped_indicator_apply, Set.indicator_apply,
    Set.mem_ofPred_eq]
  split_ifs <;> simp only [sub_self]

/-- Under a finite measure, adding a random variable strongly measurable at the initial time
preserves native local martingales. The initial variable need not be integrable. -/
theorem martingale_add_initial [IsFiniteMeasure P]
    (hX : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P) {ξ : Ω → E}
    (hξ : StronglyMeasurable[ℱ ⊥] ξ) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ X t ω + ξ ω) P := by
  classical
  let A : ℕ → Set Ω := fun n ↦ {ω | ‖ξ ω‖ ≤ (n : ℝ)}
  have hA (n : ℕ) : MeasurableSet[ℱ ⊥] (A n) :=
    measurableSet_le hξ.norm.measurable measurable_const
  let τ : ℕ → Ω → WithTop ι := fun n ↦
    (A n).piecewise (hX.localSeq n) (fun _ ↦ ⊥)
  have hτ : IsLocalizingSequence ℱ τ P := by
    refine ⟨⟨fun n ↦ ?_, ?_⟩, ?_⟩
    · exact (hX.isLocalizingSequence_localSeq.isStoppingTime n).piecewise_of_le
        (isStoppingTime_const ℱ ⊥) (i := ⊥) (by simp) (by simp) (hA n)
    · filter_upwards [hX.isLocalizingSequence_localSeq.tendsto_top] with ω hω
      have hlarge : ∀ᶠ n : ℕ in atTop, ω ∈ A n :=
        (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖ξ ω‖))
      exact hω.congr' (hlarge.mono fun n hn ↦ by simp [τ, hn])
    · filter_upwards [hX.isLocalizingSequence_localSeq.mono] with ω hω n m hnm
      by_cases hn : ω ∈ A n
      · have hn' : ‖ξ ω‖ ≤ (n : ℝ) := hn
        have hm : ω ∈ A m := hn'.trans (by exact_mod_cast hnm)
        simpa [τ, Set.piecewise, hn, hm] using hω hnm
      · simp [τ, Set.piecewise, hn]
  refine ⟨τ, hτ, fun n ↦ ?_⟩
  let Z := stoppedProcess (fun t ↦ {ω | ⊥ < hX.localSeq n ω}.indicator (X t))
    (hX.localSeq n)
  have hZ : Martingale Z ℱ P := hX.stoppedProcess_localSeq n
  have hpos : MeasurableSet[ℱ ⊥] {ω | ⊥ < hX.localSeq n ω} :=
    (hX.isLocalizingSequence_localSeq.isStoppingTime n).measurableSet_gt ⊥
  have hξn : Integrable ((A n).indicator ξ) P := by
    apply Integrable.of_bound
      ((hξ.indicator (hA n)).mono (ℱ.le ⊥)).aestronglyMeasurable (n : ℝ)
    exact ae_of_all _ fun ω ↦ by
      by_cases hω : ω ∈ A n
      · have hbound : ‖ξ ω‖ ≤ (n : ℝ) := hω
        simpa only [Set.indicator_of_mem hω] using hbound
      · simp [hω]
  have hinit := (martingale_const_fun ℱ P (hξ.indicator (hA n)) hξn).indicator
    (fun t ↦ ℱ.mono bot_le _ hpos)
  convert (hZ.indicator (fun t ↦ ℱ.mono bot_le _ (hA n))).add hinit using 1
  ext t ω
  simp only [Pi.add_apply, Z, stopped_indicator_apply, Set.indicator_apply,
    Set.mem_ofPred_eq]
  by_cases hω : ω ∈ A n
  · simp only [τ, Set.piecewise, hω, ↓reduceIte]
    split_ifs <;> simp only [add_zero]
  · simp only [τ, Set.piecewise, hω, ↓reduceIte, lt_self_iff_false, ite_self, add_zero]

end ProbabilityTheory.Locally

namespace MeasureTheory.StronglyMeasurable

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ι mΩ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {X : ι → Ω → E}

/-- When the initial value is strongly measurable at the initial time, native locality is
equivalent to locality of the centered process, with no initial moment assumption. -/
@[simp]
theorem locally_martingale_sub_initialValue_iff (h₀ : StronglyMeasurable[ℱ ⊥] (X ⊥)) :
    ProbabilityTheory.Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ X t ω - X ⊥ ω) P ↔
    ProbabilityTheory.Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P := by
  constructor
  · intro h
    simpa only [sub_add_cancel] using h.martingale_add_initial h₀
  · exact fun h ↦ h.martingale_sub_initialValue

end MeasureTheory.StronglyMeasurable
