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

/-- Subtracting the initial value preserves native local martingales, without an initial
integrability or measurability assumption. The same localizing sequence works. -/
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
  have hbot : Z ⊥ ω = {ω | ⊥ < hX.localSeq n ω}.indicator (X ⊥) ω :=
    stoppedProcess_eq_of_le (by simp)
  simp only [Pi.sub_apply, hbot]
  simp [Z, stoppedProcess, Set.indicator_apply]
  split_ifs <;> simp_all

/-- Adding a random variable known at the initial time preserves native local martingales.
The initial variable need not be integrable: cut off each localizer at zero when its norm
exceeds the stage index. -/
theorem martingale_add_initial [IsFiniteMeasure P]
    (hX : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P) {ξ : Ω → E}
    (hξ : StronglyMeasurable[ℱ ⊥] ξ) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ X t ω + ξ ω) P := by
  classical
  let A : ℕ → Set Ω := fun n ↦ {ω | ‖ξ ω‖ ≤ (n : ℝ)}
  have hA (n : ℕ) : MeasurableSet[ℱ ⊥] (A n) :=
    measurableSet_le hξ.norm.measurable measurable_const
  let τ : ℕ → Ω → WithTop ι := fun n ω ↦ if ω ∈ A n then hX.localSeq n ω else ⊥
  have hτ : IsLocalizingSequence ℱ τ P := by
    refine ⟨⟨fun n t ↦ ?_, ?_⟩, ?_⟩
    · have heq : {ω | τ n ω ≤ t} = (A n)ᶜ ∪ (A n ∩ {ω | hX.localSeq n ω ≤ t}) := by
        ext ω
        simp [τ]
        split_ifs <;> simp_all
      rw [heq]
      exact (ℱ.mono bot_le _ (hA n).compl).union
        ((ℱ.mono bot_le _ (hA n)).inter
          (hX.isLocalizingSequence_localSeq.isStoppingTime n t))
    · filter_upwards [hX.isLocalizingSequence_localSeq.tendsto_top] with ω hω
      have hlarge : ∀ᶠ n : ℕ in atTop, ω ∈ A n :=
        (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖ξ ω‖))
      exact hω.congr' (hlarge.mono fun n hn ↦ by simp [τ, hn])
    · filter_upwards [hX.isLocalizingSequence_localSeq.mono] with ω hω n m hnm
      by_cases hn : ω ∈ A n
      · have hn' : ‖ξ ω‖ ≤ (n : ℝ) := hn
        have hm : ω ∈ A m := hn'.trans (by exact_mod_cast hnm)
        simpa [τ, hn, hm] using hω hnm
      · simp [τ, hn]
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
  have hinit := (martingale_const_fun ℱ P (hξ.indicator (hA n)) hξn).indicator hpos
  convert (hZ.indicator (hA n)).add hinit using 1
  ext t ω
  by_cases hω : ω ∈ A n <;>
    simp [Z, τ, stoppedProcess, Set.indicator_apply, hω]
  split_ifs <;> simp_all

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
