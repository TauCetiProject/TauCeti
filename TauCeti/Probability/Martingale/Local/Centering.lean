/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Basic
public import TauCeti.Probability.Process.LocalProperty
public import TauCeti.Probability.Process.Stopping

/-!
# Centering local martingales at their initial values

Native locality stops the process after multiplying by the indicator that the stopping time
is positive. Centering each stopped martingale therefore proves that a native local martingale
remains local after subtracting its initial value, even if that value is not integrable or
literally measurable for the raw initial sigma algebra.

Conversely, adding any strongly initial-measurable random variable preserves native locality
under a sigma-finite filtration. The localizers are cut off at time zero outside finite-measure
initial events on which the new initial value is bounded. Thus no initial moment assumption is
needed. This gives the centering dictionary used when constructing integrals against continuous
local martingales; no path regularity, completeness or right continuity of the filtration is
required.

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
    stoppedProcess_bot _ _
  simp only [Pi.sub_apply, hbot, Z, stoppedProcess_indicator_pos_apply, Set.indicator_apply,
    Set.mem_ofPred_eq]
  split_ifs <;> simp only [sub_self]

/-- Under a sigma-finite filtration, adding a random variable strongly measurable at the initial
time preserves native local martingales. The initial variable need not be integrable. -/
theorem martingale_add_initial [SigmaFiniteFiltration P ℱ]
    (hX : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P) {ξ : Ω → E}
    (hξ : StronglyMeasurable[ℱ ⊥] ξ) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ X t ω + ξ ω) P := by
  classical
  -- Finite-measure initial events make the bounded pieces of the initial variable integrable.
  let A : ℕ → Set Ω := fun n ↦
    {ω | ‖ξ ω‖ ≤ (n : ℝ)} ∩ spanningSets (P.trim (ℱ.le ⊥)) n
  have hA (n : ℕ) : MeasurableSet[ℱ ⊥] (A n) :=
    (measurableSet_le hξ.norm.measurable measurable_const).inter (measurableSet_spanningSets _ n)
  have hAfin (n : ℕ) : P (A n) < ⊤ := by
    refine (measure_mono Set.inter_subset_right).trans_lt ?_
    rw [← trim_measurableSet_eq (ℱ.le ⊥) (measurableSet_spanningSets _ n)]
    exact measure_spanningSets_lt_top _ n
  have hAmono : Monotone A := by
    intro n m hnm ω hω
    have hbound : ‖ξ ω‖ ≤ (n : ℝ) := hω.1
    exact ⟨hbound.trans (by exact_mod_cast hnm), monotone_spanningSets _ hnm hω.2⟩
  have hexhaust : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ A n := by
    refine ae_of_all P fun ω ↦ ?_
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖ξ ω‖),
      eventually_mem_spanningSets (P.trim (ℱ.le ⊥)) ω] with n hn hs
    exact ⟨hn, hs⟩
  refine hX.isLocalizingSequence_localSeq.locally_of_indicator hA hAmono hexhaust fun n ↦ ?_
  let Z := stoppedProcess (fun t ↦ {ω | ⊥ < hX.localSeq n ω}.indicator (X t))
    (hX.localSeq n)
  have hZ : Martingale Z ℱ P := hX.stoppedProcess_localSeq n
  have hpos : MeasurableSet[ℱ ⊥] {ω | ⊥ < hX.localSeq n ω} :=
    (hX.isLocalizingSequence_localSeq.isStoppingTime n).measurableSet_gt ⊥
  have hξn : Integrable ((A n).indicator ξ) P := by
    rw [integrable_indicator_iff (ℱ.le ⊥ _ (hA n))]
    refine IntegrableOn.of_bound (hAfin n) (hξ.mono (ℱ.le ⊥)).aestronglyMeasurable.restrict
      (n : ℝ) ?_
    filter_upwards [ae_restrict_mem (ℱ.le ⊥ _ (hA n))] with ω hω
    exact hω.1
  have hinit := (martingale_const_fun ℱ P (hξ.indicator (hA n)) hξn).indicator
    (fun t ↦ ℱ.mono bot_le _ hpos)
  convert (hZ.indicator (fun t ↦ ℱ.mono bot_le _ (hA n))).add hinit using 1
  ext t ω
  simp only [Pi.add_apply, Z, stoppedProcess_indicator_pos_apply, Set.indicator_apply,
    Set.mem_ofPred_eq]
  by_cases hω : ω ∈ A n
  · simp only [hω, ↓reduceIte]
    split_ifs <;> simp only [add_zero]
  · simp [hω]

end ProbabilityTheory.Locally

namespace MeasureTheory.StronglyMeasurable

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ι mΩ} [SigmaFiniteFiltration P ℱ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {X : ι → Ω → E}

/-- Under a sigma-finite filtration, when the initial value is strongly measurable at the initial
time, native locality is equivalent to locality of the centered process, with no initial moment
assumption. -/
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
