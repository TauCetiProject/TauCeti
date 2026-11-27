/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.LocalProperty
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import TauCeti.Probability.Process.Progressive
public import TauCeti.Probability.Process.Stopping

/-!
# Adapted representatives of local processes and filtration enlargement

A native local property controls the stopped processes
`stoppedProcess (fun t ↦ {ω | ⊥ < τ n ω}.indicator (X t)) (τ n)`.
It does not force literal adaptation of `X` on exceptional sample points.
When those stopped processes are strongly adapted, we construct a strongly adapted
representative agreeing with `X` simultaneously at every time almost surely.
In particular this applies to local martingales, without completing the filtration
or assuming any path regularity or integrability of the initial value.

The key observation is stronger than fixed-time convergence: on one common full-measure
event, the native stopped stages eventually equal the original path on each bounded
initial time interval. Their pointwise limit, set to zero where no limit exists,
therefore gives the adapted representative. Any almost-sure path property, such as
continuity, transfers along this simultaneous-time equality. This does not by itself
assert that the new representative satisfies the original local property: stopping a
merely adapted replacement at a general stopping time requires additional measurability.

For any native local property, the stopped stages converge almost surely at each fixed time
to the original process (`ProbabilityTheory.Locally.ae_tendsto_stoppedProcess_localSeq`). When the
property implies strong adaptation, fixed-time evaluations and increments are therefore a.e.
strongly measurable (`ProbabilityTheory.Locally.aestronglyMeasurable_eval`,
`ProbabilityTheory.Locally.aestronglyMeasurable_sub`).

Cutting localizing times off at the initial time outside increasing, exhausting initial events
preserves localization (`ProbabilityTheory.IsLocalizingSequence.piecewise_bot`). The corresponding
indicator-restricted stopped stages suffice to establish any local property
(`ProbabilityTheory.IsLocalizingSequence.locally_of_indicator`).

For strongly progressive processes with almost-surely continuous or right-continuous paths,
adding these regularity requirements to any local property does not change locality.

Enlarging a filtration preserves its localizing sequences. The stopping-time property
transports to the larger filtration, while monotonicity and divergence are unchanged.
An absolutely continuous change of measure also preserves localizing sequences, since their
stopping-time conditions do not involve the measure and their path conditions hold almost surely.
This does not assert preservation of the martingale property of stopped processes.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Chapter 1, §5, for local martingales and their localization.
-/

public section

open MeasureTheory Filter TopologicalSpace
open scoped Topology

namespace ProbabilityTheory

/-- An absolutely continuous change of measure preserves a pre-localizing sequence. No
finiteness of either measure is needed. -/
theorem IsPreLocalizingSequence.mono_ac {ι Ω : Type*} [Preorder ι]
    [TopologicalSpace ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ι mΩ} {P Q : Measure Ω} {τ : ℕ → Ω → WithTop ι}
    (hτ : IsPreLocalizingSequence ℱ τ P) (hQP : Q ≪ P) :
    IsPreLocalizingSequence ℱ τ Q :=
  ⟨hτ.isStoppingTime, hQP.ae_le hτ.tendsto_top⟩

/-- An absolutely continuous change of measure preserves a native localizing sequence,
including its almost-sure monotonicity. It need not preserve any localized martingale identities. -/
theorem IsLocalizingSequence.mono_ac {ι Ω : Type*} [Preorder ι]
    [TopologicalSpace ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ι mΩ} {P Q : Measure Ω} {τ : ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence ℱ τ P) (hQP : Q ≪ P) :
    IsLocalizingSequence ℱ τ Q :=
  ⟨hτ.toIsPreLocalizingSequence.mono_ac hQP, hQP.ae_le hτ.mono⟩

/-- Cutting a localizing sequence off at the initial time outside increasing initial-measurable
events which eventually contain almost every sample point preserves localization. -/
theorem IsLocalizingSequence.piecewise_bot {ι Ω : Type*} [Preorder ι] [OrderBot ι]
    [TopologicalSpace ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ι mΩ} {P : Measure Ω} {τ : ℕ → Ω → WithTop ι}
    (hτ : IsLocalizingSequence ℱ τ P) {A : ℕ → Set Ω} [∀ n, DecidablePred (· ∈ A n)]
    (hA : ∀ n, MeasurableSet[ℱ ⊥] (A n)) (hmono : Monotone A)
    (hexhaust : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ A n) :
    IsLocalizingSequence ℱ (fun n ↦ (A n).piecewise (τ n) (fun _ ↦ ⊥)) P := by
  refine ⟨⟨fun n ↦ ?_, ?_⟩, ?_⟩
  · exact (hτ.isStoppingTime n).piecewise_of_le (isStoppingTime_const ℱ ⊥)
      (i := ⊥) (by simp) (by simp) (hA n)
  · filter_upwards [hτ.tendsto_top, hexhaust] with ω hω hlarge
    exact hω.congr' (hlarge.mono fun n hn ↦ by simp [hn])
  · filter_upwards [hτ.mono] with ω hω n m hnm
    by_cases hn : ω ∈ A n
    · have hm : ω ∈ A m := hmono hnm hn
      simpa [Set.piecewise, hn, hm] using hω hnm
    · simp [Set.piecewise, hn]

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
  {ℱ : Filtration ι mΩ} {P : Measure Ω} {τ : ℕ → Ω → WithTop ι}
  {X : ι → Ω → E} [Zero E]

/-- To establish a native local property, it suffices to establish it for stopped stages
restricted to increasing, exhausting initial-measurable events. The localizers are cut off
at the initial time outside those events, without any sigma-finiteness assumption. -/
theorem IsLocalizingSequence.locally_of_indicator (hτ : IsLocalizingSequence ℱ τ P)
    {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet[ℱ ⊥] (A n)) (hmono : Monotone A)
    (hexhaust : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ A n) {p : (ι → Ω → E) → Prop}
    (hp : ∀ n, p (fun t ↦ (A n).indicator (stoppedProcess
      (fun s ↦ {ω | ⊥ < τ n ω}.indicator (X s)) (τ n) t))) :
    Locally p ℱ X P := by
  classical
  refine ⟨_, hτ.piecewise_bot hA hmono hexhaust, fun n ↦ ?_⟩
  convert hp n using 1
  ext t ω
  simp only [stoppedProcess_indicator_pos_apply]
  by_cases hω : ω ∈ A n
  · simp only [Set.piecewise, hω, ↓reduceIte, Set.indicator_of_mem hω]
    simp only [stoppedProcess_indicator_pos_apply]
  · simp [hω]

/-- On one common full-measure event, native stopped stages along a localizing sequence
are eventually equal to the original path on each bounded initial time interval.
The same index works for every time in that interval, including the initial time. -/
theorem IsPreLocalizingSequence.ae_eventually_eqOn_stoppedProcess
    (hτ : IsPreLocalizingSequence ℱ τ P) :
    ∀ᵐ ω ∂P, ∀ T : ι, ∀ᶠ n in atTop,
      Set.EqOn (fun t ↦ stoppedProcess
        (fun s ↦ {ω | ⊥ < τ n ω}.indicator (X s)) (τ n) t ω)
        (fun t ↦ X t ω) (Set.Iic T) := by
  filter_upwards [hτ.tendsto_top] with ω hω
  intro T
  have hevent : ∀ᶠ n in atTop, (T : WithTop ι) < τ n ω :=
    hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top T))
  filter_upwards [hevent] with n hn
  intro t ht
  simp only [stoppedProcess_eq_of_le ((WithTop.coe_le_coe.mpr ht).trans hn.le)]
  exact Set.indicator_of_mem (s := {ω | ⊥ < τ n ω}) (lt_of_le_of_lt bot_le hn) _

/-- If a process locally has a property implying strong adaptation, it has a strongly
adapted representative equal to it at all times outside one common null set.

For a local martingale, take `hp := fun _ h ↦ h.stronglyAdapted`. No continuity,
usual-filtration condition, finite-measure condition, or initial moment is required.
The conclusion is indistinguishability, not literal adaptation of the original process. -/
theorem Locally.exists_stronglyAdapted_ae_eq [TopologicalSpace E]
    [IsCompletelyMetrizableSpace E] {p : (ι → Ω → E) → Prop}
    (hX : Locally p ℱ X P) (hp : ∀ Y, p Y → StronglyAdapted ℱ Y) :
    ∃ Y : ι → Ω → E, StronglyAdapted ℱ Y ∧ ∀ᵐ ω ∂P, ∀ t, Y t ω = X t ω := by
  classical
  let Z n := stoppedProcess
    (fun s ↦ {ω | ⊥ < hX.localSeq n ω}.indicator (X s)) (hX.localSeq n)
  have hZ : ∀ n, StronglyAdapted ℱ (Z n) := fun n ↦ hp _ (hX.stoppedProcess_localSeq n)
  let Y t ω := if ∃ c, Tendsto (fun n ↦ Z n t ω) atTop (𝓝 c)
    then limUnder atTop (fun n ↦ Z n t ω) else 0
  refine ⟨Y, fun t ↦ ?_, ?_⟩
  · let : MeasurableSpace Ω := ℱ t
    exact (StronglyMeasurable.limUnder (fun n ↦ hZ n t)).ite
      (StronglyMeasurable.measurableSet_exists_tendsto (fun n ↦ hZ n t))
      stronglyMeasurable_const
  · filter_upwards [IsPreLocalizingSequence.ae_eventually_eqOn_stoppedProcess
      (X := X) hX.isLocalizingSequence_localSeq.toIsPreLocalizingSequence] with ω hω
    intro t
    have heq : (fun n ↦ Z n t ω) =ᶠ[atTop] fun _ ↦ X t ω :=
      (hω t).mono fun n hn ↦ hn Set.self_mem_Iic
    have hlim : Tendsto (fun n ↦ Z n t ω) atTop (𝓝 (X t ω)) :=
      tendsto_const_nhds.congr' heq.symm
    have hex : ∃ c, Tendsto (fun n ↦ Z n t ω) atTop (𝓝 c) := ⟨_, hlim⟩
    simp only [Y, ite_eq_left hex, hlim.limUnder_eq]

end ProbabilityTheory

namespace ProbabilityTheory.IsLocalizingSequence

open MeasureTheory

/-- A localizing sequence for a filtration also localizes any larger filtration. -/
theorem mono_filtration {ι Ω : Type*} [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ 𝒢 : Filtration ι mΩ}
    {τ : ℕ → Ω → WithTop ι} (hτ : IsLocalizingSequence ℱ τ μ) (h : ℱ ≤ 𝒢) :
    IsLocalizingSequence 𝒢 τ μ where
  isStoppingTime n := (hτ.isStoppingTime n).mono_filtration h
  tendsto_top := hτ.tendsto_top
  mono := hτ.mono

end ProbabilityTheory.IsLocalizingSequence

namespace ProbabilityTheory.Locally

open Filter MeasureTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι] [Zero E] [TopologicalSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ι mΩ}
  {X : ι → Ω → E} {p : (ι → Ω → E) → Prop}

/-- At each fixed time, the native stopped stages of any local property converge almost surely
to the original process, including the indicator of a strictly positive localizing time. -/
theorem ae_tendsto_stoppedProcess_localSeq (hX : Locally p ℱ X P) (t : ι) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ stoppedProcess
      (fun u ↦ {ω | ⊥ < hX.localSeq n ω}.indicator (X u)) (hX.localSeq n) t ω)
      atTop (𝓝 (X t ω)) := by
  filter_upwards [hX.isLocalizingSequence_localSeq.tendsto_top] with ω hω
  have ht := hω.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))
  apply tendsto_const_nhds.congr'
  filter_upwards [ht] with n hn
  rw [stoppedProcess_eq_of_le hn.le, Set.indicator_of_mem]
  exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr bot_le) hn

/-- If a process locally has a property implying strong adaptation, its value at each fixed time
is a.e. strongly measurable. -/
theorem aestronglyMeasurable_eval [PseudoMetrizableSpace E]
    (hX : Locally p ℱ X P) (hp : ∀ Y, p Y → StronglyAdapted ℱ Y) (t : ι) :
    AEStronglyMeasurable (X t) P :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (fun n ↦ ((hp _ (hX.stoppedProcess_localSeq n) t).mono (ℱ.le t)).aestronglyMeasurable)
    (hX.ae_tendsto_stoppedProcess_localSeq t)

/-- If a process locally has a property implying strong adaptation, every increment `X t - X s`
is a.e. strongly measurable. -/
theorem aestronglyMeasurable_sub [PseudoMetrizableSpace E] [Sub E] [ContinuousSub E]
    (hX : Locally p ℱ X P) (hp : ∀ Y, p Y → StronglyAdapted ℱ Y) (s t : ι) :
    AEStronglyMeasurable (fun ω ↦ X t ω - X s ω) P :=
  continuous_sub.comp_aestronglyMeasurable
    ((hX.aestronglyMeasurable_eval hp t).prodMk (hX.aestronglyMeasurable_eval hp s))

end ProbabilityTheory.Locally

namespace ProbabilityTheory.IsStable

/-- Adding a stable property already satisfied by a process does not change locality. -/
theorem locally_and_iff_of_prop
    {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [TopologicalSpace ι] [OrderTopology ι] [Zero E]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ι mΩ}
    {X : ι → Ω → E} {p q : (ι → Ω → E) → Prop}
    (hq : IsStable ℱ q) (hqX : q X) :
    Locally (fun Y ↦ p Y ∧ q Y) ℱ X P ↔ Locally p ℱ X P := by
  refine ⟨Locally.left, ?_⟩
  rintro ⟨τ, hτ, hpτ⟩
  exact ⟨τ, hτ, fun n ↦ ⟨hpτ n, hq X hqX (τ n) (hτ.isStoppingTime n)⟩⟩

end ProbabilityTheory.IsStable

namespace MeasureTheory.Filtration

open ProbabilityTheory

/-- Strong progressivity is stable under native indicator-stopping. -/
theorem isStable_isStronglyProgressive
    {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    [PseudoMetrizableSpace ι] [MeasurableSpace ι] [BorelSpace ι]
    {mΩ : MeasurableSpace Ω} [TopologicalSpace E] [Zero E]
    (ℱ : Filtration ι mΩ) : IsStable ℱ (IsStronglyProgressive (β := E) ℱ) := by
  intro X hp τ hτ
  rw [stoppedProcess_indicator_comm']
  exact (hp.stoppedProcess hτ).indicator (fun t ↦ ℱ.mono bot_le _ (hτ.measurableSet_gt ⊥))

/-- Almost-sure path continuity is stable under native indicator-stopping. -/
theorem isStable_ae_continuous
    {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [TopologicalSpace ι] [OrderClosedTopology ι]
    {mΩ : MeasurableSpace Ω} [TopologicalSpace E] [Zero E]
    (ℱ : Filtration ι mΩ) (P : Measure Ω) :
    IsStable ℱ (fun X : ι → Ω → E ↦ ∀ᵐ ω ∂P, Continuous (X · ω)) := by
  intro X hc τ _
  filter_upwards [hc] with ω hω
  rw [stoppedProcess_indicator_comm']
  by_cases hpos : (⊥ : WithTop ι) < τ ω
  · simpa only [Set.indicator_of_mem (s := {ω | ⊥ < τ ω}) hpos] using
      hω.stoppedProcess (τ := τ)
  · simpa only [Set.indicator_of_notMem (s := {ω | ⊥ < τ ω}) hpos] using
      (continuous_const : Continuous (fun _ : ι ↦ (0 : E)))

/-- Almost-sure path right continuity is stable under native indicator-stopping. -/
theorem isStable_ae_isRightContinuous
    {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [TopologicalSpace ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} [TopologicalSpace E] [Zero E]
    (ℱ : Filtration ι mΩ) (P : Measure Ω) :
    IsStable ℱ (fun X : ι → Ω → E ↦ ∀ᵐ ω ∂P, _root_.IsRightContinuous (X · ω)) := by
  intro X hc τ _
  filter_upwards [hc] with ω hω
  rw [stoppedProcess_indicator_comm']
  by_cases hpos : (⊥ : WithTop ι) < τ ω
  · have hstop : _root_.IsRightContinuous (stoppedProcess X τ · ω) :=
      fun t ↦ (hω t).stoppedProcess (τ := τ)
    simpa only [Set.indicator_of_mem (s := {ω | ⊥ < τ ω}) hpos] using hstop
  · simpa only [Set.indicator_of_notMem (s := {ω | ⊥ < τ ω}) hpos] using
      (continuous_const.isRightContinuous : _root_.IsRightContinuous (fun _ : ι ↦ (0 : E)))

end MeasureTheory.Filtration

namespace MeasureTheory.IsStronglyProgressive

open ProbabilityTheory

/-- For a strongly progressive process with almost-surely continuous paths, localizing a property
is equivalent to localizing it together with strong progressivity and almost-sure continuity. -/
theorem locally_iff_locally_isStronglyProgressive_ae_continuous
    {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    [PseudoMetrizableSpace ι] [MeasurableSpace ι] [BorelSpace ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [TopologicalSpace E] [Zero E]
    {ℱ : Filtration ι mΩ} {X : ι → Ω → E}
    (hp : IsStronglyProgressive ℱ X) (hc : ∀ᵐ ω ∂P, Continuous (X · ω))
    (p : (ι → Ω → E) → Prop) :
    Locally p ℱ X P ↔ Locally (fun Y ↦ p Y ∧ IsStronglyProgressive ℱ Y ∧
      ∀ᵐ ω ∂P, Continuous (Y · ω)) ℱ X P := by
  exact ((ℱ.isStable_isStronglyProgressive.and (ℱ.isStable_ae_continuous P)).locally_and_iff_of_prop
    ⟨hp, hc⟩).symm

/-- For a strongly progressive process with almost-surely right-continuous paths, localizing a
property is equivalent to localizing it together with both regularity requirements. -/
theorem locally_iff_locally_isStronglyProgressive_ae_isRightContinuous
    {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    [PseudoMetrizableSpace ι] [MeasurableSpace ι] [BorelSpace ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [TopologicalSpace E] [Zero E]
    {ℱ : Filtration ι mΩ} {X : ι → Ω → E}
    (hp : IsStronglyProgressive ℱ X) (hc : ∀ᵐ ω ∂P, IsRightContinuous (X · ω))
    (p : (ι → Ω → E) → Prop) :
    Locally p ℱ X P ↔ Locally (fun Y ↦ p Y ∧ IsStronglyProgressive ℱ Y ∧
      ∀ᵐ ω ∂P, IsRightContinuous (Y · ω)) ℱ X P := by
  exact ((ℱ.isStable_isStronglyProgressive.and
    (ℱ.isStable_ae_isRightContinuous P)).locally_and_iff_of_prop ⟨hp, hc⟩).symm

end MeasureTheory.IsStronglyProgressive
