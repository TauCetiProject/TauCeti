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
to the original process (`ProbabilityTheory.Locally.ae_tendsto_stoppedProcess_localSeq`).

Cutting localizing times off at the initial time outside increasing, exhausting initial events
preserves localization (`ProbabilityTheory.IsLocalizingSequence.piecewise_bot`). The corresponding
indicator-restricted stopped stages suffice to establish any local property
(`ProbabilityTheory.IsLocalizingSequence.locally_of_indicator`).

For progressive processes with almost-surely continuous paths, adding these regularity
requirements to any local property does not change locality: the same localizers work.

Enlarging a filtration preserves its localizing sequences. The stopping-time property
transports to the larger filtration, while monotonicity and divergence are unchanged.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Chapter 1, §5, for local martingales and their localization.
-/

public section

open MeasureTheory Filter TopologicalSpace
open scoped Topology

namespace ProbabilityTheory

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

end ProbabilityTheory.Locally

namespace MeasureTheory.IsStronglyProgressive

open ProbabilityTheory

/-- For a progressive process with almost-surely continuous paths, localizing a property
is equivalent to localizing it together with progressivity and continuity.
The same native localizing sequence works in the forward direction. -/
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
  constructor
  · rintro ⟨τ, hτ, hM⟩
    refine ⟨τ, hτ, fun n ↦ ⟨hM n, ?_, ?_⟩⟩
    · rw [stoppedProcess_indicator_comm']
      exact (hp.stoppedProcess (hτ.isStoppingTime n)).indicator
        ((hτ.isStoppingTime n).measurableSet_gt ⊥)
    · filter_upwards [hc] with ω hω
      rw [stoppedProcess_indicator_comm']
      by_cases hpos : (⊥ : WithTop ι) < τ n ω
      · simpa only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hpos] using
          hω.stoppedProcess (τ := τ n)
      · simpa only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hpos] using
          (continuous_const : Continuous (fun _ : ι ↦ (0 : E)))
  · exact Locally.mono fun _ h ↦ h.1

end MeasureTheory.IsStronglyProgressive
