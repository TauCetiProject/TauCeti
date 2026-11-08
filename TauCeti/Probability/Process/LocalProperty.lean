/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.LocalProperty
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Adapted representatives of local processes

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

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Chapter 1, §5, for local martingales and their localization.
-/

public section

open MeasureTheory Filter TopologicalSpace
open scoped Topology

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
  [TopologicalSpace ι] [OrderTopology ι] {mΩ : MeasurableSpace Ω}
  {ℱ : Filtration ι mΩ} {P : Measure Ω} {τ : ℕ → Ω → WithTop ι}
  {X : ι → Ω → E} [Zero E]

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
