/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Hausdorff

/-!
# Sample-path continuity and stopping for indistinguishable processes

Modifications with almost surely continuous paths over a separable time index into a Hausdorff
target are indistinguishable (`ProbabilityTheory.Indistinguishable.of_ae_eq`): equality at each
fixed time upgrades to simultaneous equality on a countable dense time set and then everywhere by
continuity. Conversely, indistinguishability transports almost-sure sample-path continuity,
sample-event indicators, stopped values, and stopped processes without measurability or filtration
assumptions.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §1.1, Problem 1.5.
-/

public section

open Filter MeasureTheory Set TopologicalSpace

namespace ProbabilityTheory.Indistinguishable

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E}

/-- Modifications with almost surely continuous paths over a separable index set into a Hausdorff
space are indistinguishable. -/
theorem of_ae_eq [TopologicalSpace ι] [SeparableSpace ι] [TopologicalSpace E] [T2Space E]
    (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (h : ∀ t, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := by
  obtain ⟨d, hd_count, hd_dense⟩ := TopologicalSpace.exists_countable_dense ι
  have hd : ∀ᵐ ω ∂P, ∀ t ∈ d, X t ω = Y t ω := (ae_ball_iff hd_count).2 fun t _ ↦ h t
  filter_upwards [hX, hY, hd] with ω hcX hcY hdω
  exact congrFun (hcX.ext_on hd_dense hcY hdω)

/-- Indistinguishability transports almost-sure sample-path continuity. -/
theorem ae_continuous [TopologicalSpace ι] [TopologicalSpace E]
    (h : X ≡ᵐ[P] Y) (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) :
    ∀ᵐ ω ∂P, Continuous (Y · ω) := by
  filter_upwards [h, hX] with ω hω hc
  simpa only [funext hω] using hc

/-- Restricting indistinguishable processes to a sample event preserves indistinguishability. -/
protected theorem indicator [Zero E] (h : X ≡ᵐ[P] Y) (A : Set Ω) :
    (fun t ↦ A.indicator (X t)) ≡ᵐ[P] (fun t ↦ A.indicator (Y t)) := by
  filter_upwards [h] with ω hω t
  by_cases hA : ω ∈ A <;> simp [hA, hω t]

/-- Indistinguishable processes have almost surely equal stopped values at every random time. -/
theorem stoppedValue [Nonempty ι]
    (h : X ≡ᵐ[P] Y) (τ : Ω → WithTop ι) :
    MeasureTheory.stoppedValue X τ =ᵐ[P] MeasureTheory.stoppedValue Y τ := by
  filter_upwards [h] with ω hω
  simp only [MeasureTheory.stoppedValue, hω]

/-- Stopping indistinguishable processes at any random time yields indistinguishable processes. -/
theorem stoppedProcess [LinearOrder ι] [Nonempty ι]
    (h : X ≡ᵐ[P] Y) (τ : Ω → WithTop ι) :
    MeasureTheory.stoppedProcess X τ ≡ᵐ[P] MeasureTheory.stoppedProcess Y τ := by
  filter_upwards [h] with ω hω t
  simp only [MeasureTheory.stoppedProcess, hω]

end ProbabilityTheory.Indistinguishable
