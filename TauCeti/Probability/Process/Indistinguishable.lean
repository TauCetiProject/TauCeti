/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.Bases

/-!
# Indistinguishability of continuous and stopped stochastic processes

Two stochastic processes on a separable topological index space taking values in a Hausdorff space
that are modifications of each other and have almost surely continuous sample paths are
indistinguishable. Neither finiteness of the measure nor measurability of the processes is needed.

Indistinguishability transfers almost-sure path continuity and is preserved by stopping at any
random time, without measurability or stopping-time hypotheses.

## Main results

* `TauCeti.indist_of_ae_continuous`: almost surely continuous modifications on a separable index
  space into a `T₂` space are indistinguishable.
* `ProbabilityTheory.Indistinguishable.ae_continuous` and
  `ProbabilityTheory.Indistinguishable.stoppedProcess`: path-continuity transfer and stopping
  invariance under indistinguishability.
-/

public section

open MeasureTheory ProbabilityTheory TopologicalSpace

namespace TauCeti

/-- Two modifications on a separable index space with almost surely continuous paths into a `T₂`
space are indistinguishable. Neither finiteness of `P` nor measurability of the processes is
needed. -/
theorem indist_of_ae_continuous {ι Ω E : Type*} [TopologicalSpace ι] [SeparableSpace ι]
    [TopologicalSpace E] [T2Space E] {_ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : ι → Ω → E} (hX : ∀ᵐ ω ∂P, Continuous (X · ω))
    (hY : ∀ᵐ ω ∂P, Continuous (Y · ω)) (hXY : ∀ t, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense ι
  have hD : ∀ᵐ ω ∂P, ∀ t ∈ D, X t ω = Y t ω := (ae_ball_iff hDc).2 fun t _ ↦ hXY t
  filter_upwards [hX, hY, hD] with ω hXω hYω hDω
  exact fun t ↦ congr_fun (Continuous.ext_on hDd hXω hYω hDω) t

end TauCeti

namespace ProbabilityTheory.Indistinguishable

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E}

/-- Indistinguishability transfers almost-sure path continuity. -/
theorem ae_continuous [TopologicalSpace ι] [TopologicalSpace E]
    (h : X ≡ᵐ[P] Y) (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) :
    ∀ᵐ ω ∂P, Continuous (Y · ω) := by
  filter_upwards [h, hX] with ω hω hXω
  exact hXω.congr hω

/-- Stopping at any random time preserves indistinguishability. No measurability or
stopping-time assumption is needed. -/
protected theorem stoppedProcess [LinearOrder ι] [Nonempty ι]
    (h : X ≡ᵐ[P] Y) (τ : Ω → WithTop ι) :
    MeasureTheory.stoppedProcess X τ ≡ᵐ[P] MeasureTheory.stoppedProcess Y τ := by
  filter_upwards [h] with ω hω t
  exact hω _

end ProbabilityTheory.Indistinguishable
