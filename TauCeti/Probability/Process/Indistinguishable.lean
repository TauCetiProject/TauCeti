/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Probability.Process.Stopping

/-!
# Indistinguishability for continuous and stopped processes

Two processes with almost surely continuous paths into a Hausdorff space that agree almost surely
at every time in a countable dense set are indistinguishable. In particular, on a separable time
domain, fixed-time almost-sure equality implies indistinguishability.

Indistinguishability transfers almost-sure path continuity and is preserved by stopping at any
random time, without measurability or stopping-time hypotheses.
-/

public section

open MeasureTheory Set

namespace ProbabilityTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : ι → Ω → E}

/-- Two processes with almost surely continuous paths into a Hausdorff space that agree almost
surely on a countable dense set of times are indistinguishable. -/
theorem indist_of_ae_eq_of_dense_of_ae_continuous [TopologicalSpace ι] [TopologicalSpace E]
    [T2Space E] {D : Set ι} (hDc : D.Countable) (hDd : Dense D)
    (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (heq : ∀ t ∈ D, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := by
  filter_upwards [hX, hY, (ae_ball_iff hDc).2 heq] with ω hXω hYω hDω t
  exact congrFun (hXω.ext_on hDd hYω hDω) t

/-- Two processes with almost surely continuous paths on a separable time domain into a Hausdorff
space that agree almost surely at every fixed time are indistinguishable. -/
theorem indist_of_ae_eq_of_ae_continuous [TopologicalSpace ι] [TopologicalSpace.SeparableSpace ι]
    [TopologicalSpace E] [T2Space E]
    (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (heq : ∀ t, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ι
  exact indist_of_ae_eq_of_dense_of_ae_continuous hDc hDd hX hY fun t _ ↦ heq t

namespace Indistinguishable

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

end Indistinguishable

end ProbabilityTheory
