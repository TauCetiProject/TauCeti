/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Topology.Bases

import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Topology.Separation.Hausdorff

/-!
# Indistinguishability of continuous modifications

Two processes into a Hausdorff space with almost-surely continuous paths that agree almost
everywhere at each point of a countable dense set agree simultaneously at all parameter points
outside one common null set (`TauCeti.indist_of_ae_continuous_of_dense`). On a separable
parameter space, any two almost-surely continuous modifications of the same process are therefore
indistinguishable (`TauCeti.indist_of_ae_continuous`).

Neither finiteness of the ambient measure nor measurability of the processes is required.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Problem 1.1.5.
-/

public section

open MeasureTheory ProbabilityTheory Set TopologicalSpace

namespace TauCeti

variable {T Ω E : Type*} [TopologicalSpace T] [TopologicalSpace E] [T2Space E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : T → Ω → E}

/-- Processes into a Hausdorff space with almost-surely continuous paths that agree almost
everywhere on a countable dense parameter set are indistinguishable. -/
theorem indist_of_ae_continuous_of_dense {D : Set T} (hD_count : D.Countable) (hD_dense : Dense D)
    (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (hXY : ∀ t ∈ D, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := by
  have hD_ae : ∀ᵐ ω ∂P, ∀ t ∈ D, X t ω = Y t ω := (ae_ball_iff hD_count).2 hXY
  filter_upwards [hX, hY, hD_ae] with ω hXω hYω hDω
  exact congrFun (hXω.ext_on hD_dense hYω hDω)

/-- On a separable parameter space, two processes into a Hausdorff space with almost-surely
continuous paths that are modifications of each other are indistinguishable. -/
theorem indist_of_ae_continuous [SeparableSpace T]
    (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (hXY : ∀ t, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := by
  obtain ⟨D, hD_count, hD_dense⟩ := exists_countable_dense T
  exact indist_of_ae_continuous_of_dense hD_count hD_dense hX hY fun t _ ↦ hXY t

end TauCeti
