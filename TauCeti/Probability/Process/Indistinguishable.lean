/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Indistinguishability of almost surely continuous modifications

Two processes taking values in a Hausdorff space whose sample paths are almost surely continuous
are indistinguishable as soon as they agree almost everywhere at each point of a countable dense
subset of the index space, and in particular whenever they are modifications on a separable index
space. Neither probability normalization nor coordinate measurability is needed.
-/

public section

open MeasureTheory ProbabilityTheory TopologicalSpace

namespace TauCeti

variable {ι Ω E : Type*} [TopologicalSpace ι] [MeasurableSpace Ω] {P : Measure Ω}
  [TopologicalSpace E] [T2Space E] {X Y : ι → Ω → E}

/-- Two almost surely continuous processes into a Hausdorff space that agree almost everywhere at
each point of a countable dense set `D` are indistinguishable. -/
theorem indist_of_ae_continuous_of_dense {D : Set ι} (hDc : D.Countable) (hDd : Dense D)
    (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (hXY : ∀ t ∈ D, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := by
  filter_upwards [hX, hY, (ae_ball_iff hDc).2 hXY] with ω hXω hYω hDω
  exact funext_iff.mp (Continuous.ext_on hDd hXω hYω hDω)

/-- On a separable index space, modifications with almost surely continuous paths into a Hausdorff
space are indistinguishable. -/
theorem indist_of_ae_continuous [SeparableSpace ι]
    (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (hXY : ∀ t, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense ι
  exact indist_of_ae_continuous_of_dense hDc hDd hX hY fun t _ ↦ hXY t

end TauCeti
