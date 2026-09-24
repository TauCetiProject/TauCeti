/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Extreme
public import TauCeti.Probability.Exchangeability.Arrays.AldousHoover.Decomposition

/-!
# Uniform mixtures of dissociated exchangeable graph laws

Every exchangeable law on infinite graphs is a measurable mixture of dissociated exchangeable
graph laws, with one uniform variable on the unit interval as the mixing variable
(`InfiniteExchangeableGraphLaw.exists_dissociated_kernel`): the components are exchangeable
probability measures on the graphs on `ℕ`, almost all of them dissociated, and their mixture
against the uniform law is the original law. This is the ergodic decomposition of an
exchangeable graph law, with the extreme laws (`mem_extremePoints_iff_isDissociated`) as
components; by `InfiniteExchangeableGraphLaw.ae_eq_of_comp_eq` a dissociated law is its own only
decomposition. Representing the components by graphons is a separate step.

The decomposition is the array one (`JointlyExchangeable.exists_dissociated_kernel`) read back
through the graph-law/array-law adapter: almost every component of the array decomposition is
carried by the symmetric `false`-diagonal arrays, because a null set of a mixture is null for
almost every component (`ae_measure_eq_zero_of_comp_eq_zero`), so it decodes to an exchangeable
graph law, and decoding is linear.

`MeasureTheory.Measure.IsDissociatedGraphLaw` packages the
exchangeable probability measures on graphs whose finite law is dissociated, so that a component
of the decomposition is described by one predicate.

## Main results

* `TauCeti.Probability.ae_measure_eq_zero_of_comp_eq_zero` — a null set of a mixture is null for
  almost every component.
* `MeasureTheory.Measure.IsDissociatedGraphLaw` — dissociated exchangeable
  probability measures on graphs, with `isDissociatedGraphLaw_iff` and its extreme-point form
  `isDissociatedGraphLaw_iff_mem_extremePoints`.
* `TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw.exists_dissociated_kernel` — **every
  exchangeable graph law is a uniform mixture of dissociated exchangeable graph laws.**

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33–61, Section 5.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

open MeasureTheory ProbabilityTheory Set TauCeti.Probability
open scoped ENNReal

namespace TauCeti

namespace Probability

/-- A null set of a mixture is null for almost every component. -/
theorem ae_measure_eq_zero_of_comp_eq_zero {Z β : Type*} [MeasurableSpace Z] [MeasurableSpace β]
    {π : Measure Z} {κ : Kernel Z β} {s : Set β} (hs : MeasurableSet s) (h : (κ ∘ₘ π) s = 0) :
    ∀ᵐ z ∂π, κ z s = 0 := by
  rw [Measure.bind_apply hs κ.aemeasurable, lintegral_eq_zero_iff (κ.measurable_coe hs)] at h
  exact h

end Probability

namespace DenseGraphLimits

/-- A **dissociated exchangeable graph law**: an exchangeable probability measure on the graphs
on `ℕ` whose finite law is dissociated. -/
def _root_.MeasureTheory.Measure.IsDissociatedGraphLaw (μ : Measure (SimpleGraph ℕ)) : Prop :=
  ∃ L : InfiniteExchangeableGraphLaw, L.law = μ ∧
    (exchangeableGraphLawEquivInfinite.symm L).IsDissociated

/-- A measure is a dissociated exchangeable graph law exactly when it is an exchangeable
probability measure whose finite law is dissociated. -/
theorem isDissociatedGraphLaw_iff {μ : Measure (SimpleGraph ℕ)} :
    μ.IsDissociatedGraphLaw ↔
      ∃ hp : IsProbabilityMeasure μ, ∃ hex : ∀ σ : Equiv.Perm ℕ, μ.map (SimpleGraph.comap ⇑σ) = μ,
        (exchangeableGraphLawEquivInfinite.symm ⟨μ, hp, hex⟩).IsDissociated := by
  constructor
  · rintro ⟨L, rfl, h⟩
    exact ⟨L.prob, L.exchangeable, h⟩
  · rintro ⟨hp, hex, h⟩
    exact ⟨⟨μ, hp, hex⟩, rfl, h⟩

/-- A dissociated exchangeable graph law is an extreme exchangeable graph measure, and
conversely. -/
theorem isDissociatedGraphLaw_iff_mem_extremePoints {μ : Measure (SimpleGraph ℕ)} :
    μ.IsDissociatedGraphLaw ↔ μ ∈ extremePoints ℝ≥0∞ exchangeableGraphProbabilityMeasures := by
  constructor
  · rintro ⟨L, rfl, h⟩
    exact (mem_extremePoints_iff_isDissociated L).2 h
  · intro h
    obtain ⟨hex, hp⟩ := mem_exchangeableGraphProbabilityMeasures_iff.1 h.1
    exact ⟨⟨μ, hp, hex⟩, rfl, (mem_extremePoints_iff_isDissociated ⟨μ, hp, hex⟩).1 h⟩

/-- **Every exchangeable graph law is a uniform mixture of dissociated exchangeable graph laws.**
The components are dissociated exchangeable graph laws for almost every value of one uniform
variable on the unit interval, and their mixture is the original law. -/
theorem InfiniteExchangeableGraphLaw.exists_dissociated_kernel (L : InfiniteExchangeableGraphLaw) :
    ∃ κ : Kernel unitInterval (SimpleGraph ℕ), IsMarkovKernel κ ∧
      (∀ᵐ u ∂(volume : Measure unitInterval), (κ u).IsDissociatedGraphLaw) ∧
      κ ∘ₘ (volume : Measure unitInterval) = L.law := by
  obtain ⟨κ, hκ, hae, hmix⟩ :=
    (jointlyExchangeable_arrayLaw L.exchangeable).exists_dissociated_kernel
  -- almost every component of the array decomposition is carried by the symmetric arrays
  have hcarr : ∀ᵐ u ∂(volume : Measure unitInterval),
      κ u (symmetricArraysWithDiag Bool false)ᶜ = 0 :=
    ae_measure_eq_zero_of_comp_eq_zero (measurableSet_symmetricArraysWithDiag _).compl
      (hmix ▸ arrayLaw_compl_symmetricArraysWithDiag_eq_zero _)
  refine ⟨κ.map graphOfArray, Kernel.IsMarkovKernel.map κ measurable_graphOfArray, ?_, ?_⟩
  · filter_upwards [hae, hcarr] with u ⟨hexch, hdiss⟩ hc
    rw [Kernel.map_apply _ measurable_graphOfArray, ← graphLawOfArray_def]
    refine isDissociatedGraphLaw_iff.2 ⟨inferInstance,
      fun σ => map_comap_graphLawOfArray σ (hexch.map_pairReindex σ), ?_⟩
    rw [isDissociated_iff_jointlyDissociated, arrayLaw_graphLawOfArray hc]
    exact hdiss
  · rw [← Measure.map_comp _ _ measurable_graphOfArray, hmix, ← graphLawOfArray_def,
      graphLawOfArray_arrayLaw]

end DenseGraphLimits

end TauCeti
