/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory

/-!
# Orbitwise measurability of operator fields

An operator field whose fixed-vector orbits are strongly measurable sends strongly measurable
vectors to strongly measurable vectors. The same holds almost everywhere, allowing a separate
exceptional set for each fixed vector. Finite strong measurability of the vector gives finite
strong measurability of its image for arbitrary measures: linear operators preserve zero.

For composition of operator fields, apply the evaluation lemma as
`(hB x).clm_apply_of_forall hA` for each fixed vector `x`.
For finite-support conclusions it suffices that the right field has finitely strongly
measurable orbits. Neither completeness nor operator-norm measurability is needed. Addition
and scalar multiplication of orbits use the native strong-measurability arithmetic lemmas.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*,
  Volume I, §1.1, Proposition 1.1.28.
-/

public section

open MeasureTheory

variable {S 𝕜 E F : Type*} [MeasurableSpace S] {μ : Measure S}
  [NormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace MeasureTheory

/-- An orbitwise strongly measurable operator field applied to a strongly measurable vector
is strongly measurable. -/
theorem StronglyMeasurable.clm_apply_of_forall {u : S → E} (hu : StronglyMeasurable u)
    {A : S → E →L[𝕜] F} (hA : ∀ x, StronglyMeasurable (fun s ↦ A s x)) :
    StronglyMeasurable (fun s ↦ A s (u s)) :=
  hu.apply_of_forall_of_continuousAt hA (fun s ↦ (A s).continuous.continuousAt)

/-- Orbitwise a.e. strong measurability suffices for evaluating an operator field at an a.e.
strongly measurable vector; exceptional sets for the orbits may depend on the vector. -/
theorem AEStronglyMeasurable.clm_apply_of_forall {u : S → E} (hu : AEStronglyMeasurable u μ)
    {A : S → E →L[𝕜] F} (hA : ∀ x, AEStronglyMeasurable (fun s ↦ A s x) μ) :
    AEStronglyMeasurable (fun s ↦ A s (u s)) μ :=
  hu.apply_of_forall_of_continuousAt hA (.of_forall fun s ↦ (A s).continuous.continuousAt)

/-- An orbitwise strongly measurable field preserves finite strong measurability of vectors
for arbitrary measures. -/
theorem FinStronglyMeasurable.clm_apply_of_forall {u : S → E}
    (hu : FinStronglyMeasurable u μ)
    {A : S → E →L[𝕜] F} (hA : ∀ x, StronglyMeasurable (fun s ↦ A s x)) :
    FinStronglyMeasurable (fun s ↦ A s (u s)) μ :=
  hu.apply_of_forall_of_continuousAt hA (fun s ↦ (A s).continuous.continuousAt)
    (fun s ↦ (A s).map_zero)

/-- An orbitwise a.e. strongly measurable field preserves a.e. finite strong measurability
of vectors, without sigma-finiteness of the ambient measure. -/
theorem AEFinStronglyMeasurable.clm_apply_of_forall {u : S → E}
    (hu : AEFinStronglyMeasurable u μ)
    {A : S → E →L[𝕜] F} (hA : ∀ x, AEStronglyMeasurable (fun s ↦ A s x) μ) :
    AEFinStronglyMeasurable (fun s ↦ A s (u s)) μ :=
  hu.apply_of_forall_of_continuousAt hA (.of_forall fun s ↦ (A s).continuous.continuousAt)
    (.of_forall fun s ↦ (A s).map_zero)

end MeasureTheory
