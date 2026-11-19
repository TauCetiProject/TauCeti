/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Topology.IsLocalHomeomorph
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Strong measurability of continuous functions and of descended functions

A continuous function from a space with the Borel `σ`-algebra to a pseudo-metrizable space is
strongly measurable as soon as its range lies in a compact set, since the range is then separable.
No countability assumption on the domain is needed.

Strong measurability also descends along surjective local homeomorphisms out of Lindelöf spaces,
such as covering maps of second countable manifolds: a function `g` on the base is strongly
measurable as soon as its pullback `g ∘ f` is. This is how invariant functions on a covering space
are identified with functions on its base.

## Main results

* `Continuous.stronglyMeasurable_of_range_subset_isCompact`: a continuous function whose range
  lies in a compact set is strongly measurable.
* `IsLocalHomeomorph.stronglyMeasurable_comp_iff`: for a surjective local homeomorphism `f` out of
  a Lindelöf space, `g ∘ f` is strongly measurable exactly when `g` is.
-/

public section

open MeasureTheory TopologicalSpace

/-- A continuous function whose range lies in a compact set is strongly measurable, without any
countability assumption on the domain. -/
theorem Continuous.stronglyMeasurable_of_range_subset_isCompact {X Z : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [TopologicalSpace Z]
    [PseudoMetrizableSpace Z] {u : X → Z} (hu : Continuous u) {s : Set Z} (hs : IsCompact s)
    (hus : ∀ x, u x ∈ s) : StronglyMeasurable u := by
  borelize Z
  refine stronglyMeasurable_iff_measurable_separable.2 ⟨hu.measurable, ?_⟩
  exact (hs.isSeparable).mono (Set.range_subset_iff.2 hus)

/-- For a surjective local homeomorphism `f` out of a Lindelöf space, a map `g` out of the
codomain of `f` is strongly measurable exactly when `g ∘ f` is. -/
theorem IsLocalHomeomorph.stronglyMeasurable_comp_iff {X Y Z : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [LindelofSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [TopologicalSpace Z] [PseudoMetrizableSpace Z]
    {f : X → Y} (hf : IsLocalHomeomorph f) (hsurj : Function.Surjective f) {g : Y → Z} :
    StronglyMeasurable (g ∘ f) ↔ StronglyMeasurable g := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_measurable hf.continuous.measurable⟩
  borelize Z
  rw [stronglyMeasurable_iff_measurable_separable] at h ⊢
  exact ⟨(hf.measurable_comp_iff hsurj).1 h.1, hsurj.range_comp g ▸ h.2⟩

end
