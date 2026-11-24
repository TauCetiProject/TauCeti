/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Strong measurability: continuous maps with compact range and descent along local homeomorphisms

A continuous function from a space with the Borel `σ`-algebra to a pseudo-metrizable space is
strongly measurable as soon as its range lies in a compact set, since the range is then separable.
No countability assumption on the domain is needed.

Strong measurability also descends along a surjective local homeomorphism out of a Lindelöf
space: a function on its codomain is strongly measurable exactly when its composite with the local
homeomorphism is. Extending an `mΩ`-strongly measurable function by zero outside a set `T` gives
an `mProd`-strongly measurable function on `ι × Ω` whenever `T ×ˢ A` is `mProd`-measurable for all
`mΩ`-measurable `A`.

## Main results

* `Continuous.stronglyMeasurable_of_range_subset_isCompact`: a continuous function whose range
  lies in a compact set is strongly measurable.
* `IsLocalHomeomorph.stronglyMeasurable_comp_iff`: `g ∘ f` is strongly measurable exactly when
  `g` is, for a surjective local homeomorphism `f` out of a Lindelöf space.
* `MeasureTheory.StronglyMeasurable.indicator_prod`: extending an `mΩ`-strongly measurable
  function by zero outside a set `T` preserves strong measurability on `ι × Ω` when measurable
  rectangles `T ×ˢ A` are `mProd`-measurable.
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
theorem IsLocalHomeomorph.stronglyMeasurable_comp_iff {α β γ : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [LindelofSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] [TopologicalSpace γ] [PseudoMetrizableSpace γ]
    {f : α → β} (hf : IsLocalHomeomorph f) (hsurj : Function.Surjective f) {g : β → γ} :
    StronglyMeasurable (g ∘ f) ↔ StronglyMeasurable g := by
  borelize γ
  simp only [stronglyMeasurable_iff_measurable_separable, hf.measurable_comp_iff hsurj,
    hsurj.range_comp]

/-- Extending an `mΩ`-strongly measurable function `a` by zero outside a set `T` yields an
`mProd`-strongly measurable function on `ι × Ω`, provided every `mΩ`-measurable rectangle `T ×ˢ A`
is `mProd`-measurable. -/
theorem MeasureTheory.StronglyMeasurable.indicator_prod
    {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {mProd : MeasurableSpace (ι × Ω)}
    [TopologicalSpace E] [Zero E] {a : Ω → E} (ha : StronglyMeasurable[mΩ] a)
    {T : Set ι} (hT : ∀ ⦃A : Set Ω⦄, MeasurableSet[mΩ] A → MeasurableSet[mProd] (T ×ˢ A)) :
    StronglyMeasurable[mProd] (fun p : ι × Ω ↦ T.indicator (fun _ ↦ a p.2) p.1) := by
  classical
  let S : Set (ι × Ω) := T ×ˢ Set.univ
  have hS : MeasurableSet[mProd] S := hT MeasurableSet.univ
  have hproj : @Measurable S Ω inferInstance mΩ (fun p : S ↦ p.val.2) := by
    intro A hA
    refine ⟨T ×ˢ A, hT hA, ?_⟩
    ext p
    simp [S, p.property.1]
  simpa [S, Set.indicator_apply] using
    (ha.comp_measurable hproj).dite (stronglyMeasurable_const (b := (0 : E))) hS

end
