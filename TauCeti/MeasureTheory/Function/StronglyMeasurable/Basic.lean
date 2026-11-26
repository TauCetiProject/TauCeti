/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Strong measurability and finite-support approximation

A continuous function from a space with the Borel `σ`-algebra to a pseudo-metrizable space is
strongly measurable as soon as its range lies in a compact set, since the range is then separable.
No countability assumption on the domain is needed.

Strong measurability also descends along a surjective local homeomorphism out of a Lindelöf
space: a function on its codomain is strongly measurable exactly when its composite with the local
homeomorphism is.

Finite-support approximation transfers between strongly measurable functions whenever
convergence of the constant zero sequence to the first implies convergence to the second.

## Main results

* `Continuous.stronglyMeasurable_of_range_subset_isCompact`: a continuous function whose range
  lies in a compact set is strongly measurable.
* `IsLocalHomeomorph.stronglyMeasurable_comp_iff`: `g ∘ f` is strongly measurable exactly when
  `g` is, for a surjective local homeomorphism `f` out of a Lindelöf space.
* `MeasureTheory.FinStronglyMeasurable.of_tendsto_const_zero`: transfer finite-support
  approximation using convergence of constant zero sequences.
-/

public section

open MeasureTheory TopologicalSpace

open scoped Topology

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

namespace MeasureTheory

open Filter Set

/-- A strongly measurable function is finitely strongly measurable if convergence of the
constant zero sequence to a finitely strongly measurable function implies convergence to it.
This transfers finite-support approximation without any separation assumption on the spaces. -/
theorem FinStronglyMeasurable.of_tendsto_const_zero {α X G : Type*} [MeasurableSpace α]
    {μ : Measure α} [TopologicalSpace X] [TopologicalSpace G] [Zero X] [Zero G]
    {u : α → X} (hu : FinStronglyMeasurable u μ) {v : α → G}
    (hv : StronglyMeasurable v)
    (hzero : ∀ t, Tendsto (fun _ : ℕ ↦ (0 : X)) atTop (𝓝 (u t)) →
      Tendsto (fun _ : ℕ ↦ (0 : G)) atTop (𝓝 (v t))) :
    FinStronglyMeasurable v μ := by
  classical
  -- Outside the union of the approximants’ supports, zero converges to the input.
  let s := ⋃ n, Function.support (hu.approx n)
  have hs : MeasurableSet s := .iUnion fun n ↦ (hu.approx n).measurableSet_support
  have hμs : SigmaFinite (μ.restrict s) := by
    refine ⟨⟨⟨fun n ↦ sᶜ ∪ Function.support (hu.approx n), fun _ ↦ trivial,
      fun n ↦ ?_, ?_⟩⟩⟩
    · rw [Measure.restrict_apply' hs, Set.union_inter_distrib_right,
        Set.compl_inter_self s, Set.empty_union]
      exact (measure_mono Set.inter_subset_left).trans_lt (hu.fin_support_approx n)
    · rw [← Set.union_iUnion]
      exact Set.compl_union_self s
  have hv' := (hv.indicator hs).finStronglyMeasurable_of_set_sigmaFinite hs
    (fun t ht ↦ Set.indicator_of_notMem ht _) hμs
  refine ⟨fun n ↦ (hv'.approx n).restrict s, fun n ↦ ?_, fun t ↦ ?_⟩
  · refine (measure_mono ?_).trans_lt (hv'.fin_support_approx n)
    intro t ht
    by_cases hts : t ∈ s
    · simpa [SimpleFunc.restrict_apply _ hs, hts, Function.mem_support] using ht
    · simp [SimpleFunc.restrict_apply _ hs, hts, Function.mem_support] at ht
  · by_cases hts : t ∈ s
    · simpa [SimpleFunc.restrict_apply _ hs, hts] using hv'.tendsto_approx t
    · have hut : ∀ n, hu.approx n t = 0 := by
        intro n
        by_contra hn
        exact hts (Set.mem_iUnion.2 ⟨n, hn⟩)
      have ht := hzero t (by simpa only [hut] using hu.tendsto_approx t)
      simpa [SimpleFunc.restrict_apply _ hs, hts] using ht

end MeasureTheory

end
