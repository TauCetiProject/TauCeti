/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Laws on spaces of continuous maps

A law on the path space `C(T, E)` whose time marginals at the times of a countable dense set are
concentrated on a closed set `F` is concentrated on the paths with values in `F` at all times.
When `F` is the range of a closed embedding `ι : X → E`, the law is therefore the image of a law
on `C(T, X)` under postcomposition with `ι`.

## Main results

* `TauCeti.ae_forall_apply_mem_of_dense`: a law on continuous paths whose time marginals at the
  times of a countable dense set are concentrated on a closed set is concentrated on the paths
  with values in that set.
* `TauCeti.isProbabilityMeasure_comap_postcomp`: such a law can be pulled back along a closed
  embedding of the path codomain.
-/

public section

open MeasureTheory Set Topology

namespace TauCeti

/-- A law on paths `C(T, E)` whose time marginals at the times of a countable dense set `D` are
concentrated on a closed set `F` is concentrated on the paths with values in `F` at all times. -/
theorem ae_forall_apply_mem_of_dense {T E : Type*} [TopologicalSpace T] [TopologicalSpace E]
    [MeasurableSpace C(T, E)] {η : Measure C(T, E)} {D : Set T} (hDc : D.Countable)
    (hDd : Dense D) {F : Set E} (hF : IsClosed F) (h : ∀ t ∈ D, ∀ᵐ γ ∂η, γ t ∈ F) :
    ∀ᵐ γ ∂η, ∀ t, γ t ∈ F := by
  have : Countable D := hDc.to_subtype
  filter_upwards [ae_all_iff.2 fun t : D ↦ h t t.2] with γ hγ t
  have hsub := (hF.preimage γ.continuous).closure_subset_iff.2 fun s hs ↦ hγ ⟨s, hs⟩
  exact hsub (hDd.closure_eq ▸ mem_univ t)

/-- Pulling a probability law on `C(T, E)` back along postcomposition by a closed embedding
`ι : X → E` gives a probability law whose pushforward is the original law, provided the original
law is concentrated on paths valued in the range of `ι` at the times of a countable dense set. -/
theorem isProbabilityMeasure_comap_postcomp {T X E : Type*} [TopologicalSpace T]
    [TopologicalSpace X] [TopologicalSpace E] [T2Space E] [PolishSpace C(T, X)] (ι : X → E)
    (hι : IsClosedEmbedding ι) (η : Measure C(T, E)) (hη : IsProbabilityMeasure η)
    {D : Set T} (hDc : D.Countable) (hDd : Dense D)
    (hD : ∀ t ∈ D, ∀ᵐ γ ∂η, γ t ∈ range ι) :
    IsProbabilityMeasure (η.comap (⟨ι, hι.continuous⟩ : C(X, E)).comp) ∧
      (η.comap (⟨ι, hι.continuous⟩ : C(X, E)).comp).map (⟨ι, hι.continuous⟩ : C(X, E)).comp =
        η := by
  let _ := hη
  set Φ : C(T, X) → C(T, E) := (⟨ι, hι.continuous⟩ : C(X, E)).comp
  have hΦ : MeasurableEmbedding Φ := (ContinuousMap.continuous_postcomp _).measurableEmbedding
    (ContinuousMap.postcomp_injective _ hι.injective)
  have hrange : ∀ᵐ γ ∂η, γ ∈ range Φ := by
    filter_upwards [ae_forall_apply_mem_of_dense hDc hDd hι.isClosed_range hD] with γ hall
    choose g hg using hall
    have hgc : Continuous g := hι.isEmbedding.continuous_iff.2 (by simpa [Function.comp_def, hg]
      using γ.continuous)
    exact ⟨⟨g, hgc⟩, ContinuousMap.ext hg⟩
  exact ⟨hΦ.isProbabilityMeasure_comap hrange, by
    rw [hΦ.map_comap, Measure.restrict_eq_self_of_ae_mem hrange]⟩

end TauCeti
