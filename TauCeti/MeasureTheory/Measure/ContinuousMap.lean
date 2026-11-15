/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import TauCeti.Topology.CompactOpen

/-!
# Laws on spaces of continuous maps

A law on the path space `C(T, E)` whose time marginals at the times of a countable dense set are
concentrated on a closed set `F` is concentrated on the paths with values in `F` at all times.
When `F` is the range of a closed embedding `g : C(X, E)`, the law is therefore the image of a law
on `C(T, X)` under postcomposition with `g`.

## Main results

* `TauCeti.ae_forall_apply_mem_of_dense`: a law on continuous paths whose time marginals at the
  times of a countable dense set are concentrated on a closed set is concentrated on the paths
  with values in that set.
* `TauCeti.ae_mem_range_postcomp_of_dense`: if the closed set is the range of a closed embedding
  `g`, the law is concentrated on the range of postcomposition with `g`.
* `TauCeti.map_comap_postcomp_of_dense`: such a law is the pushforward of its pullback along
  postcomposition with `g`.
* `TauCeti.isProbabilityMeasure_comap_postcomp_of_dense`: the pullback of such a probability law
  is a probability law.
-/

public section

open MeasureTheory Set Topology

namespace TauCeti

variable {T X E : Type*} [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace E]
  {D : Set T}

/-- A law on paths `C(T, E)` whose time marginals at the times of a countable dense set `D` are
concentrated on a closed set `F` is concentrated on the paths with values in `F` at all times. -/
theorem ae_forall_apply_mem_of_dense [MeasurableSpace C(T, E)] {η : Measure C(T, E)}
    (hDc : D.Countable) (hDd : Dense D) {F : Set E} (hF : IsClosed F)
    (h : ∀ t ∈ D, ∀ᵐ γ ∂η, γ t ∈ F) : ∀ᵐ γ ∂η, ∀ t, γ t ∈ F := by
  filter_upwards [(ae_ball_iff hDc).2 h] with γ hγ t
  exact hDd.denseRange_val.induction_on t (hF.preimage γ.continuous) fun s ↦ hγ s s.2

/-- A law on paths `C(T, E)` that is concentrated, at the times of a countable dense set `D`, on
the range of a closed embedding `g : C(X, E)` is concentrated on the paths obtained by
postcomposing a path in `X` with `g`. -/
theorem ae_mem_range_postcomp_of_dense [MeasurableSpace C(T, E)] {η : Measure C(T, E)}
    {g : C(X, E)} (hg : IsClosedEmbedding g) (hDc : D.Countable) (hDd : Dense D)
    (hD : ∀ t ∈ D, ∀ᵐ γ ∂η, γ t ∈ range g) :
    ∀ᵐ γ ∂η, γ ∈ range (g.comp : C(T, X) → C(T, E)) := by
  rw [ContinuousMap.range_postcomp g hg.isInducing]
  exact ae_forall_apply_mem_of_dense hDc hDd hg.isClosed_range hD

/-- A law on paths `C(T, E)` that is concentrated, at the times of a countable dense set `D`, on
the range of a closed embedding `g : C(X, E)` is the pushforward of its pullback along
postcomposition by `g`. -/
theorem map_comap_postcomp_of_dense {g : C(X, E)} (hg : IsClosedEmbedding g)
    (η : Measure C(T, E)) (hDc : D.Countable) (hDd : Dense D)
    (hD : ∀ t ∈ D, ∀ᵐ γ ∂η, γ t ∈ range g) :
    (η.comap (g.comp : C(T, X) → C(T, E))).map g.comp = η := by
  rw [(ContinuousMap.isClosedEmbedding_postcomp g hg).measurableEmbedding.map_comap,
    Measure.restrict_eq_self_of_ae_mem (ae_mem_range_postcomp_of_dense hg hDc hDd hD)]

/-- Pulling a probability law on `C(T, E)` back along postcomposition by a closed embedding
`g : C(X, E)` gives a probability law, provided the original law is concentrated on the range of
`g` at the times of a countable dense set. -/
theorem isProbabilityMeasure_comap_postcomp_of_dense {g : C(X, E)} (hg : IsClosedEmbedding g)
    (η : Measure C(T, E)) [IsProbabilityMeasure η] (hDc : D.Countable) (hDd : Dense D)
    (hD : ∀ t ∈ D, ∀ᵐ γ ∂η, γ t ∈ range g) :
    IsProbabilityMeasure (η.comap (g.comp : C(T, X) → C(T, E))) :=
  (ContinuousMap.isClosedEmbedding_postcomp g hg).measurableEmbedding.isProbabilityMeasure_comap
    (ae_mem_range_postcomp_of_dense hg hDc hDd hD)

end TauCeti
