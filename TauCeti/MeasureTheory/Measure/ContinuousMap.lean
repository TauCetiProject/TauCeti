/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import TauCeti.Topology.CompactOpen
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Laws on spaces of continuous maps

A finite measure on the path space `C(T, E)` is determined by its finite-dimensional evaluation
marginals when `T` is second-countable and locally compact and `E` is second-countable and regular,
since the Borel sigma-algebra on `C(T, E)` is pulled back from the product sigma-algebra on
`T → E`.

A law on the path space `C(T, E)` whose time marginals at the times of a countable dense set are
concentrated on a closed set `F` is concentrated on the paths with values in `F` at all times.
When `F` is the range of a closed embedding `g : C(X, E)`, the law is therefore the image of a law
on `C(T, X)` under postcomposition with `g`.

## Main results

* `TauCeti.measure_continuousMap_eq_of_forall_finset_map_restrict_eq`: a finite measure on `C(T, E)`
  is uniquely determined by its finite-dimensional evaluation marginals.
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

/-- Two measures on `C(T, E)`, with `μ` finite, that have the same finite-dimensional evaluation
marginals are equal. Finiteness of `ν` is not assumed. -/
theorem measure_continuousMap_eq_of_forall_finset_map_restrict_eq
    [SecondCountableTopology T] [LocallyCompactSpace T]
    [SecondCountableTopology E] [RegularSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ ν : Measure C(T, E)} [IsFiniteMeasure μ]
    (h : ∀ I : Finset T, μ.map (fun γ : C(T, E) ↦ I.restrict (γ ·)) =
      ν.map (fun γ : C(T, E) ↦ I.restrict (γ ·))) :
    μ = ν := by
  have hcoe : Measurable ((⇑) : C(T, E) → T → E) :=
    measurable_pi_iff.mpr fun t ↦ ContinuousMap.measurable_eval t
  have hP : IsProjectiveLimit (μ.map ((⇑) : C(T, E) → T → E))
      (fun I : Finset T ↦ μ.map (fun γ : C(T, E) ↦ I.restrict (γ ·))) := fun I ↦ by
    rw [Measure.map_map (Finset.measurable_restrict I) hcoe, Function.comp_def]
  have hQ : IsProjectiveLimit (ν.map ((⇑) : C(T, E) → T → E))
      (fun I : Finset T ↦ μ.map (fun γ : C(T, E) ↦ I.restrict (γ ·))) := fun I ↦ by
    rw [Measure.map_map (Finset.measurable_restrict I) hcoe, Function.comp_def]
    exact (h I).symm
  have hmap : μ.map ((⇑) : C(T, E) → T → E) = ν.map ((⇑) : C(T, E) → T → E) :=
    hP.unique hQ
  have hcomap : ContinuousMap.measurableSpace (X := T) (Y := E) =
      MeasurableSpace.comap ((⇑) : C(T, E) → T → E) MeasurableSpace.pi := by
    rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval, MeasurableSpace.pi,
      MeasurableSpace.comap_iSup]
    refine iSup_congr fun t ↦ ?_
    rw [MeasurableSpace.comap_comp, Function.comp_def]
  ext s hs
  obtain ⟨u, hu, rfl⟩ := MeasurableSpace.measurableSet_comap.mp (hcomap ▸ hs)
  rw [← Measure.map_apply hcoe hu, hmap, Measure.map_apply hcoe hu]

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
