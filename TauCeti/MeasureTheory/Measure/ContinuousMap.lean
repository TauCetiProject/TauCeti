/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import TauCeti.Topology.CompactOpen
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Laws on spaces of continuous maps

A law on the path space `C(T, E)` whose time marginals at the times of a countable dense set are
concentrated on a closed set `F` is concentrated on the paths with values in `F` at all times.
When `F` is the range of a closed embedding `g : C(X, E)`, the law is therefore the image of a law
on `C(T, X)` under postcomposition with `g`.

When `T` is second-countable and locally compact and `E` is second-countable and regular
with its Borel measurable structure, finite Borel laws on `C(T, E)`, or on the fixed-basepoint
subspace `BasedMap`, are uniquely determined by their finite-dimensional laws.

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
* `TauCeti.continuousMap_measure_ext_of_forall_finset_map_restrict_eq`: finite-dimensional
  laws determine a finite Borel law on continuous maps.
* `TauCeti.basedMap_measure_ext_of_forall_finset_map_restrict_eq`: the corresponding
  uniqueness criterion for based continuous maps.

## References

* Mathlib's `IsProjectiveLimit.unique`: uniqueness of finite-dimensional projective limits.
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

/-- A Borel law on continuous paths agrees with a finite law if their finite-dimensional
laws agree. The empty marginal already forces equality of total masses. The topology on
the path space is compact-open, not the pointwise topology. -/
theorem continuousMap_measure_ext_of_forall_finset_map_restrict_eq
    [SecondCountableTopology T] [LocallyCompactSpace T]
    [SecondCountableTopology E] [RegularSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ ν : Measure C(T, E)} [IsFiniteMeasure ν]
    (h : ∀ I : Finset T,
      μ.map (fun γ : C(T, E) ↦ I.restrict (γ : T → E)) =
        ν.map (fun γ : C(T, E) ↦ I.restrict (γ : T → E))) : μ = ν := by
  have hcoe := ContinuousMap.measurable_coeFun (X := T) (Y := E)
  have hμ := ProbabilityTheory.isProjectiveLimit_map (P := μ) hcoe.aemeasurable
  have hν := ProbabilityTheory.isProjectiveLimit_map (P := ν) hcoe.aemeasurable
  simp_rw [h] at hμ
  have heq := hμ.unique hν
  have hm : ContinuousMap.measurableSpace (X := T) (Y := E) =
      (inferInstance : MeasurableSpace (T → E)).comap (fun γ : C(T, E) ↦ (γ : T → E)) := by
    rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
    simp [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def]
  ext A hA
  rw [hm, MeasurableSpace.measurableSet_comap] at hA
  obtain ⟨B, hB, hBA⟩ := hA
  rw [← hBA, ← Measure.map_apply hcoe hB, ← Measure.map_apply hcoe hB]
  exact congrArg (fun ρ ↦ ρ B) heq

/-- A law on based continuous paths agrees with a finite law if their finite-dimensional
laws agree, including the empty set of observation times. -/
theorem basedMap_measure_ext_of_forall_finset_map_restrict_eq
    [SecondCountableTopology T] [LocallyCompactSpace T]
    [SecondCountableTopology E] [RegularSpace E]
    [MeasurableSpace E] [BorelSpace E] {t₀ : T} {x₀ : E}
    {ν ρ : Measure (BasedMap T E t₀ x₀)} [IsFiniteMeasure ρ]
    (h : ∀ I : Finset T,
      ν.map (fun γ ↦ I.restrict (γ.1 : T → E)) =
        ρ.map (fun γ ↦ I.restrict (γ.1 : T → E))) : ν = ρ := by
  have heq : ν.map Subtype.val = ρ.map Subtype.val := by
    apply continuousMap_measure_ext_of_forall_finset_map_restrict_eq
    intro I
    simpa only [Measure.map_map (ContinuousMap.measurable_finsetRestrict I) measurable_subtype_coe,
      Function.comp_def] using h I
  ext A hA
  obtain ⟨B, hB, rfl⟩ := hA
  rw [← Measure.map_apply measurable_subtype_coe hB,
    ← Measure.map_apply measurable_subtype_coe hB, heq]

end TauCeti
