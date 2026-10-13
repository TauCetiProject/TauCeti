/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import TauCeti.MeasureTheory.MeasurableSpace.Uniformization
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
public import TauCeti.Topology.MetricSpace.GeodesicPath
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# Dynamic plans concentrated on geodesics

A *dynamic plan* on a metric space `X` is a measure `η` on the path space `C(I, X)`. Its law at
time `t`, `η.timeMarginal t`, is the pushforward of `η` along the evaluation at `t`, and its
*endpoint law* `η.endpointLaw` is the pushforward along
`γ ↦ (γ 0, γ 1)`, a measure on `X × X` whose marginals are the laws at times `0` and `1`. When
`η` is concentrated on the geodesic paths `TauCeti.geodesicPaths X`, the laws at times `s` and
`t` are coupled by the law of `(γ s, γ t)`, and each coupled pair is at distance `|s - t|` times the
distance between the endpoints of its geodesic. This gives the displacement bound
`W_p (η_s, η_t) ≤ |s - t| * ‖d‖_{Lᵖ(π)}` for every exponent `p`, where `π` is the endpoint law.

Conversely, on a Polish metric space every law `π` of pairs of points almost all of which are
joined by a geodesic (for instance, any law on a geodesic space) is the endpoint law of a dynamic
plan concentrated on geodesics. The relation between a pair of points and the geodesic
paths joining them is closed (`TauCeti.isClosed_setOf_mem_geodesicPaths_endpoints`), hence
analytic in the Polish space `(X × X) × C(I, X)`, so the Jankov–von Neumann uniformization theorem
chooses, measurably in the pair of endpoints and for `π`-almost every pair, a geodesic joining them.
The pushforward of `π` along this choice is the required dynamic plan. No global Borel choice of
geodesics is claimed: the choice depends on `π` and is only defined `π`-almost everywhere.

Applied to an optimal coupling `π` of `μ` and `ν` on a Polish geodesic space, for a finite nonzero
exponent `p`, the laws at times `0 ≤ t ≤ 1` of this dynamic
plan interpolate between `μ` and `ν`, with `W_p (η_s, η_t) ≤ |s - t| * W_p (μ, ν)`.

## Main definitions

* `MeasureTheory.Measure.timeMarginal η t`: the law at time `t` of a dynamic plan `η`.
* `MeasureTheory.Measure.endpointLaw η`: the joint law of the two endpoints of a dynamic plan `η`.

A dynamic plan is a plain `Measure C(I, X)`, so these declarations live in the namespace of
Mathlib's `MeasureTheory.Measure`, where dot notation such as `η.timeMarginal t` finds them.

## Main results

* `MeasureTheory.Measure.exists_measurable_ae_mem_geodesicPaths`: on a Polish metric space,
  relative to an s-finite law of pairs of points almost all of which are joined by a geodesic, a
  geodesic joining almost every pair can be chosen measurably in the pair.
* `MeasureTheory.Measure.exists_ae_mem_geodesicPaths_endpointLaw_eq`: every such law of pairs of
  points is the endpoint law of a dynamic plan concentrated on geodesics.
* `TauCeti.eLpNorm_edist_map_eq`: for a dynamic plan concentrated on geodesics, the `Lᵖ`
  displacement of its joint law at times `s` and `t` is `|s - t|` times that of its endpoint law.
* `TauCeti.wassersteinEDist_timeMarginal_le`: the displacement bound between the laws at two times
  of a dynamic plan concentrated on geodesics.
* `TauCeti.exists_ae_mem_geodesicPaths_wassersteinEDist_timeMarginal_le`: on a Polish geodesic space
  and for a finite nonzero exponent `p`, two finite measures with a coupling are the laws at times
  `0` and `1` of a dynamic plan concentrated on geodesics whose laws at times `s` and `t` are
  within `|s - t| * W_p (μ, ν)` of each other.

## References

* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, Birkhäuser, 2nd ed. 2008, §7.2.
* S. Lisini, *Characterization of absolutely continuous curves in Wasserstein spaces*, Calc. Var.
  Partial Differential Equations 28 (2007), 85--120.
* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 7.
-/

public section

open MeasureTheory Set
open scoped ENNReal unitInterval

namespace MeasureTheory.Measure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- The law at time `t` of a dynamic plan `η` on the path space `C(I, X)`: the pushforward of `η`
along the evaluation `γ ↦ γ t`. -/
noncomputable def timeMarginal (η : Measure C(I, X)) (t : I) : Measure X :=
  η.map fun γ ↦ γ t

/-- The endpoint law of a dynamic plan `η` on the path space `C(I, X)`: the pushforward of `η`
along `γ ↦ (γ 0, γ 1)`, the joint law of the initial and final points of a path. -/
noncomputable def endpointLaw (η : Measure C(I, X)) : Measure (X × X) :=
  η.map fun γ ↦ (γ 0, γ 1)

/-- The law at time `t` is the pushforward along the evaluation at `t`. -/
theorem timeMarginal_def (η : Measure C(I, X)) (t : I) :
    timeMarginal η t = η.map fun γ ↦ γ t :=
  (rfl)

/-- The endpoint law is the pushforward along the pair of endpoints. -/
theorem endpointLaw_def (η : Measure C(I, X)) :
    endpointLaw η = η.map fun γ ↦ (γ 0, γ 1) :=
  (rfl)

/-- A finite dynamic plan has finite laws at every time. -/
instance isFiniteMeasure_timeMarginal (η : Measure C(I, X)) [IsFiniteMeasure η] (t : I) :
    IsFiniteMeasure (timeMarginal η t) := by
  rw [timeMarginal_def]
  infer_instance

/-- A finite dynamic plan has a finite endpoint law. -/
instance isFiniteMeasure_endpointLaw (η : Measure C(I, X)) [IsFiniteMeasure η] :
    IsFiniteMeasure (endpointLaw η) := by
  rw [endpointLaw_def]
  infer_instance

/-- A probability dynamic plan has probability laws at every time. -/
instance isProbabilityMeasure_timeMarginal (η : Measure C(I, X)) [IsProbabilityMeasure η]
    (t : I) : IsProbabilityMeasure (timeMarginal η t) := by
  rw [timeMarginal_def]
  infer_instance

/-- A probability dynamic plan has a probability endpoint law. -/
instance isProbabilityMeasure_endpointLaw (η : Measure C(I, X)) [IsProbabilityMeasure η] :
    IsProbabilityMeasure (endpointLaw η) := by
  rw [endpointLaw_def]
  infer_instance

variable [BorelSpace X]

/-- The value of the law at time `t` on a measurable set `s` is the `η`-measure of the paths
lying in `s` at time `t`. -/
theorem timeMarginal_apply (η : Measure C(I, X)) (t : I) {s : Set X} (hs : MeasurableSet s) :
    timeMarginal η t s = η {γ | γ t ∈ s} :=
  Measure.map_apply (ContinuousMap.measurable_eval t) hs

/-- The value of the endpoint law on a measurable set `s` is the `η`-measure of the paths whose
pair of endpoints lies in `s`. -/
theorem endpointLaw_apply (η : Measure C(I, X)) {s : Set (X × X)} (hs : MeasurableSet s) :
    endpointLaw η s = η {γ | (γ 0, γ 1) ∈ s} :=
  Measure.map_apply
    ((ContinuousMap.measurable_eval 0).prodMk (ContinuousMap.measurable_eval 1)) hs

/-- The first marginal of the endpoint law is the law at time `0`. -/
@[simp]
theorem fst_endpointLaw (η : Measure C(I, X)) : (endpointLaw η).fst = timeMarginal η 0 :=
  Measure.fst_map_prodMk (ContinuousMap.measurable_eval 0) (ContinuousMap.measurable_eval 1)

/-- The second marginal of the endpoint law is the law at time `1`. -/
@[simp]
theorem snd_endpointLaw (η : Measure C(I, X)) : (endpointLaw η).snd = timeMarginal η 1 :=
  Measure.snd_map_prodMk (ContinuousMap.measurable_eval 0) (ContinuousMap.measurable_eval 1)

/-- The joint law at times `s` and `t` of a dynamic plan couples its laws at those two times. -/
theorem isCoupling_map_timeMarginal (η : Measure C(I, X)) (s t : I) :
    TauCeti.IsCoupling (η.map fun γ ↦ (γ s, γ t)) (timeMarginal η s) (timeMarginal η t) :=
  TauCeti.isCoupling_map_prodMk_of_measurePreserving
    ⟨ContinuousMap.measurable_eval s, (timeMarginal_def η s).symm⟩
    ⟨ContinuousMap.measurable_eval t, (timeMarginal_def η t).symm⟩

section Polish

open TauCeti (geodesicPaths isClosed_geodesicPaths isClosed_setOf_mem_geodesicPaths_endpoints)

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- **Measurable choice of geodesics.** On a Polish metric space, relative to an s-finite law `π`
of pairs of points almost all of which are joined by a geodesic path, there is a Borel map
choosing, for `π`-almost every pair `z`, a geodesic path from `z.1` to `z.2`. -/
theorem exists_measurable_ae_mem_geodesicPaths (π : Measure (X × X)) [SFinite π]
    (hπ : ∀ᵐ z ∂π, ∃ γ ∈ geodesicPaths X, γ 0 = z.1 ∧ γ 1 = z.2) :
    ∃ G : X × X → C(I, X), Measurable G ∧
      ∀ᵐ z ∂π, G z ∈ geodesicPaths X ∧ G z 0 = z.1 ∧ G z 1 = z.2 := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact ⟨fun z ↦ isEmptyElim z.1, measurable_of_empty _, .of_forall fun z ↦ isEmptyElim z.1⟩
  have : Nonempty C(I, X) := ⟨ContinuousMap.const I x₀⟩
  let R : Set ((X × X) × C(I, X)) := {q | q.2 ∈ geodesicPaths X ∧ (q.2 0, q.2 1) = q.1}
  obtain ⟨G, hG, hGR⟩ :=
    isClosed_setOf_mem_geodesicPaths_endpoints.analyticSet.exists_measurable_ae_uniformization
      (R := R) π
  refine ⟨G, hG, ?_⟩
  filter_upwards [hGR, hπ] with z hz ⟨γ, hγ, hγ0, hγ1⟩
  obtain ⟨hGz, hGe⟩ := hz ⟨(z, γ), ⟨hγ, by rw [hγ0, hγ1]⟩, rfl⟩
  exact ⟨hGz, congr_arg Prod.fst hGe, congr_arg Prod.snd hGe⟩

/-- **Lifting a law of pairs to geodesics.** On a Polish metric space, every s-finite law `π` of
pairs of points almost all of which are joined by a geodesic path is the endpoint law of an
s-finite dynamic plan concentrated on geodesic paths. -/
theorem exists_ae_mem_geodesicPaths_endpointLaw_eq (π : Measure (X × X)) [SFinite π]
    (hπ : ∀ᵐ z ∂π, ∃ γ ∈ geodesicPaths X, γ 0 = z.1 ∧ γ 1 = z.2) :
    ∃ η : Measure C(I, X), SFinite η ∧ (∀ᵐ γ ∂η, γ ∈ geodesicPaths X) ∧
      endpointLaw η = π := by
  obtain ⟨G, hG, hGπ⟩ := exists_measurable_ae_mem_geodesicPaths π hπ
  have he : Measurable fun γ : C(I, X) ↦ (γ 0, γ 1) :=
    (ContinuousMap.measurable_eval 0).prodMk (ContinuousMap.measurable_eval 1)
  refine ⟨π.map G, inferInstance,
    (ae_map_iff hG.aemeasurable isClosed_geodesicPaths.measurableSet).2 ?_, ?_⟩
  · filter_upwards [hGπ] with z hz using hz.1
  · rw [endpointLaw_def, Measure.map_map he hG]
    conv_rhs => rw [← Measure.map_id (μ := π)]
    refine Measure.map_congr ?_
    filter_upwards [hGπ] with z hz
    simp [hz.2.1, hz.2.2]

end Polish

end MeasureTheory.Measure

namespace TauCeti

section Displacement

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

/-- **The displacement along geodesics.** For a dynamic plan `η` concentrated on geodesic paths,
the `Lᵖ` size of the ground distance under the joint law at times `s` and `t` is `|s - t|` times
its `Lᵖ` size under the endpoint law. -/
theorem eLpNorm_edist_map_eq {η : Measure C(I, X)} (hη : ∀ᵐ γ ∂η, γ ∈ geodesicPaths X)
    (p : ℝ≥0∞) (s t : I) :
    eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (η.map fun γ ↦ (γ s, γ t)) =
      edist s t * eLpNorm (fun z : X × X ↦ edist z.1 z.2) p η.endpointLaw := by
  have hd : Measurable fun z : X × X ↦ edist z.1 z.2 := measurable_edist
  have hev (r : I) : Measurable fun γ : C(I, X) ↦ γ r := ContinuousMap.measurable_eval r
  rw [Measure.endpointLaw_def,
    eLpNorm_map_measure hd.aestronglyMeasurable ((hev s).prodMk (hev t)).aemeasurable,
    eLpNorm_map_measure hd.aestronglyMeasurable ((hev 0).prodMk (hev 1)).aemeasurable]
  -- Pass to the real distance, which the geodesic condition scales by the constant `dist s t`.
  have hreal (u v : I) : eLpNorm ((fun z : X × X ↦ edist z.1 z.2) ∘ fun γ ↦ (γ u, γ v)) p η =
      eLpNorm (fun γ : C(I, X) ↦ dist (γ u) (γ v)) p η :=
    eLpNorm_congr_enorm_ae (hd.comp ((hev u).prodMk (hev v))).aestronglyMeasurable
      ((hev u).dist (hev v)).aestronglyMeasurable
      (.of_forall fun γ ↦ by simp [edist_dist, Real.enorm_of_nonneg])
  rw [hreal, hreal, edist_dist, ← Real.enorm_of_nonneg dist_nonneg, ← eLpNorm_const_smul]
  refine eLpNorm_congr_ae ?_
  filter_upwards [hη] with γ hγ
  rw [Pi.smul_apply, smul_eq_mul, mem_geodesicPaths_iff.1 hγ s t, Subtype.dist_eq, Real.dist_eq]

/-- **The displacement bound along geodesics.** For a dynamic plan `η` concentrated on geodesic
paths, the `p`-Wasserstein distance between its laws at times `s` and `t` is at most
`|s - t|` times the `Lᵖ` size of the ground distance under its endpoint law. -/
theorem wassersteinEDist_timeMarginal_le {η : Measure C(I, X)}
    (hη : ∀ᵐ γ ∂η, γ ∈ geodesicPaths X) (p : ℝ≥0∞) (s t : I) :
    wassersteinEDist p (η.timeMarginal s) (η.timeMarginal t) ≤
      edist s t * eLpNorm (fun z : X × X ↦ edist z.1 z.2) p η.endpointLaw :=
  (wassersteinEDist_le (η.isCoupling_map_timeMarginal s t) p).trans_eq
    (eLpNorm_edist_map_eq hη p s t)

end Displacement

section Polish

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- **Geodesic interpolation of an optimal coupling.** On a Polish geodesic space, for a finite
nonzero exponent `p`, two finite measures `μ` and `ν` admitting a coupling are the laws at times
`0` and `1` of a finite dynamic plan `η` concentrated on geodesic paths whose laws at any two times
`s` and `t` are within `|s - t| * W_p (μ, ν)` of each other. The dynamic plan lifts an optimal
coupling of `μ` and `ν`. -/
theorem exists_ae_mem_geodesicPaths_wassersteinEDist_timeMarginal_le [IsGeodesicSpace X] {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (μ ν : Measure X) [IsFiniteMeasure μ]
    (hcoup : ∃ π, IsCoupling π μ ν) :
    ∃ η : Measure C(I, X), IsFiniteMeasure η ∧ (∀ᵐ γ ∂η, γ ∈ geodesicPaths X) ∧
      η.timeMarginal 0 = μ ∧ η.timeMarginal 1 = ν ∧
      ∀ s t : I, wassersteinEDist p (η.timeMarginal s) (η.timeMarginal t) ≤
        edist s t * wassersteinEDist p μ ν := by
  obtain ⟨π, hπ, hπopt⟩ := exists_isCoupling_eLpNorm_eq_wassersteinEDist hp0 hp μ ν hcoup
  have : IsFiniteMeasure π := hπ.isFiniteMeasure
  obtain ⟨η, -, hη, hηπ⟩ := π.exists_ae_mem_geodesicPaths_endpointLaw_eq
    (.of_forall fun z ↦ IsGeodesicSpace.exists_mem_geodesicPaths z.1 z.2)
  have : IsFiniteMeasure (η.map fun γ ↦ (γ 0, γ 1)) := by
    rw [← Measure.endpointLaw_def, hηπ]
    infer_instance
  refine ⟨η, Measure.isFiniteMeasure_of_map (μ := η) (f := fun γ ↦ (γ 0, γ 1))
    ((ContinuousMap.measurable_eval 0).prodMk (ContinuousMap.measurable_eval 1)).aemeasurable,
    hη, ?_, ?_, fun s t ↦ ?_⟩
  · rw [← Measure.fst_endpointLaw, hηπ, hπ.fst_eq]
  · rw [← Measure.snd_endpointLaw, hηπ, hπ.snd_eq]
  · simpa only [hηπ, hπopt] using wassersteinEDist_timeMarginal_le hη p s t

end Polish

end TauCeti
