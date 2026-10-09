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
time `t` is the pushforward `η.map (fun γ ↦ γ t)` along the evaluation at `t`, and its *endpoint
law* is the pushforward `η.map (fun γ ↦ (γ 0, γ 1))`, a measure on `X × X`. When `η` is
concentrated on the geodesic paths `TauCeti.geodesicPaths X`, the laws at times `s` and `t` are
coupled by the law of `(γ s, γ t)`, and each coupled pair is at distance `|s - t|` times the
distance between the endpoints of its geodesic. This gives the displacement bound
`W_p (η_s, η_t) ≤ |s - t| * ‖d‖_{Lᵖ(π)}` for every exponent `p`, where `π` is the endpoint law.

Conversely, on a Polish geodesic space every law `π` of pairs of points is the endpoint law of a
dynamic plan concentrated on geodesics. The relation between a pair of points and the geodesic
paths joining them is closed (`TauCeti.isClosed_setOf_mem_geodesicPaths_endpoints`), hence
analytic in the Polish space `(X × X) × C(I, X)`, so the Jankov–von Neumann uniformization theorem
chooses, measurably in the pair of endpoints and for `π`-almost every pair, a geodesic joining them.
The pushforward of `π` along this choice is the required dynamic plan. No global Borel choice of
geodesics is claimed: the choice depends on `π` and is only defined `π`-almost everywhere.

Applied to an optimal coupling `π` of `μ` and `ν`, the laws at times `0 ≤ t ≤ 1` of this dynamic
plan interpolate between `μ` and `ν`, with `W_p (η_s, η_t) ≤ |s - t| * W_p (μ, ν)`.

## Main results

* `TauCeti.exists_measurable_ae_mem_geodesicPaths`: on a Polish geodesic space, relative to an
  s-finite law of pairs of points, a geodesic joining almost every pair can be chosen measurably in
  the pair.
* `TauCeti.exists_ae_mem_geodesicPaths_map_eq`: every s-finite law of pairs of points is the
  endpoint law of a dynamic plan concentrated on geodesics.
* `TauCeti.wassersteinEDist_map_eval_le`: the displacement bound between the laws at two times of
  a dynamic plan concentrated on geodesics.
* `TauCeti.exists_ae_mem_geodesicPaths_wassersteinEDist_map_eval_le`: two finite measures with a
  coupling are the laws at times `0` and `1` of a dynamic plan concentrated on geodesics whose laws
  at times `s` and `t` are within `|s - t| * W_p (μ, ν)` of each other.

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

namespace TauCeti

section Displacement

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

/-- **The displacement bound along geodesics.** For a dynamic plan `η` concentrated on geodesic
paths, the `p`-Wasserstein distance between its laws at times `s` and `t` is at most
`|s - t|` times the `Lᵖ` size of the ground distance under its endpoint law. -/
theorem wassersteinEDist_map_eval_le {η : Measure C(I, X)}
    (hη : ∀ᵐ γ ∂η, γ ∈ geodesicPaths X) (p : ℝ≥0∞) (s t : I) :
    wassersteinEDist p (η.map fun γ ↦ γ s) (η.map fun γ ↦ γ t) ≤
      edist s t * eLpNorm (fun z : X × X ↦ edist z.1 z.2) p (η.map fun γ ↦ (γ 0, γ 1)) := by
  have hd : Measurable fun z : X × X ↦ edist z.1 z.2 := measurable_edist
  have hev (r : I) : Measurable fun γ : C(I, X) ↦ γ r := ContinuousMap.measurable_eval r
  have hcoup : IsCoupling (η.map fun γ ↦ (γ s, γ t)) (η.map fun γ ↦ γ s) (η.map fun γ ↦ γ t) :=
    ⟨Measure.fst_map_prodMk (hev s) (hev t), Measure.snd_map_prodMk (hev s) (hev t)⟩
  refine (wassersteinEDist_le hcoup p).trans ?_
  rw [eLpNorm_map_measure hd.aestronglyMeasurable ((hev s).prodMk (hev t)).aemeasurable,
    eLpNorm_map_measure hd.aestronglyMeasurable ((hev 0).prodMk (hev 1)).aemeasurable,
    edist_nndist, ← smul_eq_mul, ← ENNReal.smul_def]
  refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    (hd.comp ((hev s).prodMk (hev t))).aestronglyMeasurable ?_ p
  filter_upwards [hη] with γ hγ
  simp only [Function.comp_apply, enorm_eq_self, edist_nndist, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_mul, coe_nndist]
  rw [mem_geodesicPaths_iff.1 hγ s t, Subtype.dist_eq, Real.dist_eq]

end Displacement

section Polish

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [IsGeodesicSpace X]

/-- **Measurable choice of geodesics.** On a Polish geodesic space, relative to an s-finite law `π`
of pairs of points, there is a Borel map choosing, for `π`-almost every pair `z`, a geodesic path
from `z.1` to `z.2`. -/
theorem exists_measurable_ae_mem_geodesicPaths (π : Measure (X × X)) [SFinite π] :
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
  filter_upwards [hGR] with z hz
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := IsGeodesicSpace.exists_mem_geodesicPaths z.1 z.2
  obtain ⟨hGz, hGe⟩ := hz ⟨(z, γ), ⟨hγ, by rw [hγ0, hγ1]⟩, rfl⟩
  exact ⟨hGz, congr_arg Prod.fst hGe, congr_arg Prod.snd hGe⟩

/-- **Lifting a law of pairs to geodesics.** On a Polish geodesic space, every s-finite law `π` of
pairs of points is the endpoint law of a dynamic plan concentrated on geodesic paths. -/
theorem exists_ae_mem_geodesicPaths_map_eq (π : Measure (X × X)) [SFinite π] :
    ∃ η : Measure C(I, X), (∀ᵐ γ ∂η, γ ∈ geodesicPaths X) ∧ η.map (fun γ ↦ (γ 0, γ 1)) = π := by
  obtain ⟨G, hG, hGπ⟩ := exists_measurable_ae_mem_geodesicPaths π
  have he : Measurable fun γ : C(I, X) ↦ (γ 0, γ 1) :=
    (ContinuousMap.measurable_eval 0).prodMk (ContinuousMap.measurable_eval 1)
  refine ⟨π.map G, (ae_map_iff hG.aemeasurable isClosed_geodesicPaths.measurableSet).2 ?_, ?_⟩
  · filter_upwards [hGπ] with z hz using hz.1
  · rw [Measure.map_map he hG]
    conv_rhs => rw [← Measure.map_id (μ := π)]
    refine Measure.map_congr ?_
    filter_upwards [hGπ] with z hz
    simp [hz.2.1, hz.2.2]

/-- **Geodesic interpolation of an optimal coupling.** On a Polish geodesic space, for a finite
nonzero exponent `p`, two finite measures `μ` and `ν` admitting a coupling are the laws at times
`0` and `1` of a dynamic plan `η` concentrated on geodesic paths whose laws at any two times `s` and
`t` are within `|s - t| * W_p (μ, ν)` of each other. The dynamic plan lifts an optimal coupling of
`μ` and `ν`. -/
theorem exists_ae_mem_geodesicPaths_wassersteinEDist_map_eval_le {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (μ ν : Measure X) [IsFiniteMeasure μ] (hcoup : ∃ π, IsCoupling π μ ν) :
    ∃ η : Measure C(I, X), (∀ᵐ γ ∂η, γ ∈ geodesicPaths X) ∧ η.map (fun γ ↦ γ 0) = μ ∧
      η.map (fun γ ↦ γ 1) = ν ∧
      ∀ s t : I, wassersteinEDist p (η.map fun γ ↦ γ s) (η.map fun γ ↦ γ t) ≤
        edist s t * wassersteinEDist p μ ν := by
  obtain ⟨π, hπ, hπopt⟩ := exists_isCoupling_eLpNorm_eq_wassersteinEDist hp0 hp μ ν hcoup
  have : IsFiniteMeasure π := hπ.isFiniteMeasure
  obtain ⟨η, hη, hηπ⟩ := exists_ae_mem_geodesicPaths_map_eq π
  have hev (r : I) : Measurable fun γ : C(I, X) ↦ γ r := ContinuousMap.measurable_eval r
  refine ⟨η, hη, ?_, ?_, fun s t ↦ ?_⟩
  · rw [← Measure.fst_map_prodMk (hev 0) (hev 1), hηπ, hπ.fst_eq]
  · rw [← Measure.snd_map_prodMk (hev 0) (hev 1), hηπ, hπ.snd_eq]
  · simpa only [hηπ, hπopt] using wassersteinEDist_map_eval_le hη p s t

end Polish

end TauCeti
