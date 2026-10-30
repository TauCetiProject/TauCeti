/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Brenier
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Geodesic.Basic
import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Uniqueness of Wasserstein geodesics

Let `X` be a complete separable metric space and `1 < p < ∞`. Two laws `μ` and `ν` of finite
`p`-th moment can be joined by several geodesic segments of `P_p (X)`, for two independent
reasons. Two points of `X` joined by two geodesics give two geodesic segments between the Dirac
laws at these points. In the plane, the laws `(δ_(0,0) + δ_(1,1)) / 2` and `(δ_(1,0) + δ_(0,1)) / 2`
have two optimal couplings, matching each point to either of its two neighbours, and their linear
interpolations are two geodesic segments, although the plane is uniquely geodesic.

This file proves that these are the only obstructions. If the optimal coupling `π` of `μ` and `ν`
for the cost `d ^ p` is unique, and `π`-almost every pair of points is joined by only one geodesic
of `X`, then any two geodesic segments of `P_p (X)` from `μ` to `ν` agree on `[0, 1]`
(`TauCeti.WassersteinSpace.eqOn_of_isGeodesicSegment_of_ae_subsingleton`). By Lisini's
superposition principle each geodesic segment is the curve of laws of a dynamic plan concentrated
on geodesic paths whose endpoint law is an optimal coupling of `μ` and `ν`, hence is `π`
(`TauCeti.WassersteinSpace.exists_ae_mem_geodesicPaths_of_isGeodesicSegment`). When geodesics are
almost surely unique such a plan is determined by its endpoint law
(`MeasureTheory.Measure.eq_of_endpointLaw_eq_of_ae_subsingleton`), so the two geodesic segments
have the same laws at all times.

In a strictly convex separable Banach space `E` the only geodesic between two points is the affine
segment, so when the optimal coupling `π` is unique the geodesic segments of `P_p (E)` from `μ` to
`ν` are exactly the linear interpolation `t ↦ ((1 - t) • x + t • y)₊ π`. On a finite-dimensional
real inner product space, Brenier's theorem makes the quadratic optimal coupling out of an
absolutely continuous law `μ` unique, and the graph plan of the Brenier map `T`. Every geodesic
segment of `P₂ (E)` out of `μ` is then McCann's displacement interpolation
`t ↦ ((1 - t) • id + t • T)₊ μ`, and in particular there is only one.

## Main results

* `TauCeti.WassersteinSpace.eqOn_of_isGeodesicSegment_of_ae_subsingleton`: for `1 < p < ∞`, if
  the optimal coupling of `μ` and `ν` is unique and almost surely joins points by unique
  geodesics, then any two geodesic segments of `P_p (X)` from `μ` to `ν` agree on `[0, 1]`.
* `TauCeti.WassersteinSpace.isGeodesicSegment_iff_coe_eq_map_smul_add_smul`: on a strictly convex
  separable Banach space, if the optimal coupling `π` is unique, the geodesic segments of
  `P_p (E)` from `μ` to `ν` are exactly the linear interpolation of `π`.
* `TauCeti.WassersteinSpace.isGeodesicSegment_iff_coe_eq_map_smul_add_smul_of_absolutelyContinuous`:
  on a finite-dimensional real inner product space, the geodesic segments of `P₂ (E)` out of an
  absolutely continuous law are exactly McCann's displacement interpolation of a Brenier map.
* `TauCeti.WassersteinSpace.eqOn_of_isGeodesicSegment_of_absolutelyContinuous`: any two geodesic
  segments of `P₂ (E)` out of an absolutely continuous law with the same endpoint agree on
  `[0, 1]`.

## References

* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, Birkhäuser, 2nd ed. 2008, §7.2.
* R. J. McCann, *A convexity principle for interacting gases*, Adv. Math. 128 (1997), 153--179.
* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 7.
-/

public section

open MeasureTheory Set
open scoped ENNReal unitInterval

namespace TauCeti

namespace WassersteinSpace

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

section Polish

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- **Uniqueness of Wasserstein geodesics.** Let `X` be a complete separable metric space and
`1 < p < ∞`. Suppose that every optimal coupling of `μ` and `ν` for the cost `d ^ p` is `π`, and
that `π`-almost every pair of points of `X` is joined by at most one geodesic path. Then any two
geodesic segments of `P_p (X)` from `μ` to `ν` agree on `[0, 1]`. -/
theorem eqOn_of_isGeodesicSegment_of_ae_subsingleton (hp1 : 1 < p) (hp : p ≠ ∞)
    {μ ν : WassersteinSpace p X} {π : Measure (X × X)}
    (hπ : ∀ π', IsOptimalCoupling (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) π'
      ((μ : ProbabilityMeasure X) : Measure X) ((ν : ProbabilityMeasure X) : Measure X) → π' = π)
    (hgeo : ∀ᵐ z ∂π, {c | c ∈ geodesicPaths X ∧ c 0 = z.1 ∧ c 1 = z.2}.Subsingleton)
    {γ γ' : ℝ → WassersteinSpace p X} (h : IsGeodesicSegment γ μ ν)
    (h' : IsGeodesicSegment γ' μ ν) : EqOn γ γ' (Icc 0 1) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  -- Each geodesic segment is the curve of laws of a dynamic plan on geodesic paths whose endpoint
  -- law is an optimal coupling of `μ` and `ν`, hence is `π`.
  have hplan {c : ℝ → WassersteinSpace p X} (hc : IsGeodesicSegment c μ ν) :
      ∃ η : Measure C(I, X), IsProbabilityMeasure η ∧ (∀ᵐ γ ∂η, γ ∈ geodesicPaths X) ∧
        (∀ t : I, η.timeMarginal t = ((c t : ProbabilityMeasure X) : Measure X)) ∧
        η.endpointLaw = π := by
    obtain ⟨η, hηP, hη, hmarg, hopt⟩ :=
      exists_ae_mem_geodesicPaths_of_isGeodesicSegment hp1 hp hc
    have hcoup := η.isCoupling_map_timeMarginal 0 1
    rw [← Measure.endpointLaw_def, hmarg, hmarg, Icc.coe_zero, Icc.coe_one, hc.source,
      hc.target] at hcoup
    exact ⟨η, hηP, hη, hmarg,
      hπ _ ((isOptimalCoupling_edist_rpow_iff measurable_edist hp0 hp).2 ⟨hcoup, hopt⟩)⟩
  obtain ⟨η, hηP, hη, hmarg, hηπ⟩ := hplan h
  obtain ⟨η', -, hη', hmarg', hη'π⟩ := hplan h'
  -- The two plans have the same endpoint law `π`, so they are equal.
  have heq : η = η' := Measure.eq_of_endpointLaw_eq_of_ae_subsingleton hη hη'
    (hηπ.trans hη'π.symm) (hηπ ▸ hgeo)
  intro t ht
  refine ext (ProbabilityMeasure.toMeasure_injective ?_)
  rw [← hmarg ⟨t, ht⟩, ← hmarg' ⟨t, ht⟩, heq]

end Polish

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]
  [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- **The geodesics of `P_p (E)` under a unique optimal coupling.** Let `E` be a strictly convex
separable Banach space and `1 < p < ∞`. If every optimal coupling of `μ` and `ν` for the cost
`d ^ p` is `π`, then a curve `γ` is a geodesic segment of `P_p (E)` from `μ` to `ν` exactly when
for every `t ∈ [0, 1]` the law `γ t` is the law of `(1 - t) • x + t • y` under `π`. -/
theorem isGeodesicSegment_iff_coe_eq_map_smul_add_smul (hp1 : 1 < p) (hp : p ≠ ∞)
    {μ ν : WassersteinSpace p E} {π : Measure (E × E)}
    (hπ : ∀ π', IsOptimalCoupling (fun z : E × E ↦ edist z.1 z.2 ^ p.toReal) π'
      ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) → π' = π)
    {γ : ℝ → WassersteinSpace p E} :
    IsGeodesicSegment γ μ ν ↔ ∀ t ∈ Icc (0 : ℝ) 1,
      ((γ t : ProbabilityMeasure E) : Measure E) = π.map fun z ↦ (1 - t) • z.1 + t • z.2 := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  -- An optimal coupling exists, so it is `π`.
  obtain ⟨π₀, hπ₀, hπ₀opt⟩ := exists_isCoupling_eLpNorm_eq_wassersteinEDist hp0 hp _ _
    (exists_isCoupling_of_wassersteinEDist_ne_top (wassersteinEDist_ne_top measurable_edist μ ν))
  obtain rfl := hπ π₀ ((isOptimalCoupling_edist_rpow_iff measurable_edist hp0 hp).2
    ⟨hπ₀, hπ₀opt⟩)
  obtain ⟨γ₀, hγ₀, hγ₀t⟩ := exists_isGeodesicSegment_map_smul_add_smul hπ₀ hπ₀opt
  -- Geodesic paths of `E` are affine segments, so they are determined by their endpoints.
  have hgeo : ∀ᵐ z ∂π₀, {c | c ∈ geodesicPaths E ∧ c 0 = z.1 ∧ c 1 = z.2}.Subsingleton :=
    .of_forall fun z c ⟨hc, hc0, hc1⟩ c' ⟨hc', hc0', hc1'⟩ ↦ by
      rw [eq_segmentPath_of_mem_geodesicPaths hc, eq_segmentPath_of_mem_geodesicPaths hc', hc0,
        hc1, hc0', hc1']
  refine ⟨fun h t ht ↦ ?_, fun h ↦ hγ₀.congr fun t ht ↦ ?_⟩
  · rw [eqOn_of_isGeodesicSegment_of_ae_subsingleton hp1 hp hπ hgeo h hγ₀ ht, hγ₀t t ht]
  · exact ext (ProbabilityMeasure.toMeasure_injective ((h t ht).trans (hγ₀t t ht).symm))

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ : Measure E} [ρ.IsAddHaarMeasure]

/-- **Geodesics out of an absolutely continuous law are McCann's interpolation.** Let `E` be a
finite-dimensional real inner product space, let `μ` and `ν` be laws of finite second moment with
`μ` absolutely continuous with respect to an additive Haar measure, and let `T` be a Brenier map,
an optimal transport map from `μ` to `ν` for the cost `‖x - y‖ ^ 2 / 2`. Then a curve `γ` is a
geodesic segment of `P₂ (E)` from `μ` to `ν` exactly when for every `t ∈ [0, 1]` the law `γ t` is
the image of `μ` under `x ↦ (1 - t) • x + t • T x`. -/
theorem isGeodesicSegment_iff_coe_eq_map_smul_add_smul_of_absolutelyContinuous
    {μ ν : WassersteinSpace 2 E} (hμ : ((μ : ProbabilityMeasure E) : Measure E) ≪ ρ) {T : E → E}
    (hT : IsKantorovichOptimalTransportMap (fun z : E × E ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) T)
    {γ : ℝ → WassersteinSpace 2 E} :
    IsGeodesicSegment γ μ ν ↔ ∀ t ∈ Icc (0 : ℝ) 1, ((γ t : ProbabilityMeasure E) : Measure E) =
      ((μ : ProbabilityMeasure E) : Measure E).map fun x ↦ (1 - t) • x + t • T x := by
  have hc : Continuous fun z : E × E ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) :=
    continuous_ofReal_norm_sub_sq_div_two
  -- The graph plan of `T` is the unique optimal coupling, by Brenier's theorem.
  have hgraph := (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hT.toHasLaw
    hc.measurable.aemeasurable).1 hT
  have hπ : ∀ π', IsOptimalCoupling (fun z : E × E ↦ edist z.1 z.2 ^ (2 : ℝ≥0∞).toReal) π'
      ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) →
      π' = graphPlan T ((μ : ProbabilityMeasure E) : Measure E) := fun π' hπ' ↦ by
    rw [ENNReal.toReal_ofNat] at hπ'
    exact (isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two hπ').unique hμ hgraph
      (transportCost_norm_sub_sq_div_two_ne_top μ ν)
  rw [isGeodesicSegment_iff_coe_eq_map_smul_add_smul ENNReal.one_lt_two ENNReal.ofNat_ne_top hπ]
  refine forall₂_congr fun t _ ↦ ?_
  rw [graphPlan_def, AEMeasurable.map_map_of_aemeasurable (by fun_prop)
    (aemeasurable_id'.prodMk hT.aemeasurable), Function.comp_def]

/-- **Uniqueness of geodesics out of an absolutely continuous law.** On a finite-dimensional real
inner product space, if `μ` is absolutely continuous with respect to an additive Haar measure, any
two geodesic segments of `P₂ (E)` from `μ` to `ν` agree on `[0, 1]`. -/
theorem eqOn_of_isGeodesicSegment_of_absolutelyContinuous {μ ν : WassersteinSpace 2 E}
    (hμ : ((μ : ProbabilityMeasure E) : Measure E) ≪ ρ) {γ γ' : ℝ → WassersteinSpace 2 E}
    (h : IsGeodesicSegment γ μ ν) (h' : IsGeodesicSegment γ' μ ν) : EqOn γ γ' (Icc 0 1) := by
  obtain ⟨u, -, -, -, -, hT, -⟩ := exists_isKantorovichOptimalTransportMap_gradient hμ
    (transportCost_norm_sub_sq_div_two_ne_top μ ν)
  intro t ht
  refine ext (ProbabilityMeasure.toMeasure_injective ?_)
  rw [(isGeodesicSegment_iff_coe_eq_map_smul_add_smul_of_absolutelyContinuous hμ hT).1 h t ht,
    (isGeodesicSegment_iff_coe_eq_map_smul_add_smul_of_absolutelyContinuous hμ hT).1 h' t ht]

end InnerProduct

end WassersteinSpace

end TauCeti
