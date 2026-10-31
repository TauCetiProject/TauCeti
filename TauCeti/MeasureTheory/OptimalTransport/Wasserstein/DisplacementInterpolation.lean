/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Geodesic.Basic

/-!
# Displacement interpolation as a relation

`TauCeti.IsDisplacementInterpolation p μ` says that the curve of probability laws `μ`, indexed
by the unit interval, is induced by an optimal dynamic plan concentrated on constant-speed
geodesics. It does not select an optimal coupling or a geodesic between each pair of endpoints.
In particular different presentations are allowed, and different interpolations can join the
same endpoint laws.

For finite endpoint distance and `1 ≤ p`, such a curve has the constant-speed Wasserstein
distance formula. For `1 < p < ∞`, this relation characterizes geodesic segments in `P_p(X)`.
At the endpoints `p = 1` and `p = ∞` only the forward implication is asserted. Uniqueness of
interpolation follows from uniqueness of the endpoint optimizer together with almost-everywhere
uniqueness of the ground geodesics; neither condition alone is substituted for both.

On a separable Banach space the affine interpolation of an optimal coupling satisfies this
relation. The graph-plan specialization identifies map-induced affine interpolation with the
same relation, without assuming that the transport map is everywhere measurable.

## References

* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, §7.2.
* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 7.
-/

public section

open MeasureTheory Set
open scoped ENNReal unitInterval

namespace TauCeti

variable {p : ℝ≥0∞}

section Definition

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- A curve of probability laws is a displacement interpolation if it is the curve of time
marginals of a probability dynamic plan on constant-speed geodesics with optimal endpoint law.
The optimality uses `eLpNorm`, so it includes the infinite exponent and infinite values. -/
def IsDisplacementInterpolation (p : ℝ≥0∞) (μ : I → ProbabilityMeasure X) : Prop :=
  ∃ η : Measure C(I, X), IsProbabilityMeasure η ∧
    (∀ᵐ c ∂η, c ∈ geodesicPaths X) ∧
    (∀ t, η.timeMarginal t = (μ t : Measure X)) ∧
    eLpNorm (fun z : X × X ↦ edist z.1 z.2) p η.endpointLaw =
      wassersteinEDist p (μ 0 : Measure X) (μ 1 : Measure X)

/-- The dynamic-plan characterization of displacement interpolation. -/
theorem isDisplacementInterpolation_iff {μ : I → ProbabilityMeasure X} :
    IsDisplacementInterpolation p μ ↔
      ∃ η : Measure C(I, X), IsProbabilityMeasure η ∧
        (∀ᵐ c ∂η, c ∈ geodesicPaths X) ∧
        (∀ t, η.timeMarginal t = (μ t : Measure X)) ∧
        eLpNorm (fun z : X × X ↦ edist z.1 z.2) p η.endpointLaw =
          wassersteinEDist p (μ 0 : Measure X) (μ 1 : Measure X) :=
  Iff.rfl

end Definition

section Distance

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [StandardBorelSpace X] {μ : I → ProbabilityMeasure X}

/-- A displacement interpolation at finite endpoint distance has constant Wasserstein speed,
including at the exponents one and infinity. -/
theorem IsDisplacementInterpolation.wassersteinEDist_eq (h : IsDisplacementInterpolation p μ)
    (hp : 1 ≤ p) (hfin : wassersteinEDist p (μ 0 : Measure X) (μ 1 : Measure X) ≠ ∞)
    (s t : I) :
    wassersteinEDist p (μ s : Measure X) (μ t : Measure X) =
      edist s t * wassersteinEDist p (μ 0 : Measure X) (μ 1 : Measure X) := by
  obtain ⟨η, hηP, hη, hmarg, hopt⟩ := h
  simpa only [hmarg] using wassersteinEDist_timeMarginal_eq hη hp
    (by simpa only [hmarg] using hopt) (by simpa only [hmarg] using hfin) s t

end Distance

section Polish

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- Probability laws at finite Wasserstein distance on a Polish geodesic space admit a
displacement interpolation. No moment hypothesis on either endpoint is required. -/
theorem exists_isDisplacementInterpolation [IsGeodesicSpace X] (hp : 1 ≤ p)
    (μ₀ μ₁ : ProbabilityMeasure X)
    (hfin : wassersteinEDist p (μ₀ : Measure X) (μ₁ : Measure X) ≠ ∞) :
    ∃ μ : I → ProbabilityMeasure X, IsDisplacementInterpolation p μ ∧ μ 0 = μ₀ ∧ μ 1 = μ₁ := by
  obtain ⟨η, hηF, hη, h0, h1, hopt, -⟩ :=
    exists_ae_mem_geodesicPaths_wassersteinEDist_timeMarginal_eq hp _ _ hfin
  have : IsProbabilityMeasure η := by
    rw [← Measure.isProbabilityMeasure_map_iff (ContinuousMap.measurable_eval 0).aemeasurable,
      ← Measure.timeMarginal_def, h0]
    infer_instance
  refine ⟨fun t ↦ (η.timeMarginal t).toProbabilityMeasure, ?_, ?_, ?_⟩
  · exact ⟨η, inferInstance, hη, fun _ ↦ by simp, by simpa only
      [Measure.coe_toProbabilityMeasure, h0, h1] using hopt⟩
  · exact ProbabilityMeasure.toMeasure_injective (by simpa using h0)
  · exact ProbabilityMeasure.toMeasure_injective (by simpa using h1)

/-- Displacement interpolation is independent of presentation when the endpoint optimizer is
unique and almost every pair under that optimizer has at most one ground geodesic.
This applies also to the infinite exponent, unlike the converse characterization of geodesics. -/
theorem IsDisplacementInterpolation.eq_of_ae_subsingleton
    {μ ν : I → ProbabilityMeasure X} (hμ : IsDisplacementInterpolation p μ)
    (hν : IsDisplacementInterpolation p ν) (h0 : ν 0 = μ 0) (h1 : ν 1 = μ 1)
    {π : Measure (X × X)}
    (hπ : ∀ π', IsCoupling π' (μ 0 : Measure X) (μ 1 : Measure X) →
      eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π' =
        wassersteinEDist p (μ 0 : Measure X) (μ 1 : Measure X) → π' = π)
    (hgeo : ∀ᵐ z ∂π, {c | c ∈ geodesicPaths X ∧ c 0 = z.1 ∧ c 1 = z.2}.Subsingleton) :
    μ = ν := by
  obtain ⟨η, hηP, hη, hmarg, hopt⟩ := hμ
  obtain ⟨η', hη'P, hη', hmarg', hopt'⟩ := hν
  have hηπ : η.endpointLaw = π := hπ _ (by
    simpa only [← Measure.endpointLaw_def, hmarg] using η.isCoupling_map_timeMarginal 0 1) hopt
  have hη'π : η'.endpointLaw = π := hπ _ (by
    simpa only [← Measure.endpointLaw_def, hmarg', h0, h1] using
      η'.isCoupling_map_timeMarginal 0 1) (by simpa only [h0, h1] using hopt')
  have heq := Measure.eq_of_endpointLaw_eq_of_ae_subsingleton hη hη'
    (hηπ.trans hη'π.symm) (hηπ ▸ hgeo)
  funext t
  exact ProbabilityMeasure.toMeasure_injective ((hmarg t).symm.trans (heq ▸ hmarg' t))

/-- At strictly intermediate exponents, displacement interpolation characterizes geodesic
segments of the finite-moment Wasserstein space. No geodesicity of the ground space is assumed. -/
theorem WassersteinSpace.isGeodesicSegment_iff_isDisplacementInterpolation [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) {γ : ℝ → WassersteinSpace p X} :
    IsGeodesicSegment γ (γ 0) (γ 1) ↔
      IsDisplacementInterpolation p (fun t : I ↦ (γ t : ProbabilityMeasure X)) := by
  rw [isDisplacementInterpolation_iff]
  simpa only [Icc.coe_zero, Icc.coe_one] using
    WassersteinSpace.isGeodesicSegment_iff_exists_ae_mem_geodesicPaths hp1 hp (γ := γ)

end Polish

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  {μ : I → ProbabilityMeasure E} {π : Measure (E × E)}

/-- Affine interpolation of an optimal coupling is a displacement interpolation. The formula
specifies the curve, but no choice of optimizer is built into the relation. Completeness and
strict convexity of the norm are not needed for this construction. -/
theorem isDisplacementInterpolation_of_map_smul_add_smul
    (hπ : IsCoupling π (μ 0 : Measure E) (μ 1 : Measure E))
    (hopt : eLpNorm (fun z : E × E ↦ edist z.1 z.2) p π =
      wassersteinEDist p (μ 0 : Measure E) (μ 1 : Measure E))
    (hmarg : ∀ t : I, (μ t : Measure E) =
      π.map fun z ↦ (1 - (t : ℝ)) • z.1 + (t : ℝ) • z.2) :
    IsDisplacementInterpolation p μ := by
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hseg : Measurable (segmentPath : E × E → C(I, E)) := segmentPath.continuous.measurable
  have hend : (π.map segmentPath).endpointLaw = π := by
    rw [Measure.endpointLaw_def, Measure.map_map ContinuousMap.measurable_endpoints hseg]
    convert Measure.map_id
    ext z <;> simp
  refine ⟨π.map segmentPath, inferInstance, ?_, ?_, by rwa [hend]⟩
  · exact (ae_map_iff hseg.aemeasurable isClosed_geodesicPaths.measurableSet).2
      (.of_forall segmentPath_mem_geodesicPaths)
  · intro t
    rw [Measure.timeMarginal_map _ hseg, hmarg]
    congr 1
    ext z
    simp [AffineMap.lineMap_apply_module]

/-- The affine curve induced by an optimal transport map is a displacement interpolation.
Transport-map feasibility is `HasLaw`, so an a.e.-measurable representative suffices. -/
theorem _root_.ProbabilityTheory.HasLaw.isDisplacementInterpolation_smul_add_smul {T : E → E}
    (hT : ProbabilityTheory.HasLaw T (μ 1 : Measure E) (μ 0 : Measure E))
    (hopt : eLpNorm (fun z : E × E ↦ edist z.1 z.2) p (graphPlan T (μ 0 : Measure E)) =
      wassersteinEDist p (μ 0 : Measure E) (μ 1 : Measure E))
    (hmarg : ∀ t : I, (μ t : Measure E) =
      (μ 0 : Measure E).map fun x ↦ (1 - (t : ℝ)) • x + (t : ℝ) • T x) :
    IsDisplacementInterpolation p μ := by
  refine isDisplacementInterpolation_of_map_smul_add_smul (isCoupling_graphPlan hT) hopt ?_
  intro t
  rw [hmarg, map_graphPlan hT.aemeasurable (by fun_prop)]

end Affine

end TauCeti
