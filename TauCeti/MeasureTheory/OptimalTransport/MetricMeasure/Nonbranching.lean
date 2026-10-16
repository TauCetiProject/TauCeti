/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.MetricMeasure.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Geodesic
public import TauCeti.Topology.MetricSpace.Nonbranching

/-!
# Essentially nonbranching metric-measure spaces

A metric-measure space is *essentially nonbranching* when every quadratic optimal dynamic plan
between two finite-second-moment laws absolutely continuous with respect to the reference measure
is concentrated on one nonbranching family of geodesics. The condition is weaker than requiring
all geodesics of the carrier to be nonbranching: only paths used by the relevant optimal plans
are constrained.

This file packages quadratic optimal dynamic plans using the existing endpoint-law and optimal-
coupling APIs, then defines essential nonbranching. The condition is inherited when the reference
measure is replaced by a measure absolutely continuous with respect to it. If the full family of
geodesics is nonbranching, every reference measure is essentially nonbranching; in particular this
holds on strictly convex separable Banach spaces.

## Main definitions and results

* `MeasureTheory.Measure.IsQuadraticOptimalDynamicPlan`: a dynamic plan concentrated on geodesics
  whose endpoint law is a quadratic optimal coupling;
* `TauCeti.MetricMeasureSpace.EssentiallyNonbranching`: essential nonbranching relative to the
  reference measure;
* `TauCeti.MetricMeasureSpace.EssentiallyNonbranching.of_absolutelyContinuous`: inheritance by an
  absolutely continuous reference measure;
* `TauCeti.MetricMeasureSpace.essentiallyNonbranching_of_isNonbranchingGeodesics`: the geometric
  nonbranching criterion;
* `TauCeti.MetricMeasureSpace.essentiallyNonbranching_of_strictConvexSpace`: strictly convex real
  normed spaces are essentially nonbranching for every boundedly finite reference measure.

## References

* F. Cavalletti and A. Mondino, *Optimal maps in essentially non-branching spaces*, Commun.
  Contemp. Math. 19 (2017), 1750007, Definition 2.1.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal unitInterval

namespace MeasureTheory.Measure

open TauCeti

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- A **quadratic optimal dynamic plan** from `μ₀` to `μ₁`: a measure on path space concentrated
on constant-speed geodesics whose endpoint law is an optimal coupling for the squared-distance
cost. The optimal-coupling field forces the plan to have total mass one when the endpoints are
probability laws. -/
structure IsQuadraticOptimalDynamicPlan (η : Measure C(I, X))
    (μ₀ μ₁ : ProbabilityMeasure X) : Prop where
  /-- Almost every path of the dynamic plan is a constant-speed geodesic. -/
  ae_mem_geodesicPaths : ∀ᵐ γ ∂η, γ ∈ geodesicPaths X
  /-- The joint law of the two endpoints is a quadratic optimal coupling. -/
  endpointLaw_isOptimalCoupling :
    IsOptimalCoupling (fun z : X × X ↦ edist z.1 z.2 ^ (2 : ℝ)) η.endpointLaw
      (μ₀ : Measure X) (μ₁ : Measure X)

/-- The endpoint law of a quadratic optimal dynamic plan couples its prescribed endpoints. -/
theorem IsQuadraticOptimalDynamicPlan.endpointLaw_isCoupling {η : Measure C(I, X)}
    {μ₀ μ₁ : ProbabilityMeasure X} (hη : η.IsQuadraticOptimalDynamicPlan μ₀ μ₁) :
    TauCeti.IsCoupling η.endpointLaw (μ₀ : Measure X) (μ₁ : Measure X) :=
  hη.endpointLaw_isOptimalCoupling.toIsCoupling

variable [BorelSpace X]

/-- The time-zero marginal of a quadratic optimal dynamic plan is its source law. -/
theorem IsQuadraticOptimalDynamicPlan.timeMarginal_zero {η : Measure C(I, X)}
    {μ₀ μ₁ : ProbabilityMeasure X} (hη : η.IsQuadraticOptimalDynamicPlan μ₀ μ₁) :
    η.timeMarginal 0 = (μ₀ : Measure X) := by
  rw [← fst_endpointLaw, hη.endpointLaw_isCoupling.fst_eq]

/-- The time-one marginal of a quadratic optimal dynamic plan is its target law. -/
theorem IsQuadraticOptimalDynamicPlan.timeMarginal_one {η : Measure C(I, X)}
    {μ₀ μ₁ : ProbabilityMeasure X} (hη : η.IsQuadraticOptimalDynamicPlan μ₀ μ₁) :
    η.timeMarginal 1 = (μ₁ : Measure X) := by
  rw [← snd_endpointLaw, hη.endpointLaw_isCoupling.snd_eq]

/-- A quadratic optimal dynamic plan between probability laws is itself a probability measure on
path space. -/
theorem IsQuadraticOptimalDynamicPlan.isProbabilityMeasure {η : Measure C(I, X)}
    {μ₀ μ₁ : ProbabilityMeasure X} (hη : η.IsQuadraticOptimalDynamicPlan μ₀ μ₁) :
    IsProbabilityMeasure η := by
  refine ⟨?_⟩
  have hend : η.endpointLaw univ = 1 := by
    rw [← hη.endpointLaw_isCoupling.measure_univ_left, measure_univ]
  rw [endpointLaw_apply η MeasurableSet.univ] at hend
  simpa using hend

end MeasureTheory.Measure

namespace TauCeti.MetricMeasureSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [BorelSpace X] {M N : MetricMeasureSpace X}

/-- A metric-measure space is **essentially nonbranching** if every quadratic optimal dynamic plan
between two laws in `P₂(X)` that are absolutely continuous with respect to the reference measure
is concentrated on a nonbranching family of geodesics. -/
def EssentiallyNonbranching (M : MetricMeasureSpace X) : Prop :=
  ∀ (μ₀ μ₁ : WassersteinSpace 2 X),
    ((μ₀ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
    ((μ₁ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
    ∀ ⦃η : Measure C(I, X)⦄,
      η.IsQuadraticOptimalDynamicPlan (μ₀ : ProbabilityMeasure X) (μ₁ : ProbabilityMeasure X) →
      ∃ Γ : Set C(I, X), Γ.IsNonbranchingGeodesics ∧ ∀ᵐ γ ∂η, γ ∈ Γ

/-- The defining characterization of essential nonbranching. -/
theorem essentiallyNonbranching_iff : M.EssentiallyNonbranching ↔
    ∀ (μ₀ μ₁ : WassersteinSpace 2 X),
      ((μ₀ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
      ((μ₁ : ProbabilityMeasure X) : Measure X) ≪ M.reference →
      ∀ ⦃η : Measure C(I, X)⦄,
        η.IsQuadraticOptimalDynamicPlan (μ₀ : ProbabilityMeasure X) (μ₁ : ProbabilityMeasure X) →
        ∃ Γ : Set C(I, X), Γ.IsNonbranchingGeodesics ∧ ∀ᵐ γ ∂η, γ ∈ Γ :=
  Iff.rfl

/-- Essential nonbranching is inherited when the reference measure is replaced by a measure
absolutely continuous with respect to the old reference measure. -/
theorem EssentiallyNonbranching.of_absolutelyContinuous (hM : M.EssentiallyNonbranching)
    (hNM : N.reference ≪ M.reference) : N.EssentiallyNonbranching := by
  intro μ₀ μ₁ hμ₀ hμ₁ η hη
  exact hM μ₀ μ₁ (hμ₀.trans hNM) (hμ₁.trans hNM) hη

/-- If every geodesic of the carrier belongs to one nonbranching family, every boundedly finite
reference measure on that carrier is essentially nonbranching. -/
theorem essentiallyNonbranching_of_isNonbranchingGeodesics (M : MetricMeasureSpace X)
    (hX : (geodesicPaths X).IsNonbranchingGeodesics) : M.EssentiallyNonbranching := by
  intro μ₀ μ₁ hμ₀ hμ₁ η hη
  exact ⟨geodesicPaths X, hX, hη.ae_mem_geodesicPaths⟩

section StrictConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]
  [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- Every boundedly finite reference measure on a strictly convex separable real Banach space is
essentially nonbranching. This includes Euclidean spaces with Lebesgue measure. -/
theorem essentiallyNonbranching_of_strictConvexSpace (M : MetricMeasureSpace E) :
    M.EssentiallyNonbranching :=
  essentiallyNonbranching_of_isNonbranchingGeodesics M isNonbranchingGeodesics_geodesicPaths

end StrictConvex

end TauCeti.MetricMeasureSpace
