/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.MetricMeasure.Basic
public import TauCeti.MeasureTheory.OptimalTransport.DynamicPlan
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
public import TauCeti.Topology.MetricSpace.Nonbranching

/-!
# Essentially nonbranching metric-measure spaces

A metric-measure space is *essentially nonbranching* when every quadratic optimal dynamic plan
between two finite-second-moment laws absolutely continuous with respect to the reference measure
is concentrated on one nonbranching family of geodesics. The condition is weaker than requiring
all geodesics of the carrier to be nonbranching: only paths used by the relevant optimal plans
are constrained.

This file defines essential nonbranching using the quadratic optimal dynamic plans of
`TauCeti.MeasureTheory.OptimalTransport.DynamicPlan`. The condition is inherited when the reference
measure is replaced by a measure absolutely continuous with respect to it. If the full family of
geodesics is nonbranching, every reference measure is essentially nonbranching; in particular this
holds on strictly convex separable Banach spaces.

## Main definitions and results

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
