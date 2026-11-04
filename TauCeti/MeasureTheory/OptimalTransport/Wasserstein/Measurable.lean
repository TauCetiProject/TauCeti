/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Separable
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.LowerSemicontinuous
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.WeakConvergence

/-!
# Measurable Wasserstein distances, including the infinite exponent

We retain the Giry measurable structures on `WassersteinSpace` and `WassersteinComponent`.
For a Polish metric ground space, Wasserstein distance is jointly measurable in the two laws
for every exponent, including infinity. Consequently distances and metric balls in these spaces
are measurable for the inherited structure even when the Wasserstein topology is nonseparable.
This permits integration of distances between random laws without a finite-moment assumption
on their distribution.

The inherited sigma algebra is contained in the metric Borel sigma algebra. We do not claim
the reverse inclusion without separability: measurability of individual balls does not imply
measurability of their arbitrary unions. In particular no `OpensMeasurableSpace` instance is
installed at infinity. A random law measurable for the metric Borel structure is measurable for
the inherited structure, but the converse is not asserted.

For extended pseudometric ground spaces with Polish topology we also prove joint measurability
at finite exponents. No claim about the infinite-exponent weak lower semicontinuity on such
extended ground spaces is needed here.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer, 2009, Chapter 6.
* C. R. Givens and R. M. Shortt, *A class of Wasserstein metrics for probability distributions*,
  Michigan Math. J. 31 (1984), Proposition 1. The weak lower semicontinuity used here at infinity
  follows from their finite-exponent supremum formula.
-/

public section

open MeasureTheory MeasurableSpace Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

/-- On an extended pseudometric space with Polish topology, Wasserstein distance is jointly
Giry measurable at every finite exponent. -/
theorem measurable_wassersteinEDist_of_ne_top
    {X : Type*} [PseudoEMetricSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {p : ℝ≥0∞} (hp : p ≠ ∞) :
    Measurable fun q : ProbabilityMeasure X × ProbabilityMeasure X ↦
      wassersteinEDist p q.1.toMeasure q.2.toMeasure :=
  (lowerSemicontinuous_wassersteinEDist_of_ne_top hp).measurable

/-- On a Polish metric space, Wasserstein distance is jointly Giry measurable at every exponent,
including infinity. Infinite distances are retained. -/
theorem measurable_wassersteinEDist
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [CompleteSpace X] (p : ℝ≥0∞) :
    Measurable fun q : ProbabilityMeasure X × ProbabilityMeasure X ↦
      wassersteinEDist p q.1.toMeasure q.2.toMeasure :=
  (lowerSemicontinuous_wassersteinEDist p).measurable

namespace WassersteinSpace

section Comparison

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [StandardBorelSpace X] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The inherited Giry sigma algebra on `P_p(X)` is contained in its metric Borel sigma algebra,
including at infinity. This is only one direction of comparison. -/
theorem measurableSpace_le_borel :
    (inferInstance : MeasurableSpace (WassersteinSpace p X)) ≤ borel (WassersteinSpace p X) := by
  have hm : (inferInstance : MeasurableSpace (WassersteinSpace p X)) =
      .comap toProbabilityMeasure inferInstance := by
    refine le_antisymm (fun s hs ↦ ?_) measurable_toProbabilityMeasure.comap_le
    have h := @measurable_mk X p _ _ _ (.comap toProbabilityMeasure inferInstance) _
      (comap_measurable _) hasFiniteMoment
    simpa using h hs
  rw [hm]
  rw [BorelSpace.measurable_eq (α := ProbabilityMeasure X)]
  exact (continuous_toProbabilityMeasure (X := X) (p := p)).borel_measurable.comap_le

end Comparison

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Extended distance on `P_p(X)` is jointly measurable for the inherited Giry structure,
without assuming separability of its Wasserstein topology. -/
theorem measurable_edist :
    Measurable fun q : WassersteinSpace p X × WassersteinSpace p X ↦ edist q.1 q.2 := by
  simpa only [edist_def, Function.comp_def] using
    (measurable_wassersteinEDist (X := X) p).comp
      ((measurable_toProbabilityMeasure.comp measurable_fst).prodMk
        (measurable_toProbabilityMeasure.comp measurable_snd))

/-- Real distance on `P_p(X)` is jointly Giry measurable, including at infinity. -/
theorem measurable_dist :
    Measurable fun q : WassersteinSpace p X × WassersteinSpace p X ↦ dist q.1 q.2 := by
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using measurable_edist.ennreal_toReal

/-- A ball in `P_p(X)` is Giry measurable even at infinity. This does not assert measurability of
arbitrary unions of balls. -/
theorem measurableSet_ball (μ : WassersteinSpace p X) (r : ℝ) :
    MeasurableSet (Metric.ball μ r) :=
  measurableSet_lt (measurable_dist.comp (measurable_id.prodMk measurable_const)) measurable_const

/-- A closed ball in `P_p(X)` is Giry measurable even at infinity. -/
theorem measurableSet_closedBall (μ : WassersteinSpace p X) (r : ℝ) :
    MeasurableSet (Metric.closedBall μ r) :=
  measurableSet_le (measurable_dist.comp (measurable_id.prodMk measurable_const)) measurable_const

end WassersteinSpace

namespace WassersteinComponent

section Comparison

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [StandardBorelSpace X] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {μ₀ : ProbabilityMeasure X}

/-- On every anchored component the inherited Giry sigma algebra is contained in the metric
Borel sigma algebra, with no moment hypothesis on the anchor and including at infinity. -/
theorem measurableSpace_le_borel :
    (inferInstance : MeasurableSpace (WassersteinComponent p μ₀)) ≤
      borel (WassersteinComponent p μ₀) := by
  have hm : (inferInstance : MeasurableSpace (WassersteinComponent p μ₀)) =
      .comap toProbabilityMeasure inferInstance := by
    refine le_antisymm (fun s hs ↦ ?_) measurable_toProbabilityMeasure.comap_le
    have h := @measurable_mk X p _ _ μ₀ _ (.comap toProbabilityMeasure inferInstance) _
      (comap_measurable _) wassersteinEDist_anchor_ne_top
    simpa using h hs
  rw [hm]
  rw [BorelSpace.measurable_eq (α := ProbabilityMeasure X)]
  exact (continuous_toProbabilityMeasure (p := p) (μ₀ := μ₀)).borel_measurable.comap_le

end Comparison

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {μ₀ : ProbabilityMeasure X}

/-- Extended distance in an arbitrary anchored component is jointly Giry measurable, including
at infinity, without requiring a finite-moment anchor. -/
theorem measurable_edist :
    Measurable fun q : WassersteinComponent p μ₀ × WassersteinComponent p μ₀ ↦ edist q.1 q.2 := by
  simpa only [edist_def, Function.comp_def] using
    (measurable_wassersteinEDist (X := X) p).comp
      ((measurable_toProbabilityMeasure.comp measurable_fst).prodMk
        (measurable_toProbabilityMeasure.comp measurable_snd))

/-- Real distance in an arbitrary anchored component is jointly Giry measurable. -/
theorem measurable_dist :
    Measurable fun q : WassersteinComponent p μ₀ × WassersteinComponent p μ₀ ↦ dist q.1 q.2 := by
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using measurable_edist.ennreal_toReal

/-- A ball in an arbitrary anchored component is Giry measurable, including at infinity. -/
theorem measurableSet_ball (μ : WassersteinComponent p μ₀) (r : ℝ) :
    MeasurableSet (Metric.ball μ r) :=
  measurableSet_lt (measurable_dist.comp (measurable_id.prodMk measurable_const)) measurable_const

/-- A closed ball in an arbitrary anchored component is Giry measurable, including at infinity. -/
theorem measurableSet_closedBall (μ : WassersteinComponent p μ₀) (r : ℝ) :
    MeasurableSet (Metric.closedBall μ r) :=
  measurableSet_le (measurable_dist.comp (measurable_id.prodMk measurable_const)) measurable_const

end WassersteinComponent

end TauCeti
