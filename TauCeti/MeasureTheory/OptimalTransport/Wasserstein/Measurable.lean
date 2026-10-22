/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Borel
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.LowerSemicontinuous

/-!
# Measurable distances without Wasserstein separability

The measurable structure of `WassersteinSpace p X` is inherited from `ProbabilityMeasure X`.
For `1 ≤ p` and a Polish metric ground space, all Wasserstein distances are jointly measurable
for this structure, even when `p = ∞` and the Wasserstein space is not separable. In particular,
its balls and closed balls are measurable. These facts allow integration of distances between random
laws and between measurable families of kernel section laws at the infinite-exponent endpoint.

The inherited σ-algebra is contained in the Wasserstein Borel σ-algebra. We do not identify them
at `p = ∞`, nor assert that every Wasserstein-open set is inherited-measurable. Measurability of
balls alone does not imply that assertion in a nonseparable space.

The distance measurability argument passes through finite first moments: every finite `p`-moment
law with `1 ≤ p` has finite first moment, and `P₁(X)` has its inherited Borel structure. Weak lower
semicontinuity makes every `W_q`, including `W_∞`, measurable on `P₁(X) × P₁(X)`.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 6, for the distinction
  between finite-exponent and infinite-exponent Wasserstein topologies.
-/

public section

noncomputable section

open MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

namespace TauCeti

namespace WassersteinSpace

section StandardBorel

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [StandardBorelSpace X] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The inherited σ-algebra on `P_p(X)` is contained in its Wasserstein Borel σ-algebra,
including at `p = ∞`. This inclusion does not require completeness of the ground space. -/
theorem measurableSpace_le_borel :
    (inferInstance : MeasurableSpace (WassersteinSpace p X)) ≤
      borel (WassersteinSpace p X) := by
  let : MeasurableSpace (WassersteinSpace p X) := borel (WassersteinSpace p X)
  let : BorelSpace (WassersteinSpace p X) := ⟨rfl⟩
  have h := @measurable_mk X p _ _ _ (borel (WassersteinSpace p X)) _
    (continuous_toProbabilityMeasure.measurable_probabilityMeasure) hasFiniteMoment
  intro s hs
  simpa only [mk_coe, preimage_id'] using h hs

end StandardBorel

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every Wasserstein distance `W_q` is jointly measurable on finite `p`-moment laws, for
`1 ≤ p` and arbitrary `q`. Both exponents may be infinite. Measurability refers to the inherited
σ-algebra, not to an assumed Borel structure for the `W_p` topology. -/
@[fun_prop]
theorem measurable_wassersteinEDist (q : ℝ≥0∞) :
    Measurable fun z : WassersteinSpace p X × WassersteinSpace p X ↦
      wassersteinEDist q (z.1 : Measure X) (z.2 : Measure X) := by
  have hfirst (μ : WassersteinSpace p X) : HasFiniteMoment 1 (μ : Measure X) := by
    obtain ⟨x, hx⟩ := hasFiniteMoment_def.mp μ.hasFiniteMoment
    exact hasFiniteMoment_def.mpr ⟨x, hx.mono_exponent Fact.out⟩
  let f : WassersteinSpace p X → WassersteinSpace 1 X :=
    fun μ ↦ mk (μ : ProbabilityMeasure X) (hfirst μ)
  have hf : Measurable f := measurable_mk measurable_toProbabilityMeasure hfirst
  have hlsc : LowerSemicontinuous fun z : WassersteinSpace 1 X × WassersteinSpace 1 X ↦
      wassersteinEDist q (z.1 : Measure X) (z.2 : Measure X) :=
    (lowerSemicontinuous_wassersteinEDist q).comp
      (continuous_toProbabilityMeasure.prodMap continuous_toProbabilityMeasure)
  have : BorelSpace (WassersteinSpace 1 X) := borelSpace (by norm_num)
  have : SeparableSpace (WassersteinSpace 1 X) := separableSpace (by norm_num)
  simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, f, coe_mk] using
    hlsc.measurable.comp (hf.prodMap hf)

/-- The extended metric of `P_p(X)` is jointly measurable for the inherited σ-algebra, including
at `p = ∞`, without separability of `P_p(X)`. -/
@[fun_prop]
theorem measurable_edist :
    Measurable fun z : WassersteinSpace p X × WassersteinSpace p X ↦ edist z.1 z.2 := by
  simpa only [edist_def] using measurable_wassersteinEDist (X := X) (p := p) p

/-- The real metric of `P_p(X)` is jointly measurable for the inherited σ-algebra, including
at `p = ∞`. -/
@[fun_prop]
theorem measurable_dist :
    Measurable fun z : WassersteinSpace p X × WassersteinSpace p X ↦ dist z.1 z.2 := by
  simpa only [dist_edist] using (measurable_edist (X := X) (p := p)).ennreal_toReal

/-- Open metric balls in `P_p(X)` are inherited-measurable even at `p = ∞`. -/
@[measurability]
theorem measurableSet_ball (μ : WassersteinSpace p X) (r : ℝ) :
    MeasurableSet (Metric.ball μ r) := by
  exact measurableSet_lt
    ((measurable_dist (X := X) (p := p)).comp (measurable_id.prodMk measurable_const))
    measurable_const

/-- Closed metric balls in `P_p(X)` are inherited-measurable even at `p = ∞`. -/
@[measurability]
theorem measurableSet_closedBall (μ : WassersteinSpace p X) (r : ℝ) :
    MeasurableSet (Metric.closedBall μ r) := by
  exact measurableSet_le
    ((measurable_dist (X := X) (p := p)).comp (measurable_id.prodMk measurable_const))
    measurable_const

/-- Extended metric balls in `P_p(X)` are inherited-measurable even at `p = ∞`. -/
@[measurability]
theorem measurableSet_eball (μ : WassersteinSpace p X) (r : ℝ≥0∞) :
    MeasurableSet (Metric.eball μ r) := by
  exact measurableSet_lt
    ((measurable_edist (X := X) (p := p)).comp (measurable_id.prodMk measurable_const))
    measurable_const

end WassersteinSpace

end TauCeti
