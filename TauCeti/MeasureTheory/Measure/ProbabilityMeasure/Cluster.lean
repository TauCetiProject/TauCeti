/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Integrals at weak cluster points

Bounded-continuous integrals preserve eventual membership in closed sets at weak cluster points.
-/

public section

open MeasureTheory Filter Set Topology
open scoped BoundedContinuousFunction

namespace MeasureTheory.ProbabilityMeasure

/-- A bounded-continuous integral at a weak cluster point belongs to every closed set that
eventually contains the integrals along the filter. -/
theorem integral_mem_of_mapClusterPt {ι X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {l : Filter ι} {μn : ι → ProbabilityMeasure X}
    {ν : ProbabilityMeasure X}
    (hν : MapClusterPt ν l μn) (g : X →ᵇ ℝ) {C : Set ℝ} (hC : IsClosed C)
    (h : ∀ᶠ n in l, ∫ x, g x ∂(μn n : Measure X) ∈ C) :
    ∫ x, g x ∂(ν : Measure X) ∈ C := by
  have hc : Continuous fun p : ProbabilityMeasure X => ∫ x, g x ∂(p : Measure X) :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction g
  have hcont : ContinuousAt (fun p : ProbabilityMeasure X => ∫ x, g x ∂(p : Measure X)) ν :=
    hc.continuousAt
  have hmap := MapClusterPt.continuousAt_comp
    (f := fun p : ProbabilityMeasure X => ∫ x, g x ∂(p : Measure X))
    (x := ν) hcont hν
  exact hC.mem_of_mapClusterPt hmap h

end MeasureTheory.ProbabilityMeasure
