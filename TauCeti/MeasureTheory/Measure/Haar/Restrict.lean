/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Sets.Opens

/-!
# Restricting an additive Haar measure to the whole space

Restricting a measure to the top open set `⊤ : Opens G` gives back the measure, but instance search
does not see through the coercion of `⊤` to `Set.univ`. Function spaces on an open set `Ω`, such as
test functions and Sobolev spaces, use the restricted measure `μ.restrict Ω`; the instance
`TauCeti.instIsAddHaarMeasureRestrictTop` lets their whole-space versions use the Haar measure API.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace

/-- The whole-space restriction of an additive Haar measure is an additive Haar measure. -/
instance instIsAddHaarMeasureRestrictTop {G : Type*} [MeasurableSpace G] [TopologicalSpace G]
    [AddGroup G] {μ : Measure G} [μ.IsAddHaarMeasure] :
    (μ.restrict (⊤ : Opens G)).IsAddHaarMeasure := by
  simpa only [Opens.coe_top, Measure.restrict_univ] using (inferInstance : μ.IsAddHaarMeasure)

end TauCeti
