/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.AtomlessStandardBorel
public import TauCeti.MeasureTheory.Measure.UnitIntervalMap

/-!
# Transport from an atomless standard Borel probability space

An atomless standard Borel probability space admits a measurable map with any prescribed
standard Borel probability law. The source is measure-preservingly mapped to the unit interval
by `MeasureTheory.Measure.exists_mpModNull_equiv_unitInterval`, and the requested law is
realized from that interval by `MeasureTheory.Measure.exists_measurePreserving_from_unitInterval`.
The resulting map may collapse sets of positive measure when the target has atoms.

This is the nonatomic feasibility result for the Monge transport problem. It also supplies
the map realization needed when approximating couplings by graph plans.

See S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*,
Theorems A.7 and A.9, for the two standard Borel transport results being composed.
-/

public section

open MeasureTheory

namespace MeasureTheory.Measure

/-- Every probability law on a standard Borel target is the image of an atomless standard Borel
probability law under a measurable map. The target may have atoms.

Mathlib's `Measure.exists_measurable_map_eq` starts from the unit interval; the atomless source
is mapped to that interval first. -/
theorem exists_measurePreserving_of_nullSingleton
    {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] :
    ∃ T : X → Y, MeasurePreserving T μ ν := by
  obtain ⟨f, -, hf, -⟩ := μ.exists_mpModNull_equiv_unitInterval
  obtain ⟨g, hg⟩ := ν.exists_measurePreserving_from_unitInterval
  exact ⟨g ∘ f, hg.comp hf⟩

end MeasureTheory.Measure
