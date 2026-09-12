/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Triangle
public import Mathlib.MeasureTheory.Constructions.UnitInterval
import TauCeti.MeasureTheory.Measure.UnitIntervalMap

/-!
# Reading a graphon on the unit interval

Every standard Borel probability space receives a measure-preserving map out of `(I, volume)`
(Janson, Theorem A.9), and the cut distance does not change when a graphon is read along a
measure-preserving map (`cutDist_comap_right`).  Pulling a graphon back along such a map therefore
puts it on the canonical carrier `(I, volume)` at no cost: every graphon on a standard Borel
carrier is at cut distance zero from one on the unit interval, so nothing is lost by working there.

The map is an arbitrary choice, and so is the representative built from it; what is canonical is
its cut class, which is what `cutDist_unitIntervalModel` records.

The standard Borel hypothesis is what the map theorem needs, and this file does not remove it.
The representation theorem for an *arbitrary* probability carrier (Janson, Theorem 7.1) goes
through a countably generated sub-σ-algebra instead, and is not proved here.

## Main definitions

* `TauCeti.DenseGraphLimits.unitIntervalModel` -- the `(I, volume)` representative of a graphon on
  a standard Borel probability carrier.

## Main results

* `TauCeti.DenseGraphLimits.cutDist_unitIntervalModel` -- cut distances to a graphon are unchanged
  by reading it on the unit interval;
* `TauCeti.DenseGraphLimits.exists_graphon_unitInterval_cutDist_eq_zero_of_standardBorel` -- every
  graphon on a standard Borel carrier is at cut distance zero from one on the unit interval.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Theorem A.9.
-/

public section

noncomputable section

open MeasureTheory

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]

/-- The `(I, volume)` representative of a graphon on a standard Borel probability carrier: its
pullback along a measure-preserving map out of the unit interval (Janson, Thm A.9).

The map is an arbitrary choice; `cutDist_unitIntervalModel` shows that no cut distance to the
graphon depends on it. -/
def unitIntervalModel (ν : Measure α) [IsProbabilityMeasure ν] (V : Graphon α ν) :
    Graphon I (volume : Measure I) :=
  V.comap (Measure.exists_measurePreserving_from_unitInterval ν).choose
    (Measure.exists_measurePreserving_from_unitInterval ν).choose_spec.measurable volume

/-- Reading a graphon on the unit interval leaves every cut distance to it unchanged. -/
theorem cutDist_unitIntervalModel (ν : Measure α) [IsProbabilityMeasure ν] (U : Graphon Ω μ)
    (V : Graphon α ν) : cutDist U (unitIntervalModel ν V) = cutDist U V :=
  cutDist_comap_right U V (Measure.exists_measurePreserving_from_unitInterval ν).choose_spec

/-- **Every graphon on a standard Borel carrier is at cut distance zero from a graphon on the unit
interval**: the canonical carrier sees every such graphon up to cut distance.

This is the standard Borel case only, the one the map theorem of Janson, Thm A.9 covers; the
arbitrary-carrier representation theorem (Janson, Thm 7.1) is a separate statement. -/
theorem exists_graphon_unitInterval_cutDist_eq_zero_of_standardBorel (ν : Measure α)
    [IsProbabilityMeasure ν] (V : Graphon α ν) :
    ∃ W : Graphon I (volume : Measure I), cutDist V W = 0 :=
  ⟨unitIntervalModel ν V, (cutDist_unitIntervalModel ν V V).trans (cutDist_self V)⟩

end DenseGraphLimits

end TauCeti
