/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Nonsingularity of topological additive equivalences

A continuous additive equivalence into a second-countable locally compact group is nonsingular
for any additive Haar measures chosen on its source and target. Thus null sets can be transported
between the groups independently of the normalizations of their measures.

This uses `MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure` for the pushforward,
which is again an additive Haar measure.

## Main results

* `ContinuousAddEquiv.quasiMeasurePreserving_addHaar`: a continuous additive equivalence
  is quasi measure preserving for additive Haar measures on its source and target.
-/

public section

open MeasureTheory MeasureTheory.Measure

/-- A continuous additive equivalence into a second-countable locally compact group is nonsingular
for any additive Haar measures on its source and target. -/
theorem ContinuousAddEquiv.quasiMeasurePreserving_addHaar {G H : Type*}
    [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [AddGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H]
    (e : G ≃ₜ+ H) (μ : Measure G) (ν : Measure H)
    [IsAddHaarMeasure μ] [IsAddHaarMeasure ν] : QuasiMeasurePreserving e μ ν :=
  ⟨e.continuous.measurable, absolutelyContinuous_isAddHaarMeasure (μ.map e) ν⟩

end
