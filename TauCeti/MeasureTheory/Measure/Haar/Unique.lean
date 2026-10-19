/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Nonsingularity of topological group isomorphisms

A continuous group isomorphism into a second-countable locally compact group is nonsingular for
any Haar measures chosen on its source and target. Thus null sets can be transported between the
groups independently of the normalizations of their measures. Both multiplicative and additive
versions are provided.

This uses `MeasureTheory.Measure.absolutelyContinuous_isHaarMeasure` for the pushforward,
which is again a Haar measure.

## Main results

* `ContinuousMulEquiv.quasiMeasurePreserving_haar`: a continuous group isomorphism
  is quasi measure preserving for Haar measures on its source and target.
* `ContinuousAddEquiv.quasiMeasurePreserving_addHaar`: the additive version.
-/

public section

open MeasureTheory MeasureTheory.Measure

/-- A continuous group isomorphism into a second-countable locally compact group is nonsingular
for any Haar measures on its source and target. -/
@[to_additive
/-- A continuous additive equivalence into a second-countable locally compact group is nonsingular
for any additive Haar measures on its source and target. -/]
theorem ContinuousMulEquiv.quasiMeasurePreserving_haar {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H]
    (e : G ≃ₜ* H) (μ : Measure G) (ν : Measure H)
    [IsHaarMeasure μ] [IsHaarMeasure ν] : QuasiMeasurePreserving e μ ν :=
  ⟨e.continuous.measurable, absolutelyContinuous_isHaarMeasure (μ.map e) ν⟩

end
