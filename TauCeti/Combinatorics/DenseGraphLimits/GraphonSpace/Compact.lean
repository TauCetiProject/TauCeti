/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.Complete
public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.TotallyBounded
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Graphon space is compact

The canonical graphon space `GraphonSpaceI` is a compact metric space (the
Lovász--Szegedy compactness theorem). It combines completeness of unit-interval graphons
with total boundedness of their cut-distance quotient.

Compactness passes to the mixing measures: `ProbabilityMeasure GraphonSpaceI` is compact and
metrizable (the compact-space direction of Prokhorov's theorem), so every sequence of probability
measures on the graphon space has a weakly convergent subsequence
(`exists_subseq_tendsto_probabilityMeasure`).

## Main results

* `TauCeti.DenseGraphLimits.GraphonSpaceI.instCompactSpace` -- `GraphonSpaceI` is compact.
* `TauCeti.DenseGraphLimits.exists_subseq_tendsto_probabilityMeasure` -- every sequence of
  probability measures on `GraphonSpaceI` has a weakly convergent subsequence.

## References

* L. Lovász and B. Szegedy, *Szemerédi's Lemma for the Analyst*, GAFA 17 (2007), Theorem 5.1.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Theorem 9.23.
-/

public section

noncomputable section

open Filter MeasureTheory

open scoped Topology unitInterval

namespace TauCeti

namespace DenseGraphLimits

/-- **Lovász--Szegedy compactness.** The cut-distance quotient of unit-interval graphons is a
compact metric space. This supplies compactness for graphon-space arguments. -/
instance GraphonSpaceI.instCompactSpace : CompactSpace GraphonSpaceI :=
  ⟨isCompact_iff_totallyBounded_isComplete.2 ⟨totallyBounded_graphonSpaceI, isComplete_univ⟩⟩

/-- **Compactness extraction.** Every sequence of probability measures on `GraphonSpaceI` has a
weakly convergent subsequence: the graphon space is a compact metric space, so its space of
probability measures is compact and metrizable (the compact-space direction of Prokhorov's
theorem, with no tightness argument). -/
theorem exists_subseq_tendsto_probabilityMeasure (Ps : ℕ → ProbabilityMeasure GraphonSpaceI) :
    ∃ (P : ProbabilityMeasure GraphonSpaceI) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (Ps ∘ φ) atTop (𝓝 P) :=
  CompactSpace.tendsto_subseq Ps

end DenseGraphLimits

end TauCeti
