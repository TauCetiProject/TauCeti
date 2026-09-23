/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.Complete
public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.TotallyBounded

/-!
# Graphon space is compact

The canonical graphon space `GraphonSpaceI` is a compact metric space (the
Lovász--Szegedy compactness theorem). It combines completeness of unit-interval graphons
with total boundedness of their cut-distance quotient.

## Main results

* `TauCeti.DenseGraphLimits.GraphonSpaceI.instCompactSpace` -- `GraphonSpaceI` is compact.

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

end DenseGraphLimits

end TauCeti
