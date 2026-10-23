/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Compactness.DeltaGeneratedSpace
public import TauCeti.Topology.CWComplex.Classical.Quotient

/-!
# CW complexes are delta-generated, hence locally path-connected

A Hausdorff relative CW complex `C` with base `D` is a quotient of the disjoint union of `D` and
of one closed unit ball of `Fin n → ℝ` for each `n`-cell
(`TauCeti.isQuotientMap_sumElim_base_map`). Closed balls of `Fin n → ℝ` are delta-generated
(`TauCeti.instDeltaGeneratedSpaceClosedBall`), and disjoint unions and quotients of
delta-generated spaces are delta-generated. So `C` is delta-generated as soon as its base is
(`TauCeti.deltaGeneratedSpace_complex`), and every Hausdorff CW complex is delta-generated
(`TauCeti.instDeltaGeneratedSpaceCWComplex`, and `TauCeti.instDeltaGeneratedSpaceOfCWComplexUniv`
for a CW structure on the whole space).

Delta-generated spaces are locally path-connected and sequential (Mathlib's instances for
`DeltaGeneratedSpace`), so with these instances every Hausdorff CW complex is a
`LocallyPathConnectedSpace` and a `SequentialSpace`. Local path-connectedness is one of the
standing hypotheses of covering-space theory: a path-connected, locally path-connected and
semilocally simply connected space has a universal cover.

## Main results

* `TauCeti.deltaGeneratedSpace_complex`: a Hausdorff relative CW complex over a delta-generated
  base is delta-generated.
* `TauCeti.instDeltaGeneratedSpaceCWComplex`: a Hausdorff CW complex is delta-generated.
* `TauCeti.instDeltaGeneratedSpaceOfCWComplexUniv`: a Hausdorff space with a CW structure on the
  whole space is delta-generated.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Proposition A.4: CW complexes are locally contractible, in particular locally
  path-connected.
-/

public section

open Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/-- **A relative CW complex over a delta-generated base is delta-generated.** The complex is a
quotient of the disjoint union of its base and of its closed cells, and closed balls are
delta-generated. -/
theorem deltaGeneratedSpace_complex {C D : Set X} [RelCWComplex C D] [DeltaGeneratedSpace D] :
    DeltaGeneratedSpace C :=
  isQuotientMap_sumElim_base_map.isGeneratedBy

/-- **A Hausdorff CW complex is delta-generated**, so in particular locally path-connected. -/
instance instDeltaGeneratedSpaceCWComplex {C : Set X} [CWComplex C] : DeltaGeneratedSpace C :=
  deltaGeneratedSpace_complex (D := ∅)

/-- **A Hausdorff space with a CW structure on the whole space is delta-generated**, so in
particular locally path-connected. -/
instance instDeltaGeneratedSpaceOfCWComplexUniv [CWComplex (univ : Set X)] :
    DeltaGeneratedSpace X :=
  (Homeomorph.Set.univ X).isQuotientMap.isGeneratedBy

end TauCeti
