/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import TauCeti.Topology.FilledIn
-- Provides `NormedSpace.toLocallyConvexSpace`, hence `LocallyConnectedSpace E`.
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import TauCeti.Analysis.Normed.Module.FilledHull

/-!
# Compactness of the relative fill in a proper normed space

`TauCeti/Topology/FilledIn.lean` defines when a set `K` is filled in an ambient set `Ω`
(`TauCeti.IsFilledIn K Ω`, meaning no connected component of `Ω \ K` has compact closure inside
`Ω`) and defines `TauCeti.fillIn K Ω`, the union of `K` with all relatively compact components of
`Ω \ K` in `Ω`.

In a proper real normed space, boundedness of filled hulls (`TauCeti.isBounded_filledHull`) implies
that filling a compact set `K` inside an open set `Ω` produces a compact set (`IsCompact.fillIn`),
combining `IsClosed.fillIn` with enclosure inside `TauCeti.filledHull K`
(`TauCeti.fillIn_subset_filledHull`). Preservation of `TauCeti.IsFilledIn` under adjoining a point
(`TauCeti.IsFilledIn.insert`) or a closed discrete set (`TauCeti.IsFilledIn.union_of_isDiscrete`) in
real dimension greater than one is proved more generally for manifolds in
`TauCeti/Geometry/Manifold/FilledIn.lean` (applying directly to `E` via `chartedSpaceSelf`). Both
results enter the topological identification of `TauCeti.holomorphicHull Ω K` in
`TauCeti/Analysis/Complex/Runge/Approximation.lean`.

## Main results

* `IsCompact.fillIn`: filling a compact set inside an open set produces a compact set.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1 and Lemma 11.3.
-/

public section

open Metric Set TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- In a proper real normed space, filling a compact set `K` inside an open set `Ω` produces a
compact set. -/
protected theorem IsCompact.fillIn {K Ω : Set E} (hK : IsCompact K) (hΩ : IsOpen Ω) :
    IsCompact (TauCeti.fillIn K Ω) :=
  isCompact_of_isClosed_isBounded (hK.isClosed.fillIn hΩ)
    ((isBounded_filledHull.mpr hK.isBounded).subset
      (fillIn_subset_filledHull (hΩ.sdiff hK.isClosed)))

end
