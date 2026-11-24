/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import TauCeti.Topology.FilledIn
-- Provides `NormedSpace.toLocallyConvexSpace`, hence `LocallyConnectedSpace E`.
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Geometry.Manifold.FilledIn

/-!
# Normed-space operations on sets filled in an open set

`TauCeti/Topology/FilledIn.lean` defines when a set `K` is filled in an ambient set `Ω`
(`TauCeti.IsFilledIn K Ω`, meaning no connected component of `Ω \ K` has compact closure inside
`Ω`) and defines `TauCeti.fillIn K Ω`, the union of `K` with all relatively compact components of
`Ω \ K` in `Ω`.

In a real normed space, boundedness of filled hulls (`TauCeti.isBounded_filledHull`) and
discrete-set adjoining on manifolds of real dimension greater than one
(`TauCeti.IsFilledIn.insert_of_chartedSpace` in `TauCeti/Geometry/Manifold/FilledIn.lean`) supply
two operations on domain-relative filled sets, independent of compact exhaustions:

* In a proper real normed space, filling a compact set `K` inside an open set `Ω` produces a
  compact set (`IsCompact.fillIn`), combining `IsClosed.fillIn` with enclosure inside
  `TauCeti.filledHull K` (`TauCeti.fillIn_subset_filledHull`).
* When `1 < Module.rank ℝ E` and `Ω \ K` is open, inserting a single point `z` into a set `K` filled
  in `Ω` preserves `TauCeti.IsFilledIn` (`TauCeti.IsFilledIn.insert`).

Both results enter the topological identification of `TauCeti.holomorphicHull Ω K` in
`TauCeti/Analysis/Complex/Runge/Approximation.lean`.

## Main results

* `IsCompact.fillIn`: filling a compact set inside an open set produces a compact set.
* `TauCeti.IsFilledIn.insert`: inserting a point preserves `TauCeti.IsFilledIn` in real dimension
  greater than one.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1 and Lemma 11.3.
-/

public section

open Metric Set

section CompactFill

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- In a proper real normed space, filling a compact set `K` inside an open set `Ω` produces a
compact set. -/
protected theorem IsCompact.fillIn {K Ω : Set E} (hK : IsCompact K) (hΩ : IsOpen Ω) :
    IsCompact (TauCeti.fillIn K Ω) :=
  isCompact_of_isClosed_isBounded (hK.isClosed.fillIn hΩ)
    ((isBounded_filledHull.mpr hK.isBounded).subset
      (fillIn_subset_filledHull (hΩ.sdiff hK.isClosed)))

end CompactFill

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In a real normed space of dimension greater than one, inserting a point into `K` when `Ω \ K`
is open preserves `TauCeti.IsFilledIn K Ω`. -/
protected theorem IsFilledIn.insert {K Ω : Set E} (h : IsFilledIn K Ω)
    (hrank : 1 < Module.rank ℝ E) (hΩK : IsOpen (Ω \ K)) (z : E) :
    IsFilledIn (insert z K) Ω :=
  h.insert_of_chartedSpace hrank hΩK z

end TauCeti
