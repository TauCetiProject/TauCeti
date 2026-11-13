/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Basic

/-!
# Boundaryless models have polyhedral range

The range of a boundaryless real model with corners is the whole model vector space, so it is a
convex polyhedron (`ModelWithCorners.isConvexPolyhedron_range`). Results on PL manifolds that
require a convex polyhedral model range, such as the PL inverse theorem `TauCeti.IsPLMap.symm`,
therefore apply to every boundaryless model. For the half-space model see
`TauCeti.isConvexPolyhedron_range_modelWithCornersHalfSpace`.
-/

public section

open Set

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]

/-- The range of a boundaryless model with corners, the whole model vector space, is a convex
polyhedron. -/
theorem ModelWithCorners.isConvexPolyhedron_range (I : ModelWithCorners ℝ E H)
    [I.Boundaryless] : TauCeti.IsConvexPolyhedron (range I) :=
  I.range_eq_univ ▸ TauCeti.isConvexPolyhedron_univ
