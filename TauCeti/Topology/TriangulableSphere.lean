/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.BoundarySphere
public import TauCeti.Topology.Triangulable

/-!
# Triangulability of spheres

This file proves that every round sphere is triangulable, using the homeomorphism from the
realization of the boundary of a standard simplex.

## Main results

* `TauCeti.isTriangulable_sphere`: the unit `n`-sphere is triangulable.
-/

public section

noncomputable section

open Metric

namespace TauCeti

/-- The unit `n`-sphere is triangulable: it is homeomorphic to the realization of the boundary of
the standard `(n + 1)`-simplex. -/
theorem isTriangulable_sphere (n : ℕ) :
    IsTriangulable.{0} (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  (AbstractSimplicialComplex.realizationStandardSuccSimplexBoundaryHomeomorphSphere
    n).isTriangulable_iff.mp (AbstractSimplicialComplex.isTriangulable_realization _)

end TauCeti
