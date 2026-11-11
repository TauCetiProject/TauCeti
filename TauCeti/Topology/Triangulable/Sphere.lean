/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.BoundarySphere
public import TauCeti.Topology.Triangulable.Vertices

/-!
# Triangulations of spheres

The boundary of the standard `(n + 1)`-simplex triangulates the unit `n`-sphere. Through the
stereographic homeomorphism, the one-point compactification of a finite-dimensional real vector
space is therefore triangulable. For instance the Riemann sphere `OnePoint ℂ` is triangulated
as the boundary of a tetrahedron.

## Main results

* `TauCeti.isTriangulable_sphere`: the unit `n`-sphere is triangulable.
* `TauCeti.isTriangulable_onePoint`: the one-point compactification of a finite-dimensional real
  vector space is triangulable.
-/

public section

open AbstractSimplicialComplex Metric Module

universe u v

namespace TauCeti

/-- The unit `n`-sphere is triangulable, by the boundary of the standard `(n + 1)`-simplex. -/
theorem isTriangulable_sphere (n : ℕ) :
    IsTriangulable.{v} (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ((realizationStandardSuccSimplexBoundaryHomeomorphSphere n).isTriangulable_iff.1
    (standardSuccSimplexBoundary n).isTriangulable_realization).lift_of_compactSpace

/-- The one-point compactification of a finite-dimensional real vector space is triangulable:
it is homeomorphic to a sphere, which is triangulated by the boundary of a simplex. -/
theorem isTriangulable_onePoint (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] :
    IsTriangulable.{v} (OnePoint V) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin (finrank ℝ V + 1)) (by simp)).isTriangulable_iff.2
    (isTriangulable_sphere _)

end TauCeti
