/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.BoundarySphere
public import TauCeti.Topology.Triangulable.Vertices
public import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# Triangulations of spheres

The boundary of the standard `(n + 1)`-simplex is a finite simplicial complex whose realization
is homeomorphic to the unit sphere `Sⁿ` of `EuclideanSpace ℝ (Fin (n + 1))`
(`AbstractSimplicialComplex.realizationStandardSuccSimplexBoundaryHomeomorphSphere`). So every
sphere is triangulable, and so is the one-point compactification of a finite-dimensional real
vector space, which is homeomorphic to a sphere.

## Main results

* `TauCeti.isTriangulable_sphere`: the unit sphere `Sⁿ` is triangulable.
* `TauCeti.isTriangulable_onePoint`: the one-point compactification of a finite-dimensional real
  vector space is triangulable.

## References

* J. R. Munkres, *Elements of Algebraic Topology*, Addison-Wesley, 1984, §1 (the boundary of a
  simplex as a triangulation of a sphere).
-/

public section

open Metric Module

universe u v

namespace TauCeti

/-- **Spheres are triangulable.** The unit sphere `Sⁿ` of `EuclideanSpace ℝ (Fin (n + 1))` is
homeomorphic to the realization of the boundary of the standard `(n + 1)`-simplex. -/
theorem isTriangulable_sphere (n : ℕ) :
    IsTriangulable.{v} (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  IsTriangulable.lift_of_compactSpace.{0} <| (isTriangulable_iff _).2
    ⟨Fin (n + 2), _,
      ⟨AbstractSimplicialComplex.realizationStandardSuccSimplexBoundaryHomeomorphSphere n⟩⟩

/-- **One-point compactifications of real vector spaces are triangulable.** The one-point
compactification of a finite-dimensional real vector space is homeomorphic to a sphere, hence
triangulable. In particular the Riemann sphere `OnePoint ℂ` is triangulable. -/
theorem isTriangulable_onePoint {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] :
    IsTriangulable.{v} (OnePoint V) :=
  ((onePointEquivSphereOfFinrankEq (ι := Fin (finrank ℝ V + 1)) (by simp)).isTriangulable_iff).2
    (isTriangulable_sphere _)

end TauCeti
