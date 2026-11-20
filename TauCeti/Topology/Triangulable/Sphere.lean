/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.BoundarySphere
public import TauCeti.Topology.Triangulable.Vertices
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Triangulations of spheres

The boundary of the standard `(n + 1)`-simplex triangulates the unit `n`-sphere, and hence every
sphere of positive radius in a real normed space of dimension `n + 1`. Through the
stereographic homeomorphism, the one-point compactification of a finite-dimensional real vector
space is therefore triangulable. For instance the Riemann sphere `OnePoint ℂ` is triangulated
as the boundary of a tetrahedron.

## Main results

* `TauCeti.isTriangulable_sphere`: every sphere in a finite-dimensional real normed space is
  triangulable.
* `TauCeti.isTriangulable_onePoint`: the one-point compactification of a finite-dimensional real
  vector space is triangulable.
-/

public section

open AbstractSimplicialComplex Metric Module

universe u v

namespace TauCeti

/-- The unit `n`-sphere of Euclidean space is triangulable, by the boundary of the standard
`(n + 1)`-simplex. -/
private theorem isTriangulable_sphere_euclideanSpace (n : ℕ) :
    IsTriangulable.{v} (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ((realizationStandardSuccSimplexBoundaryHomeomorphSphere n).isTriangulable_iff.1
    (standardSuccSimplexBoundary n).isTriangulable_realization).lift_of_compactSpace

/-- Every sphere in a finite-dimensional real normed space is triangulable. A sphere of positive
radius in a space of dimension `n + 1` is triangulated by the boundary of the standard
`(n + 1)`-simplex; every other sphere has at most one point. -/
theorem isTriangulable_sphere {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (x : E) (r : ℝ) : IsTriangulable.{v} (sphere x r) := by
  rcases le_or_gt r 0 with hr | hr
  · have : Subsingleton (sphere x r) := (subsingleton_sphere x hr).coe_sort
    exact (isTriangulable_of_discreteTopology _).lift_of_compactSpace
  cases hE : finrank ℝ E with
  | zero =>
    have : Subsingleton E := finrank_zero_iff.1 hE
    exact (isTriangulable_of_discreteTopology _).lift_of_compactSpace
  | succ n =>
    let e : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₜ sphere x r :=
      (sphereHomeomorphOfFinrankEq (by simp [hE])).trans <|
        ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addRight x)).subtype fun y => by
          simp [mem_sphere_iff_norm, Homeomorph.smulOfNeZero_apply, norm_smul, Real.norm_eq_abs,
            abs_of_pos hr, hr.ne']
    exact e.isTriangulable_iff.1 (isTriangulable_sphere_euclideanSpace n)

/-- The one-point compactification of a finite-dimensional real vector space is triangulable:
it is homeomorphic to a sphere, which is triangulated by the boundary of a simplex. -/
theorem isTriangulable_onePoint {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] :
    IsTriangulable.{v} (OnePoint V) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin (finrank ℝ V + 1)) (by simp)).isTriangulable_iff.2
    (isTriangulable_sphere _ _)

end TauCeti
