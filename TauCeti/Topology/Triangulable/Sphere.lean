/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.BoundarySphere
public import TauCeti.Topology.Triangulable.Vertices
public import Mathlib.Topology.Compactification.OnePoint.Sphere
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Triangulations of spheres

The boundary of the standard `(n + 1)`-simplex is a finite simplicial complex whose realization
is homeomorphic to the unit sphere `Sⁿ` of `EuclideanSpace ℝ (Fin (n + 1))`
(`AbstractSimplicialComplex.realizationStandardSuccSimplexBoundaryHomeomorphSphere`). We deduce
that every sphere `sphere x r` of a finite-dimensional real normed space is triangulable, and so is
the one-point compactification of a finite-dimensional real vector space. These triangulations
are what is needed to puncture spheres, for instance the Riemann sphere at finitely many points.

## Main results

* `TauCeti.isTriangulable_sphere`: every sphere of a finite-dimensional real normed space is
  triangulable.
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

/-- The unit sphere of a finite-dimensional real normed space is triangulable. -/
private theorem isTriangulable_unitSphere {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : IsTriangulable.{v} (sphere (0 : E) 1) := by
  rcases (finrank ℝ E).eq_zero_or_pos with hE | hE
  · have : IsEmpty (sphere (0 : E) 1) := ⟨fun x ↦ by
      simpa [finrank_zero_iff_forall_zero.1 hE x] using x.2⟩
    exact (isTriangulable_of_discreteTopology _).lift_of_compactSpace
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero hE.ne'
    refine ((sphereHomeomorphOfFinrankEq (F := EuclideanSpace ℝ (Fin (n + 1)))
      (by simp [hn])).isTriangulable_iff).2 <| IsTriangulable.lift_of_compactSpace.{0} <|
      (isTriangulable_iff _).2 ⟨Fin (n + 2), _,
        ⟨AbstractSimplicialComplex.realizationStandardSuccSimplexBoundaryHomeomorphSphere n⟩⟩

/-- **Spheres are triangulable.** Every sphere `sphere x r` of a finite-dimensional real normed
space is triangulable, with vertices in any universe. -/
theorem isTriangulable_sphere {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (x : E) (r : ℝ) : IsTriangulable.{v} (sphere x r) := by
  rcases le_or_gt r 0 with hr | hr
  · have h (a : sphere x r) : (a : E) = x := dist_le_zero.1 ((mem_sphere.1 a.2).le.trans hr)
    have : Subsingleton (sphere x r) := ⟨fun a b ↦ Subtype.ext ((h a).trans (h b).symm)⟩
    exact (isTriangulable_of_discreteTopology _).lift_of_compactSpace
  · refine ((((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft x)).subtype
      (p := (· ∈ sphere (0 : E) 1)) (q := (· ∈ sphere x r)) fun v ↦ ?_).isTriangulable_iff).1
      isTriangulable_unitSphere
    simp [norm_smul, abs_of_pos hr, hr.ne']

/-- **One-point compactifications of finite-dimensional real vector spaces are triangulable.**
The one-point compactification `OnePoint V` of a finite-dimensional Hausdorff real topological
vector space `V` is triangulable, with vertices in any universe. In particular the Riemann sphere
`OnePoint ℂ` is triangulable. -/
theorem isTriangulable_onePoint {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] :
    IsTriangulable.{v} (OnePoint V) :=
  ((onePointEquivSphereOfFinrankEq (ι := Fin (finrank ℝ V + 1)) (by simp)).isTriangulable_iff).2
    (isTriangulable_sphere _ _)

end TauCeti
