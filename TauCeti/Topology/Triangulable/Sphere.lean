/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.BoundarySphere
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import TauCeti.Geometry.Manifold.Triangulation.Puncture
public import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Manifold.Complex.Analytic

/-!
# Triangulations of spheres

The boundary of the standard `(n + 1)`-simplex is a finite simplicial complex whose realization
is homeomorphic to the unit sphere `Sⁿ` of `EuclideanSpace ℝ (Fin (n + 1))`
(`AbstractSimplicialComplex.realizationStandardSuccSimplexBoundaryHomeomorphSphere`). So every
sphere is triangulable, and so is the one-point compactification of a finite-dimensional real
vector space, which is homeomorphic to a sphere.

For the Riemann sphere `OnePoint ℂ`, a compact connected complex curve, the triangulation can be
moved so that any finite set becomes a set of vertices
(`Set.Finite.finiteCWType_compl_of_isTriangulable`). Hence the complement of every finite set of
points of the Riemann sphere has finite CW type. This is stated as a theorem rather than an
instance, since the finite set is a hypothesis and not part of the type.

## Main results

* `TauCeti.isTriangulable_sphere`: the unit sphere `Sⁿ` is triangulable.
* `TauCeti.isTriangulable_onePoint`: the one-point compactification of a finite-dimensional real
  vector space is triangulable.
* `Set.Finite.finiteCWType_compl_onePoint_complex`: the Riemann sphere punctured at a finite set
  has finite CW type.

## References

* J. R. Munkres, *Elements of Algebraic Topology*, Addison-Wesley, 1984, §1 (the boundary of a
  simplex as a triangulation of a sphere).
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (punctured surfaces in the topological proof of Riemann–Hurwitz).
-/

public section

open Metric Module
open scoped Manifold

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

namespace Set.Finite

open TauCeti

/-- **Punctured Riemann spheres have finite CW type.** The complement of a finite set of points
of the Riemann sphere `OnePoint ℂ` has finite CW type. -/
theorem finiteCWType_compl_onePoint_complex {S : Set (OnePoint ℂ)} (hS : S.Finite) :
    FiniteCWType ↥Sᶜ := by
  have : IsManifold 𝓘(ℝ, ℂ) 2 (OnePoint ℂ) :=
    (inferInstance : IsManifold 𝓘(ℂ) 1 (OnePoint ℂ)).restrictScalars_of_ne_zero 2 (by norm_num)
  exact hS.finiteCWType_compl_of_isTriangulable (E := ℂ)
    (by rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]; norm_num)
    (isTriangulable_onePoint.{0, 0})

end Set.Finite
