/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Homeomorph
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Ball
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.BoundarySphere

/-!
# Geometric balls and spheres from combinatorial complexes

The weak polyhedron of a combinatorial `n`-ball or `n`-sphere is homeomorphic to the Euclidean
closed ball or unit sphere. The ball result identifies the closed vertex stars used to construct
manifold charts, while the sphere result identifies the spherical links at interior vertices. Both
results concern the actual subpolyhedron of an arbitrary ambient realization, so unused ambient
vertices contribute no extra points.

Intrinsic stellar equivalence supplies the homeomorphism to a simplex or simplex boundary, and the
standard models supply the Euclidean closed ball or sphere. Injective relabeling changes the
ambient realization without changing the topology of the polyhedron. No finiteness assumption on
the ambient complex or its vertex type is required; finiteness follows from the combinatorial
ball or sphere hypothesis.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 2–3 (stellar equivalence and combinatorial manifolds).
-/

public section

open AbstractSimplicialComplex Metric

namespace PreAbstractSimplicialComplex

variable {ι : Type*} {P : PreAbstractSimplicialComplex ι}
  {A : AbstractSimplicialComplex ι} {n : ℕ}

/-- A combinatorial `n`-ball has a weak polyhedron homeomorphic to the Euclidean closed `n`-ball.

The ambient complex may contain unused vertices. They are removed by the weak-polyhedron subtype. -/
theorem IsCombinatorialBall.nonempty_homeomorph_closedBall
    [DecidableEq ι] (h : IsCombinatorialBall P n)
    (hA : P ≤ A.toPreAbstractSimplicialComplex) :
    Nonempty ({x : Realization A // x.1.support ∈ P} ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  classical
  obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp h
  obtain ⟨s⟩ := he.nonempty_homeomorph h.finite_faces
  obtain ⟨t⟩ := nonempty_homeomorph_simplex_closedBall hV (le_top _)
  exact ⟨(topRealizationHomeomorph P hA).symm.trans (s.trans t)⟩

/-- A combinatorial `n`-sphere has a weak polyhedron homeomorphic to the unit `n`-sphere,
inside any ambient realization containing it. This includes the two-point zero-sphere. -/
theorem IsCombinatorialSphere.nonempty_homeomorph_sphere [DecidableEq ι]
    (h : IsCombinatorialSphere P n)
    (hA : P ≤ A.toPreAbstractSimplicialComplex) :
    Nonempty ({x : Realization A // x.1.support ∈ P} ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  classical
  let r := topRealizationHomeomorph P hA
  obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp h
  obtain ⟨s⟩ := he.nonempty_homeomorph h.finite_faces
  obtain ⟨t⟩ := nonempty_homeomorph_simplexBoundary_sphere hV (le_top _)
  exact ⟨r.symm.trans (s.trans t)⟩

end PreAbstractSimplicialComplex
