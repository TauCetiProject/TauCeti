/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Homeomorph
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Ball

/-!
# Realizing combinatorial balls

The weak polyhedron of a combinatorial `n`-ball is homeomorphic to the Euclidean closed
`n`-ball. The identification works inside any ambient realization containing the complex,
including infinite complexes with unused vertices. In particular, a ball vertex link has
the closed-disc model needed for a boundary vertex chart. Dimension zero gives a singleton
disc, as required at an endpoint of a one-dimensional manifold.

Stellar equivalence supplies the comparison with a simplex; the simplex-to-ball comparison
uses Mathlib's convex-body rescaling. These are topological identifications, with no claim
of piecewise-linear regularity of the radial rescaling.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2–3 (stellar equivalence and combinatorial balls).
-/

public section

open Set Metric AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex

/-- A combinatorial `n`-ball realizes to the Euclidean closed `n`-ball. The polyhedron
carries the subspace topology of any containing weak realization, and unused vertices
contribute no points. -/
theorem IsCombinatorialBall.nonempty_homeomorph_closedBall {ι : Type*} [DecidableEq ι]
    {P : PreAbstractSimplicialComplex ι} {n : ℕ} (h : IsCombinatorialBall P n)
    {K : AbstractSimplicialComplex ι} (hK : P ≤ K.toPreAbstractSimplicialComplex) :
    Nonempty ({x : Realization K // x.1.support ∈ P} ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have htop (Q : PreAbstractSimplicialComplex ι) :
      Q ≤ (⊤ : AbstractSimplicialComplex ι).toPreAbstractSimplicialComplex := by
    rw [top_toPreAbstractSimplicialComplex]
    exact le_top
  obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp h
  obtain ⟨e⟩ := he.nonempty_homeomorph h.finite_faces
  obtain ⟨b⟩ := nonempty_homeomorph_simplex_closedBall hV (htop _)
  exact ⟨(P.ambientHomeomorph hK (htop _)).trans (e.trans b)⟩

end PreAbstractSimplicialComplex
