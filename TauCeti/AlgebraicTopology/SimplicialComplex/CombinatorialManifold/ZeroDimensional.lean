/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Basic

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.ZeroDimensional

/-!
# Combinatorial zero-balls and zero-spheres

A combinatorial zero-ball is exactly a single vertex, and a combinatorial zero-sphere is
exactly two distinct vertices, with no higher faces. These characterizations identify the base
cases of the sphere-or-ball link condition without requiring callers to unpack stellar move
sequences. In particular, the link of a vertex in a combinatorial one-manifold has one or two
vertices, corresponding to a boundary or interior point.

The definitions use stellar equivalence rather than a literal standard model. Their necessity
follows from preservation of dimension and, in dimension zero, of face cardinality under every
stellar move and injective relabeling.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3 (combinatorial balls, spheres, and manifold links).
-/

public section

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}

/-- A combinatorial zero-ball is exactly the simplex on a single vertex. -/
@[simp]
theorem isCombinatorialBall_zero_iff :
    IsCombinatorialBall K 0 ↔ ∃ v, K = simplex {v} := by
  constructor
  · intro h
    have hdim : dimension K ≤ 0 := h.dimension_eq.le
    obtain ⟨V, hV, he⟩ := isCombinatorialBall_iff.mp h
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (by simpa using hV)
    have hc := he.encard_faces_eq_of_dimension_le_zero hdim
    rw [simplex_singleton, TauCeti.PreAbstractSimplicialComplex.faces_point,
      Set.encard_singleton] at hc
    obtain ⟨σ, hfaces⟩ := Set.encard_eq_one.mp hc.symm
    have hσ : σ ∈ K.faces := by
      rw [hfaces]
      simp
    obtain ⟨w, rfl⟩ := dimension_le_zero_iff.mp hdim σ hσ
    refine ⟨w, PreAbstractSimplicialComplex.ext ?_⟩
    rw [simplex_singleton, TauCeti.PreAbstractSimplicialComplex.faces_point]
    exact hfaces
  · rintro ⟨v, rfl⟩
    exact isCombinatorialBall_simplex (by simp)

/-- A combinatorial zero-sphere is exactly the boundary of the edge on two distinct vertices. -/
@[simp]
theorem isCombinatorialSphere_zero_iff :
    IsCombinatorialSphere K 0 ↔ ∃ v w, v ≠ w ∧ K = simplexBoundary {v, w} := by
  constructor
  · intro h
    have hdim : dimension K ≤ 0 := h.dimension_eq.le
    obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp h
    obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp (by simpa using hV)
    have hc := he.encard_faces_eq_of_dimension_le_zero hdim
    rw [faces_simplexBoundary_pair hvw,
      Set.encard_pair (by simpa using hvw)] at hc
    obtain ⟨σ, τ, hστ, hfaces⟩ := Set.encard_eq_two.mp hc.symm
    have hσ : σ ∈ K.faces := by
      rw [hfaces]
      simp
    have hτ : τ ∈ K.faces := by
      rw [hfaces]
      simp
    obtain ⟨x, rfl⟩ := dimension_le_zero_iff.mp hdim σ hσ
    obtain ⟨y, rfl⟩ := dimension_le_zero_iff.mp hdim τ hτ
    have hxy : x ≠ y := by simpa using hστ
    refine ⟨x, y, hxy, PreAbstractSimplicialComplex.ext ?_⟩
    rw [faces_simplexBoundary_pair hxy]
    exact hfaces
  · rintro ⟨v, w, hvw, rfl⟩
    exact isCombinatorialSphere_simplexBoundary (by simp [hvw])

end PreAbstractSimplicialComplex
