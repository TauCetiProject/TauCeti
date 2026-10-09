/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Homeomorph
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.BoundarySphere

/-!
# Geometric spheres from combinatorial spheres

The weak polyhedron of a combinatorial `n`-sphere is homeomorphic to the Euclidean unit
`n`-sphere. This identifies the spherical links used to construct interior vertex charts
in triangulated manifolds. The result concerns the actual subpolyhedron of an arbitrary
ambient realization, so unused ambient vertices contribute no extra points.

Intrinsic stellar equivalence supplies the homeomorphism to a simplex boundary, and the
standard simplex-boundary model supplies the Euclidean sphere. Injective relabeling changes
the ambient realization without changing the topology of the polyhedron. No finiteness
assumption on the ambient complex or its vertex type is required.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 2–3 (stellar equivalence and combinatorial manifolds).
-/

public section

open AbstractSimplicialComplex Metric

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {P : PreAbstractSimplicialComplex ι}
  {A : AbstractSimplicialComplex ι} {n : ℕ}

/-- A combinatorial `n`-sphere has a weak polyhedron homeomorphic to the unit `n`-sphere,
inside any ambient realization containing it. This includes the two-point zero-sphere. -/
theorem IsCombinatorialSphere.nonempty_homeomorph_sphere (h : IsCombinatorialSphere P n)
    (hA : P ≤ A.toPreAbstractSimplicialComplex) :
    Nonempty ({x : Realization A // x.1.support ∈ P} ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  have htop (Q : PreAbstractSimplicialComplex ι) :
      Q ≤ (⊤ : AbstractSimplicialComplex ι).toPreAbstractSimplicialComplex :=
    fun _ hσ => TauCeti.AbstractSimplicialComplex.mem_top_iff.mpr
      (Q.isRelLowerSet_faces.prop_of_mem hσ)
  have r : {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ P} ≃ₜ
      {x : Realization A // x.1.support ∈ P} := by
    have hid : P.map (Function.Embedding.refl ι) = P := by
      simpa only [Function.Embedding.coe_refl] using (map_id (K := P))
    exact (P.relabelingHomeomorph (Function.Embedding.refl ι) (htop P)
      (by rw [hid]; exact hA)).trans
      (Homeomorph.setCongr (by rw [hid]))
  obtain ⟨V, hV, he⟩ := isCombinatorialSphere_iff.mp h
  obtain ⟨s⟩ := he.nonempty_homeomorph h.finite_faces
  obtain ⟨t⟩ := nonempty_homeomorph_simplexBoundary_sphere hV (htop _)
  exact ⟨r.symm.trans (s.trans t)⟩

end PreAbstractSimplicialComplex
