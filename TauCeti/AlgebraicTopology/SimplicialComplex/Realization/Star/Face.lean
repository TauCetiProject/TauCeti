/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Homeomorph

/-!
# Conical neighbourhoods of face barycentres

The closed star of a nonempty face is a conical neighbourhood of its barycentre. Starring
that face at a fresh vertex turns its closed star into a simplicial cone
(`isCone_stellarSubdivision_closedStar`). The barycentric stellar homeomorphism identifies this
cone with the original closed star, taking the apex to the barycentre
(`AbstractSimplicialComplex.stellarSubdivisionLinearMap_single_eq_faceBarycenter`) and fixing
the boundary. Its open apex star corresponds to the points whose carriers contain the original
face. That set is open relative to the polyhedron of the original precomplex, since it is the
trace of the ambient open vertex stars of the face; so the closed star is a neighbourhood of
these points in that polyhedron (`setOf_support_mem_closedStar_mem_nhds`, in
`Realization.Star.Basic`). It need not be open
in the ambient weak realization: an open edge is not open in a containing triangle. The cone's
link corresponds exactly to the part of the original star avoiding that face.

These identifications work for arbitrary precomplexes in a containing weak realization,
without finiteness or local finiteness. They use the weak stellar homeomorphism from
`Subdivision.Stellar.Homeomorph` and the combinatorial link computation
`link_stellarSubdivision_closedStar_singleton`. The boundary is a subpolyhedron, rather than the
ambient topological frontier, which can be smaller when the face star is the whole space.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapter 2 (starrings and conical neighbourhoods).
-/

public section

open Set Topology AbstractSimplicialComplex Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {A : AbstractSimplicialComplex ι} {σ : Finset ι} {v : ι}

/-- The starred closed star of a face is identified with the original closed star in the weak
topology. This starred complex is a simplicial cone with apex the new vertex
(`isCone_stellarSubdivision_closedStar`), and the cone apex maps by the barycentric stellar map
to the face barycentre. The open apex star maps exactly to carriers containing the face; the
cone link maps to the boundary subpolyhedron, and that boundary is fixed pointwise. The
containing realization may have arbitrary unused vertices. -/
theorem exists_homeomorph_stellarSubdivision_closedStar (hσ : σ ∈ K)
    (hv : ({v} : Finset ι) ∉ closedStar K σ)
    (hK : closedStar K σ ≤ A.toPreAbstractSimplicialComplex)
    (hS : stellarSubdivision (closedStar K σ) σ v ≤ A.toPreAbstractSimplicialComplex) :
    ∃ e : {x : Realization A // x.1.support ∈ stellarSubdivision (closedStar K σ) σ v} ≃ₜ
        {x : Realization A // x.1.support ∈ closedStar K σ},
      (∀ x, (e x).1.1 = stellarSubdivisionLinearMap σ v x.1.1) ∧
      (∀ x, 0 < x.1.1 v ↔ σ ⊆ (e x).1.1.support) ∧
      (∀ x, x.1.1.support ∈ link (stellarSubdivision (closedStar K σ) σ v) {v} ↔
        (e x).1.1.support ∈ deletion K σ) ∧
      (∀ x, x.1.1.support ∈ link (stellarSubdivision (closedStar K σ) σ v) {v} →
        (e x).1 = x.1) := by
  have hσstar : σ ∈ closedStar K σ := by simp [hσ]
  have hcone := isCone_stellarSubdivision_closedStar (v := v) hσ
  obtain ⟨e, he⟩ := exists_homeomorph_stellarSubdivision hσstar hv hK hS
  have hopen (x) : 0 < x.1.1 v ↔ σ ⊆ (e x).1.1.support := by
    rw [he]
    exact (subset_support_stellarSubdivisionLinearMap_iff (Realization.nonneg A x.1) x.2).symm
  have hzero (x : {x : Realization A // x.1.support ∈ stellarSubdivision (closedStar K σ) σ v}) :
      x.1.1 v = 0 ↔ (e x).1.1.support ∈ deletion K σ := by
    rw [mem_deletion]
    have hface := closedStar_le (e x).2
    have hnonneg := Realization.nonneg A x.1 v
    rw [← hopen]
    exact ⟨fun hz => ⟨hface, by linarith⟩, fun h => by linarith [h.2]⟩
  refine ⟨e, he, hopen, ?_, ?_⟩
  · intro x
    rw [mem_link, Finset.disjoint_singleton_right, Finsupp.notMem_support_iff]
    have hinsert := hcone.insert_mem x.2
    simpa only [x.2, true_and, Finset.union_singleton, hinsert, and_true] using hzero x
  · intro x hx
    have hxv : x.1.1 v = 0 := Finsupp.notMem_support_iff.mp
      (Finset.disjoint_singleton_right.mp (mem_link.mp hx).2.1)
    apply Subtype.ext
    rw [he]
    ext i
    simp [stellarSubdivisionLinearMap_apply, hxv]

end PreAbstractSimplicialComplex
