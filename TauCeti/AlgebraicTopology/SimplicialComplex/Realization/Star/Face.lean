/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Homeomorph
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic

/-!
# Conical neighbourhoods of face barycentres

The closed star of a nonempty face is a conical neighbourhood of its barycentre. Starring
that face at a fresh vertex turns its closed star into a simplicial cone. The barycentric
stellar homeomorphism identifies this cone with the original closed star, taking the apex
to the barycentre and fixing the boundary. Its open apex star corresponds to the points
whose carriers contain the original face. That set is open in the ambient weak realization.
The cone's link corresponds exactly to the part of the original star avoiding that face.

These identifications work for arbitrary precomplexes in a containing weak realization,
without finiteness or local finiteness. They use the weak stellar homeomorphism from
`Subdivision.Stellar.Homeomorph` and the combinatorial link computation
`link_stellarSubdivision_singleton`. The boundary is a subpolyhedron, rather than the
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

/-- A closed face star is a neighbourhood of every point whose carrier contains that face,
relative to the original polyhedron in a containing weak realization. In particular this
applies to the face barycentre. -/
theorem closedStar_mem_nhds (K : PreAbstractSimplicialComplex ι)
    {x : {x : Realization A // x.1.support ∈ K}} (hx : σ ⊆ x.1.1.support) :
    {y : {x : Realization A // x.1.support ∈ K} |
      y.1.1.support ∈ closedStar K σ} ∈ 𝓝 x := by
  have hopen := (isOpen_biInter_finset fun i (_ : i ∈ σ) =>
    A.isOpen_openStarRealization i).preimage
      (continuous_subtype_val (p := fun x : Realization A => x.1.support ∈ K))
  have hmem : x.1 ∈ ⋂ i ∈ σ, A.openStarRealization i := by
    exact Set.mem_iInter₂.mpr fun i hi =>
      A.mem_openStarRealization_iff_mem_support.mpr (hx hi)
  apply Filter.mem_of_superset (hopen.mem_nhds hmem)
  intro y hy
  have hsub : σ ⊆ y.1.1.support := by
    intro i hi
    exact A.mem_openStarRealization_iff_mem_support.mp (Set.mem_iInter₂.mp hy i hi)
  exact mem_closedStar.mpr ⟨y.2, by simpa only [Finset.union_eq_left.mpr hsub] using y.2⟩

/-- A closed face star has a simplicial cone model in the weak topology. The cone apex maps
by the barycentric stellar map to the face barycentre. The open apex star maps exactly to
carriers containing the face; the cone link maps to the boundary subpolyhedron, and that
boundary is fixed pointwise. The containing realization may have arbitrary unused vertices. -/
theorem exists_isCone_homeomorph_closedStar (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K)
    (hK : closedStar K σ ≤ A.toPreAbstractSimplicialComplex)
    (hS : stellarSubdivision (closedStar K σ) σ v ≤ A.toPreAbstractSimplicialComplex) :
    ∃ C : PreAbstractSimplicialComplex ι, IsCone C v ∧
      link C {v} = closedStar K σ ⊓ deletion K σ ∧
      ∃ e : {x : Realization A // x.1.support ∈ C} ≃ₜ
          {x : Realization A // x.1.support ∈ closedStar K σ},
        (∀ x, (e x).1.1 = stellarSubdivisionLinearMap σ v x.1.1) ∧
        (∀ x, 0 < x.1.1 v ↔ σ ⊆ (e x).1.1.support) ∧
        (∀ x, x.1.1.support ∈ link C {v} ↔ (e x).1.1.support ∈ deletion K σ) ∧
        (∀ x, x.1.1.support ∈ link C {v} → (e x).1 = x.1) := by
  have hσstar : σ ∈ closedStar K σ := by simp [hσ]
  have hvstar : ({v} : Finset ι) ∉ closedStar K σ := fun h => hv (closedStar_le h)
  let C := stellarSubdivision (closedStar K σ) σ v
  have hcone : IsCone C v :=
    isCone_stellarSubdivision_of_closedStar_eq_self hσstar closedStar_closedStar
  have hlink : link C {v} = closedStar K σ ⊓ deletion K σ := by
    rw [link_stellarSubdivision_singleton hvstar, closedStar_closedStar]
    refine SetLike.ext fun τ => ?_
    simp only [mem_inf, mem_closedStar, mem_deletion]
    tauto
  obtain ⟨e, he⟩ := exists_homeomorph_stellarSubdivision hσstar hvstar hK hS
  have hopen (x) : 0 < x.1.1 v ↔ σ ⊆ (e x).1.1.support := by
    rw [he]
    exact (subset_support_stellarSubdivisionLinearMap_iff
      (notMem_of_singleton_notMem hv hσ) (Realization.nonneg A x.1) x.2).symm
  have hzero (x : {x : Realization A // x.1.support ∈ C}) :
      x.1.1 v = 0 ↔ (e x).1.1.support ∈ deletion K σ := by
    rw [mem_deletion]
    have hface := closedStar_le (e x).2
    have hnonneg := Realization.nonneg A x.1 v
    rw [← hopen]
    exact ⟨fun hz => ⟨hface, by linarith⟩, fun h => by linarith [h.2]⟩
  refine ⟨C, hcone, hlink, e, he, hopen, ?_, ?_⟩
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
