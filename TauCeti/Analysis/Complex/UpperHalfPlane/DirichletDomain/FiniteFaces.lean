/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.DirichletDomain.Finite
public import TauCeti.Analysis.Complex.UpperHalfPlane.DirichletDomain.UnboundedFaces

/-!
# Finite face covers of hyperbolic Dirichlet domains

A finite closed-half-plane description of a Dirichlet domain gives a finite cover of its
boundary by equality faces (`frontier_dirichletDomain_eq_biUnion_dirichletFace_of_eq_iInter`).
Every nonempty face in this cover is a single extended geodesic segment
(`exists_dirichletFace_eq_extGeodesicSegment`): a bounded segment, a ray with one ideal
endpoint, or a complete geodesic with two ideal endpoints.

Together these results turn finite distance constraints into the finite geodesic boundary data
needed to enumerate the sides and vertices of a Dirichlet polygon. Redundant constraints are
allowed: a selected face may be empty or may consist of a single point.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §3.2.
-/

public section

open Set UpperHalfPlane
open scoped MatrixGroups OnePoint

namespace TauCeti.UpperHalfPlane

variable {G : Type*} [SMul G ℍ]

/-- If finitely many nontrivial distance constraints define a Dirichlet domain, their equality
faces cover its boundary exactly. Constraints which are redundant contribute an empty or
lower-dimensional face, so no irredundancy hypothesis is needed. -/
theorem frontier_dirichletDomain_eq_biUnion_dirichletFace_of_eq_iInter
    {p : ℍ} {s : Finset G} (hmove : ∀ g ∈ s, p ≠ g • p)
    (hD : dirichletDomain G p =
      ⋂ g ∈ s, closure (leftHalfPlane (perpBisector p (g • p)))) :
    frontier (dirichletDomain G p) = ⋃ g ∈ s, dirichletFace p g := by
  apply Set.Subset.antisymm
  · intro z hz
    have hzD : z ∈ dirichletDomain G p :=
      (isClosed_dirichletDomain G p).closure_subset (frontier_subset_closure hz)
    by_contra hzfaces
    have hstrict : ∀ g ∈ s, dist z p < dist z (g • p) := by
      intro g hg
      refine lt_of_le_of_ne (mem_dirichletDomain.mp hzD g) fun heq ↦ ?_
      apply hzfaces
      exact mem_iUnion_of_mem g (mem_iUnion_of_mem hg
        (mem_dirichletFace.mpr ⟨hzD, heq⟩))
    apply hz.2
    rw [hD, Finset.interior_iInter]
    exact mem_iInter₂.mpr fun g hg ↦ by
      rw [interior_closure_leftHalfPlane,
        mem_leftHalfPlane_perpBisector_iff (hmove g hg)]
      exact hstrict g hg
  · exact iUnion₂_subset fun g hg ↦ dirichletFace_subset_frontier (hmove g hg).symm

/-- Every nonempty equality face indexed by an element moving the centre is one extended
geodesic segment. The endpoints may coincide in the bounded singleton case. -/
theorem exists_dirichletFace_eq_extGeodesicSegment {p : ℍ} {g : G} (hg : g • p ≠ p)
    (hne : (dirichletFace p g).Nonempty) :
    ∃ a b : ℍ ⊕ OnePoint ℝ, dirichletFace p g = extGeodesicSegment a b := by
  by_cases hb : Bornology.IsBounded (dirichletFace p g)
  · obtain ⟨z, w, hzw⟩ := exists_dirichletFace_eq_geodesicSegment hg hne hb
    exact ⟨.inl z, .inl w, hzw.trans (extGeodesicSegment_inl_inl z w).symm⟩
  · rcases exists_dirichletFace_eq_extGeodesicSegment_of_not_isBounded hg hne hb with
      ⟨z, ξ, hzξ⟩ | ⟨ξ, η, -, hξη⟩
    · exact ⟨.inl z, .inr ξ, hzξ⟩
    · exact ⟨.inr ξ, .inr η, hξη⟩

end TauCeti.UpperHalfPlane
