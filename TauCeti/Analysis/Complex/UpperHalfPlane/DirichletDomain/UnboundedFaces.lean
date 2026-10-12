/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.DirichletDomain.Faces
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.ExtSegment
public import TauCeti.Topology.Order.Interval

/-!
# Unbounded faces of hyperbolic Dirichlet domains

A nonempty unbounded equality face of a hyperbolic Dirichlet domain is either a geodesic ray or a
complete geodesic line. In the ray case the face has one finite endpoint and one ideal endpoint;
in the line case both endpoints are ideal. This supplies the unbounded sides and ideal vertices
needed when assembling a cuspidal Dirichlet polygon.

The result does not assume finite covolume or finite-sidedness. It applies to an individual face
for any family of translates of the centre: the face is a closed order-connected interval in its
supporting geodesic, and unboundedness determines which kind of extended segment it is.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §3.2.
-/

public section

open UpperHalfPlane Set
open scoped MatrixGroups OnePoint

namespace TauCeti.UpperHalfPlane

variable {G : Type*} [SMul G ℍ]

/-- Every nonempty unbounded equality face whose index moves the centre is either an extended
geodesic segment with one finite and one ideal endpoint, or a complete geodesic between two
distinct ideal endpoints. -/
theorem exists_dirichletFace_eq_extGeodesicSegment_of_not_isBounded
    {p : ℍ} {g : G} (hg : g • p ≠ p) (hne : (dirichletFace p g).Nonempty)
    (hunbounded : ¬ Bornology.IsBounded (dirichletFace p g)) :
    (∃ z : ℍ, ∃ ξ : OnePoint ℝ,
      dirichletFace p g = extGeodesicSegment (.inl z) (.inr ξ)) ∨
    (∃ ξ η : OnePoint ℝ, ξ ≠ η ∧
      dirichletFace p g = extGeodesicSegment (.inr ξ) (.inr η)) := by
  let k := perpBisector p (g • p)
  let S := geodesicLine k ⁻¹' dirichletFace p g
  have hsub : dirichletFace p g ⊆ range (geodesicLine k) := by
    rw [dirichletFace_eq_inter_range_geodesicLine hg]
    exact inter_subset_right
  have himage : geodesicLine k '' S = dirichletFace p g :=
    image_preimage_eq_of_subset hsub
  have hS : S.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨t, rfl⟩ := hsub hz
    exact ⟨t, hz⟩
  have hclosed : IsClosed S :=
    (isClosed_dirichletFace p g).preimage (isometry_geodesicLine k).continuous
  have hnotOrderBounded : ¬(BddBelow S ∧ BddAbove S) := by
    intro hbounded
    apply hunbounded
    rw [← himage]
    exact (isometry_geodesicLine k).lipschitzWith.isBounded_image
      (isBounded_iff_bddBelow_bddAbove.mpr hbounded)
  have hclassification :
      (∃ a, S = Ici a) ∨ (∃ a, S = Iic a) ∨ S = univ :=
    (ordConnected_preimage_geodesicLine_dirichletFace hg).eq_Ici_or_eq_Iic_or_eq_univ
      hS hclosed hnotOrderBounded
  rcases hclassification with ⟨a, hS⟩ | ⟨a, hS⟩ | hS
  · refine Or.inl ⟨geodesicLine k a, k • (∞ : OnePoint ℝ), ?_⟩
    rw [← himage, hS, geodesicLine_image_Ici]
  · refine Or.inl ⟨geodesicLine k a, k • ((0 : ℝ) : OnePoint ℝ), ?_⟩
    rw [← himage, hS, geodesicLine_image_Iic, extGeodesicSegment_comm]
  · refine Or.inr ⟨k • ((0 : ℝ) : OnePoint ℝ), k • (∞ : OnePoint ℝ),
      (MulAction.injective k).ne (OnePoint.coe_ne_infty (0 : ℝ)), ?_⟩
    rw [← himage, hS, image_univ, range_geodesicLine_eq_extGeodesicSegment]

end TauCeti.UpperHalfPlane
