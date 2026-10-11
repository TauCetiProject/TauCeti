/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.DirichletDomain.Basic
public import TauCeti.MeasureTheory.Group.DirichletDomain.Faces
import Mathlib.Topology.Order.Compact

/-!
# Geodesic faces of hyperbolic Dirichlet domains

An equality face whose index moves the centre is the intersection of the Dirichlet domain
with the corresponding perpendicular bisector. It is a geodesically convex boundary piece,
and its parameters on that bisector form a closed interval. In particular every nonempty
bounded face is a geodesic segment, possibly a singleton. This identifies the bounded boundary
pieces used as sides and vertices of Dirichlet polygons without assuming finite-sidedness.

The geometric statements apply to any family of translates in the upper half-plane. Proper
discontinuity is needed only for the exact boundary and interior characterizations, where it
ensures local finiteness of the distance constraints. Indices fixing the centre are explicitly
excluded from the boundary description: their equality face is the whole domain.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §3.2.

The construction uses `TauCeti.dirichletFace` and the perpendicular-bisector half-plane API.
-/

public section

open UpperHalfPlane Set
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

variable {G : Type*} [SMul G ℍ]

/-- A face indexed by an element moving the centre is cut out by its perpendicular bisector. -/
theorem dirichletFace_eq_inter_range_geodesicLine {p : ℍ} {g : G} (hg : g • p ≠ p) :
    dirichletFace p g =
      dirichletDomain G p ∩ range (geodesicLine (perpBisector p (g • p))) := by
  ext z
  simp only [mem_dirichletFace, mem_inter_iff,
    mem_range_geodesicLine_perpBisector_iff hg.symm]

/-- Equality faces of a hyperbolic Dirichlet domain are geodesically convex, including the
whole-domain face of an index fixing the centre. -/
theorem geodesicSegment_subset_dirichletFace {p z w : ℍ} {g : G}
    (hz : z ∈ dirichletFace p g) (hw : w ∈ dirichletFace p g) :
    geodesicSegment z w ⊆ dirichletFace p g := by
  obtain ⟨hzD, hzE⟩ := mem_dirichletFace.mp hz
  obtain ⟨hwD, hwE⟩ := mem_dirichletFace.mp hw
  intro u hu
  have huD := geodesicSegment_subset_dirichletDomain G hzD hwD hu
  exact mem_dirichletFace.mpr ⟨huD, le_antisymm (mem_dirichletDomain.mp huD g)
    (geodesicSegment_subset_setOf_dist_le_dist hzE.ge hwE.ge hu)⟩

/-- On its supporting bisector the face imposes just the Dirichlet-domain inequalities. -/
@[simp]
theorem preimage_geodesicLine_dirichletFace {p : ℍ} {g : G} (hg : g • p ≠ p) :
    geodesicLine (perpBisector p (g • p)) ⁻¹' dirichletFace p g =
      geodesicLine (perpBisector p (g • p)) ⁻¹' dirichletDomain G p := by
  rw [dirichletFace_eq_inter_range_geodesicLine hg, preimage_inter,
    preimage_range, inter_univ]

/-- The parameters of a nontrivial equality face on its supporting bisector form an interval. -/
theorem ordConnected_preimage_geodesicLine_dirichletFace {p : ℍ} {g : G}
    (hg : g • p ≠ p) :
    (geodesicLine (perpBisector p (g • p)) ⁻¹' dirichletFace p g).OrdConnected := by
  rw [preimage_geodesicLine_dirichletFace hg]
  exact ordConnected_preimage_geodesicLine_dirichletDomain G

/-- A face indexed by an element moving the centre lies on the boundary of the domain.
This conclusion does not require discreteness or an isometric group action. -/
theorem dirichletFace_subset_frontier {p : ℍ} {g : G} (hg : g • p ≠ p) :
    dirichletFace p g ⊆ frontier (dirichletDomain G p) := by
  intro z hz
  obtain ⟨hzD, hzE⟩ := mem_dirichletFace.mp hz
  refine ⟨subset_closure hzD, fun hzI ↦ ?_⟩
  have hd : Disjoint (interior (dirichletDomain G p))
      (rightHalfPlane (perpBisector p (g • p))) := by
    refine disjoint_left.mpr fun u huD huR ↦ ?_
    have hle := mem_dirichletDomain.mp (interior_subset huD) g
    have hlt := (mem_rightHalfPlane_perpBisector_iff hg.symm u).mp huR
    exact hlt.not_ge hle
  apply disjoint_left.mp (hd.closure_right isOpen_interior) hzI
  rw [closure_rightHalfPlane]
  exact Or.inr ((mem_range_geodesicLine_perpBisector_iff hg.symm z).mpr hzE)

/-- Every nonempty bounded face whose index moves the centre is an actual geodesic segment.
A face consisting of one point is allowed; no positive side length is asserted. -/
theorem exists_dirichletFace_eq_geodesicSegment {p : ℍ} {g : G} (hg : g • p ≠ p)
    (hne : (dirichletFace p g).Nonempty) (hb : Bornology.IsBounded (dirichletFace p g)) :
    ∃ z w : ℍ, dirichletFace p g = geodesicSegment z w := by
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
  have hcompact : IsCompact S :=
    (isometry_geodesicLine k).isClosedEmbedding.isCompact_preimage
      (Metric.isCompact_of_isClosed_isBounded (isClosed_dirichletFace p g) hb)
  have hconn : IsConnected S :=
    ⟨hS, (ordConnected_preimage_geodesicLine_dirichletFace hg).isPreconnected⟩
  have hab := eq_Icc_of_connected_compact hconn hcompact
  refine ⟨geodesicLine k (sInf S), geodesicLine k (sSup S), ?_⟩
  rw [geodesicSegment_geodesicLine, uIcc_of_le (nonempty_Icc.mp (hab ▸ hS)),
    ← hab, himage]

variable [ProperlyDiscontinuousSMul G ℍ]

/-- The boundary is exactly the union of the faces indexed by elements moving the centre. -/
theorem frontier_dirichletDomain_eq_iUnion_dirichletFace {p : ℍ} :
    frontier (dirichletDomain G p) = ⋃ g : {g : G // g • p ≠ p}, dirichletFace p g.1 := by
  apply subset_antisymm (frontier_dirichletDomain_subset_iUnion_dirichletFace p)
  exact iUnion_subset fun g ↦ dirichletFace_subset_frontier g.2

/-- A point is in the interior exactly when all constraints from indices moving the centre
are strict. Local finiteness of the constraints is essential for the reverse implication. -/
@[simp]
theorem mem_interior_dirichletDomain_iff {p z : ℍ} :
    z ∈ interior (dirichletDomain G p) ↔
      ∀ g : G, g • p ≠ p → dist z p < dist z (g • p) := by
  refine ⟨fun hz g hg ↦ ?_, mem_interior_dirichletDomain_of_forall_dist_lt⟩
  have hzD := interior_subset hz
  refine lt_of_le_of_ne (mem_dirichletDomain.mp hzD g) fun he ↦ ?_
  exact (dirichletFace_subset_frontier hg (mem_dirichletFace.mpr ⟨hzD, he⟩)).2 hz

end TauCeti.UpperHalfPlane
