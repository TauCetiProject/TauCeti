/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Sides
public import TauCeti.Analysis.Complex.UpperHalfPlane.Parabola
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.GaussBonnet
import Mathlib.Analysis.Convex.GaugeRescale

/-!
# Compact hyperbolic polygons are closed disks

A compact convex hyperbolic polygon is homeomorphic to the closed complex unit disk.
The homeomorphism identifies its interior with the open disk and the union of its sides
with the unit circle. Thus the polygon is a genuine closed two-cell, with its geometric
sides as the boundary on which side identifications can be attached.

Parabolic coordinates turn the polygon into a compact Euclidean convex set with nonempty
interior. We apply Mathlib's
`exists_homeomorph_image_interior_closure_frontier_eq_unitBall` (gauge rescaling, by
Yury Kudryashov), rather than choosing a triangulation or invoking surface classification.
No assertion about quotients or ideal vertices is made here.
-/

public section

noncomputable section

open Set Metric Topology UpperHalfPlane

namespace TauCeti.UpperHalfPlane

namespace ConvexPolygon

variable {n : ℕ} [NeZero n] (P : ConvexPolygon n)

/-- A convex hyperbolic polygon has a convex image in parabolic coordinates, including when
some of its vertices are ideal. -/
theorem convex_parabolaMap_image_carrier : Convex ℝ (parabolaMap '' P.carrier) := by
  rw [P.carrier_def]
  exact convex_parabolaMap_image_iInter_closure_leftHalfPlane P.sideGeodesic

end ConvexPolygon

namespace CompactConvexPolygon

variable {n : ℕ} [NeZero n] (P : CompactConvexPolygon n)

/-- **A compact hyperbolic polygon is a closed disk, with its sides as boundary.** There is a
homeomorphism carrying precisely the interior points to the open unit disk and precisely the
points on sides to the unit circle. In particular the boundary correspondence is with the
actual geometric sides, not an unspecified topological circle. -/
theorem exists_homeomorph_closedBall :
    ∃ e : P.carrier ≃ₜ closedBall (0 : ℂ) 1,
      (∀ z, (e z : ℂ) ∈ ball (0 : ℂ) 1 ↔ (z : ℍ) ∈ interior P.carrier) ∧
      (∀ z, (e z : ℂ) ∈ sphere (0 : ℂ) 1 ↔ ∃ i, (z : ℍ) ∈ P.side i) := by
  let s : Set ℂ := parabolaMap '' P.carrier
  have hf := isOpenEmbedding_parabolaMap
  have hc : Convex ℝ s := by
    simpa only [carrier_toConvexPolygon] using P.toConvexPolygon.convex_parabolaMap_image_carrier
  have hcompact : IsCompact s := P.isCompact_carrier.image hf.continuous
  have hne : (interior s).Nonempty := by
    have hP : (interior P.carrier).Nonempty := by
      simpa only [carrier_toConvexPolygon] using P.toConvexPolygon.nonempty_interior_carrier
    exact (hP.image parabolaMap).mono (hf.isOpenMap.image_interior_subset P.carrier)
  obtain ⟨h, hi, hcl, hfr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hcompact.isBounded
  have hs : h '' s = closedBall (0 : ℂ) 1 := by
    rwa [hcompact.isClosed.closure_eq] at hcl
  have himage : (h ∘ parabolaMap) '' P.carrier = closedBall (0 : ℂ) 1 := by
    rw [image_comp]
    exact hs
  let e := ((h.isEmbedding.comp hf.isEmbedding).homeomorphImage P.carrier).trans
    (Homeomorph.setCongr himage)
  -- Restricting the ambient coordinate change and identifying its image with the disk
  -- does not change its forward function.
  have he (z : P.carrier) : (e z : ℂ) = h (parabolaMap z) := (rfl)
  have hpreint : parabolaMap ⁻¹' interior s = interior P.carrier := by
    rw [hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous,
      hf.injective.preimage_image]
  have hprefr : parabolaMap ⁻¹' frontier s = frontier P.carrier := by
    rw [hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous,
      hf.injective.preimage_image]
  have hboundary : frontier P.carrier = ⋃ i, P.side i := by
    simpa only [carrier_toConvexPolygon, side_toConvexPolygon] using
      P.toConvexPolygon.frontier_carrier
  refine ⟨e, fun z ↦ ?_, fun z ↦ ?_⟩
  · rw [he, ← hi, h.injective.mem_set_image]
    exact Set.ext_iff.mp hpreint z
  · rw [he, ← hfr, h.injective.mem_set_image]
    have hz := Set.ext_iff.mp hprefr (z : ℍ)
    rwa [hboundary, mem_iUnion] at hz

end CompactConvexPolygon

end TauCeti.UpperHalfPlane
