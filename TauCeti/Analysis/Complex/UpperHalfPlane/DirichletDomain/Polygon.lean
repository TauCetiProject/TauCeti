/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.DirichletDomain.Finite
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
public import TauCeti.MeasureTheory.Group.DirichletDomain.Faces
public import TauCeti.Topology.Algebra.GroupAction.FreeLocus
import TauCeti.Analysis.Complex.UpperHalfPlane.DirichletDomain.Faces
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Sides
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.HalfPlaneIntersection

/-!
# Compact Dirichlet polygons

A bounded hyperbolic Dirichlet domain of a properly discontinuous action on `ℍ` is the carrier of
a compact convex polygon. Each side of the polygon is a Dirichlet face `dirichletFace p g`: the
part of the domain on the perpendicular bisector of the centre `p` and a translate `g • p ≠ p`,
with the domain on the side of `p`. In particular, for an isometric action with compact orbit
space every Dirichlet domain is a compact convex polygon. This enumerates the vertices and sides
of a compact Dirichlet polygon.

Conversely, for any convex polygon, possibly with ideal vertices, whose carrier is a Dirichlet
domain, the sides are exactly the Dirichlet faces with two distinct points indexed by elements
moving the centre. A side lies in the boundary, which is covered by the locally finite faces, so
some face contains two of its points and hence lies on its supporting line.

The statements combine the finite bisector descriptions of
`TauCeti.UpperHalfPlane.exists_finset_dirichletDomain_eq_iInter_closure_leftHalfPlane` with
`TauCeti.UpperHalfPlane.exists_compactConvexPolygon_carrier_eq_iInter_closure_leftHalfPlane`.

## Main results

* `TauCeti.UpperHalfPlane.exists_compactConvexPolygon_carrier_eq_dirichletDomain`: a bounded
  Dirichlet domain is a compact convex polygon whose sides are Dirichlet faces.
* `TauCeti.UpperHalfPlane.exists_compactConvexPolygon_carrier_eq_dirichletDomain_of_compactSpace`:
  the same for every Dirichlet domain of an isometric action with compact orbit space.
* `TauCeti.UpperHalfPlane.ConvexPolygon.exists_side_eq_dirichletFace` and
  `TauCeti.UpperHalfPlane.ConvexPolygon.exists_side_eq_dirichletFace_of_nontrivial`: the sides of
  a Dirichlet polygon are its nondegenerate Dirichlet faces.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §3.2.
-/

public section

open Set UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

variable {G : Type*}

/-- **A bounded Dirichlet domain is a compact convex polygon.** For a properly discontinuous
action on `ℍ`, a bounded Dirichlet domain centred at `p` is the carrier of a compact convex
polygon. Each side is the Dirichlet face of an element `g` moving `p`, and the polygon lies on the
side of `p` of the perpendicular bisector of `p` and `g • p`. -/
theorem exists_compactConvexPolygon_carrier_eq_dirichletDomain [SMul G ℍ]
    [ProperlyDiscontinuousSMul G ℍ] {p : ℍ} (hb : Bornology.IsBounded (dirichletDomain G p)) :
    ∃ (n : ℕ) (_ : NeZero n) (P : CompactConvexPolygon n), P.carrier = dirichletDomain G p ∧
      ∀ i, ∃ g : G, p ≠ g • p ∧
        leftHalfPlane (geodesicBetween (P.vertex i) (P.vertex (i + 1))) =
          leftHalfPlane (perpBisector p (g • p)) ∧ P.side i = dirichletFace p g := by
  obtain ⟨s, hmove, hD⟩ := exists_finset_dirichletDomain_eq_iInter_closure_leftHalfPlane hb
  -- the centre lies strictly inside every bisector half-plane
  have hint : (interior (⋂ g ∈ s, closure (leftHalfPlane (perpBisector p (g • p))))).Nonempty := by
    refine ⟨p, ?_⟩
    simp only [Finset.interior_iInter, interior_closure_leftHalfPlane, mem_iInter₂]
    intro g hg
    rw [mem_leftHalfPlane_perpBisector_iff (hmove g hg), dist_self]
    exact dist_pos.2 (hmove g hg)
  obtain ⟨n, _, P, hP, hside⟩ := exists_compactConvexPolygon_carrier_eq_iInter_closure_leftHalfPlane
    s (fun g ↦ perpBisector p (g • p)) hint (hD ▸ hb)
  refine ⟨n, inferInstance, P, hP.trans hD.symm, fun i ↦ ?_⟩
  obtain ⟨g, hg, hl, hs⟩ := hside i
  refine ⟨g, hmove g hg, hl, ?_⟩
  ext z
  rw [hs, ← hD, mem_inter_iff, mem_range_geodesicLine_perpBisector_iff (hmove g hg),
    mem_dirichletFace]

variable (G)

/-- **Dirichlet polygons of cocompact actions.** For a properly discontinuous isometric action on
`ℍ` with compact orbit space, every Dirichlet domain is the carrier of a compact convex polygon
whose sides are Dirichlet faces, as in `exists_compactConvexPolygon_carrier_eq_dirichletDomain`. -/
theorem exists_compactConvexPolygon_carrier_eq_dirichletDomain_of_compactSpace [Group G]
    [MulAction G ℍ] [IsIsometricSMul G ℍ] [ProperlyDiscontinuousSMul G ℍ]
    [CompactSpace (MulAction.orbitRel.Quotient G ℍ)] (p : ℍ) :
    ∃ (n : ℕ) (_ : NeZero n) (P : CompactConvexPolygon n), P.carrier = dirichletDomain G p ∧
      ∀ i, ∃ g : G, p ≠ g • p ∧
        leftHalfPlane (geodesicBetween (P.vertex i) (P.vertex (i + 1))) =
          leftHalfPlane (perpBisector p (g • p)) ∧ P.side i = dirichletFace p g :=
  exists_compactConvexPolygon_carrier_eq_dirichletDomain
    (isCompact_dirichletDomain_of_compactSpace p).isBounded

/-! ### Sides of Dirichlet polygons are Dirichlet faces -/

section ConvexPolygon

variable {G} [SMul G ℍ] [ProperlyDiscontinuousSMul G ℍ] {n : ℕ} [NeZero n] {P : ConvexPolygon n}
  {p : ℍ}

/-- **Nondegenerate Dirichlet faces are sides.** If a convex polygon, possibly with ideal vertices,
is a Dirichlet domain, then every Dirichlet face with two distinct points, indexed by an element
moving the centre, is one of its sides. -/
theorem ConvexPolygon.exists_side_eq_dirichletFace_of_nontrivial
    (hP : P.carrier = dirichletDomain G p) {g : G} (hg : g • p ≠ p)
    (hne : (dirichletFace p g).Nontrivial) : ∃ j, P.side j = dirichletFace p g := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hne
  rw [dirichletFace_eq_inter_range_geodesicLine hg, ← hP] at hx hy ⊢
  -- interior points are strictly closer to `p`, so they are not on the bisector
  have hk : Disjoint (interior P.carrier) (range (geodesicLine (perpBisector p (g • p)))) := by
    rw [hP]
    refine disjoint_left.2 fun z hz hzk ↦ ?_
    exact (mem_interior_dirichletDomain_iff.1 hz g hg).ne
      ((mem_range_geodesicLine_perpBisector_iff hg.symm z).1 hzk)
  obtain ⟨j, hj⟩ := P.exists_range_sideGeodesic_eq hk hxy hx hy
  exact ⟨j, by rw [← hj, P.carrier_inter_range_sideGeodesic]⟩

/-- **Sides of a Dirichlet polygon are Dirichlet faces.** If a convex polygon, possibly with
ideal vertices, is a Dirichlet domain, then each of its sides is the Dirichlet face of an element
moving the centre. -/
theorem ConvexPolygon.exists_side_eq_dirichletFace (hP : P.carrier = dirichletDomain G p)
    (i : Fin n) : ∃ g : G, g • p ≠ p ∧ P.side i = dirichletFace p g := by
  obtain ⟨x, hx, y, hy, hxy⟩ := P.side_nontrivial i
  -- the segment `S` from `x` to `y` is an infinite bounded part of the side
  set S := geodesicSegment x y
  have hS : S ⊆ P.side i := fun z hz ↦ by
    rw [← P.carrier_inter_range_sideGeodesic]
    refine ⟨P.geodesicSegment_subset_carrier (P.side_subset_carrier i hx)
      (P.side_subset_carrier i hy) hz, ?_⟩
    rw [← range_geodesicLine_geodesicBetween_of_mem (P.side_subset_range_sideGeodesic i hx)
      (P.side_subset_range_sideGeodesic i hy) hxy]
    exact geodesicSegment_subset_range_geodesicLine x y hz
  have hinf : S.Infinite := by
    refine (((Icc_infinite (dist_pos.2 hxy)).image
      (geodesicLine_injective (geodesicBetween x y)).injOn)).mono ?_
    rintro _ ⟨t, ht, rfl⟩
    exact (mem_geodesicSegment_iff _ _ _).2 ⟨t, ht, rfl⟩
  -- `S` lies on the boundary, so it is covered by the finitely many faces meeting it; one of
  -- them contains two points of `S`
  obtain ⟨g, hg, hgS⟩ : ∃ g : G, g • p ≠ p ∧ (dirichletFace p g ∩ S).Nontrivial := by
    by_contra! hsub
    have hfin : {g : G | (dirichletFace p g ∩ S).Nonempty ∧ g • p ≠ p}.Finite :=
      (finite_setOf_dirichletFace_inter_nonempty p (isCompact_geodesicSegment x y).isBounded).subset
        fun g hg ↦ hg.1
    refine hinf ((hfin.biUnion fun g hg ↦
      (hsub g hg.2).finite).subset fun z hz ↦ ?_)
    have hzf : z ∈ frontier (dirichletDomain G p) :=
      hP ▸ P.side_subset_frontier_carrier i (hS hz)
    obtain ⟨⟨g', hg'⟩, hzg'⟩ :=
      mem_iUnion.1 (frontier_dirichletDomain_subset_iUnion_dirichletFace p hzf)
    exact mem_biUnion (x := g') ⟨⟨z, hzg', hz⟩, hg'⟩ ⟨hzg', hz⟩
  obtain ⟨j, hj⟩ := P.exists_side_eq_dirichletFace_of_nontrivial hP hg
    (hgS.mono inter_subset_left)
  refine ⟨g, hg, ?_⟩
  rw [← hj, P.eq_of_nontrivial_side_inter_side (i := i) (j := j) ?_]
  rw [hj, inter_comm]
  exact hgS.mono (inter_subset_inter_right _ hS)

end ConvexPolygon

section ConvexPolygon

variable {G} [Group G] [MulAction G ℍ] [ProperlyDiscontinuousSMul G ℍ]
  {n : ℕ} [NeZero n] {P : ConvexPolygon n} {p : ℍ}

/-- For a centre with trivial stabilizer, each side of a Dirichlet polygon is the Dirichlet face
of a unique element other than the identity. -/
theorem ConvexPolygon.existsUnique_side_eq_dirichletFace
    (hP : P.carrier = dirichletDomain G p) (hp : p ∈ TauCeti.freeLocus G ℍ) (i : Fin n) :
    ∃! g : G, g ≠ 1 ∧ P.side i = dirichletFace p g := by
  obtain ⟨g, hg, hi⟩ := P.exists_side_eq_dirichletFace hP i
  refine ⟨g, ⟨fun h ↦ hg (by rw [h, one_smul]), hi⟩, fun g' hg' ↦ ?_⟩
  refine eq_of_nontrivial_dirichletFace_inter hp hg'.1
    (fun h ↦ hg (by rw [h, one_smul])) ?_
  rw [← hi, ← hg'.2, inter_self]
  exact P.side_nontrivial i

end ConvexPolygon

end TauCeti.UpperHalfPlane
