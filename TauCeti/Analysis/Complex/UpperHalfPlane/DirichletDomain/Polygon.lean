/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.DirichletDomain.Finite
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Basic
public import TauCeti.MeasureTheory.Group.DirichletDomain.Faces
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.HalfPlaneIntersection

/-!
# Compact Dirichlet polygons

A bounded hyperbolic Dirichlet domain of a properly discontinuous action on `ℍ` is the carrier of
a compact convex polygon. Each side of the polygon is a Dirichlet face `dirichletFace p g`: the
part of the domain on the perpendicular bisector of the centre `p` and a translate `g • p ≠ p`,
with the domain on the side of `p`. In particular, for an isometric action with compact orbit
space every Dirichlet domain is a compact convex polygon. This enumerates the vertices and sides
of a compact Dirichlet polygon.

The statements combine the finite bisector descriptions of
`TauCeti.UpperHalfPlane.exists_finset_dirichletDomain_eq_iInter_closure_leftHalfPlane` with
`TauCeti.UpperHalfPlane.exists_compactConvexPolygon_carrier_eq_iInter_closure_leftHalfPlane`.

## Main results

* `TauCeti.UpperHalfPlane.exists_compactConvexPolygon_carrier_eq_dirichletDomain`: a bounded
  Dirichlet domain is a compact convex polygon whose sides are Dirichlet faces.
* `TauCeti.UpperHalfPlane.exists_compactConvexPolygon_carrier_eq_dirichletDomain_of_compactSpace`:
  the same for every Dirichlet domain of an isometric action with compact orbit space.

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

end TauCeti.UpperHalfPlane
