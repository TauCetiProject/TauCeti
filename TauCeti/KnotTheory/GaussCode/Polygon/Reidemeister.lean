/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.GaussCode.PDCode.Basepoint
public import TauCeti.KnotTheory.GaussCode.Polygon.Rotate

/-!
# Relabelling a polygonal knot cyclically keeps its diagram up to Reidemeister equivalence

A regular projection of a simple polygon `poly` in a three-dimensional real affine space along a
direction `d` has a based oriented Gauss code `Polygon.gaussCode hs hπ b`, read by traversing the
polygon from its vertex `0`, and through `TauCeti.BasedOrientedGaussCode.toOrientedPDCode` an
oriented PD-code: the diagram of the projected knot. Comparing the diagrams of combinatorially
equivalent polygonal knots, as in Reidemeister's theorem, compares these PD-codes up to
Reidemeister equivalence (`TauCeti.OrientedPDCode.ReidemeisterEquiv`).

The cyclic relabelling `poly.rotate`, an elementary move of polygonal knots, does not move the
knot, but it starts the traversal at another vertex. Its Gauss code is a basepoint rotation of
that of `poly` with the crossings relabelled
(`Polygon.exists_gaussCode_rotate_eq_relabel_rotateBasepoint_pow`). Such a change only relabels
the half-edges and crossings of the PD-code
(`TauCeti.BasedOrientedGaussCode.toOrientedPDCode_rotateBasepoint`), so the two diagrams are
Reidemeister equivalent (`Polygon.reidemeisterEquiv_toOrientedPDCode_gaussCode_rotate`).

The other elementary moves that create no crossings, subdividing an edge
(`Polygon.gaussCode_insertVertex`) and a Δ-move whose moved edges meet no crossing
(`Polygon.gaussCode_insertVertex_of_disjoint`), leave the Gauss code itself unchanged, and give
Reidemeister equivalent diagrams through
`TauCeti.BasedOrientedGaussCode.reidemeisterEquiv_toOrientedPDCode_of_sigma_eq`.

## Main results

* `Polygon.reidemeisterEquiv_toOrientedPDCode_gaussCode_rotate`: relabelling the vertices of a
  polygonal knot cyclically gives a Reidemeister equivalent diagram.

## References

* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, for the elementary moves on polygonal knots and their regular projections.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1, for
  knot diagrams and Reidemeister moves.
-/

public section

open Module TauCeti

namespace Polygon

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P] {n : ℕ} [NeZero n]
  {poly : Polygon P n} {p₀ : P} {d : V}

/-- **Relabelling the vertices gives a Reidemeister equivalent diagram.** Let `poly` be a simple
polygon in a three-dimensional real affine space with a regular projection along `d`. The diagrams
of `poly` and of its cyclic relabelling `poly.rotate`, the oriented PD-codes of their Gauss codes,
are Reidemeister equivalent. -/
theorem reidemeisterEquiv_toOrientedPDCode_gaussCode_rotate (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) (b : Basis (Fin 3) ℝ V) :
    OrientedPDCode.ReidemeisterEquiv
      (gaussCode ((isSimple_rotate_iff poly).2 hs) (isRegularProjection_rotate_iff.2 hπ)
        b).toOrientedPDCode
      (gaussCode hs hπ b).toOrientedPDCode := by
  obtain ⟨k, e, h⟩ := exists_gaussCode_rotate_eq_relabel_rotateBasepoint_pow hs hπ b
  refine (BasedOrientedGaussCode.reidemeisterEquiv_toOrientedPDCode_of_sigma_eq h).trans <|
    (BasedOrientedGaussCode.reidemeisterEquiv_toOrientedPDCode_relabel _ e).trans ?_
  exact BasedOrientedGaussCode.reidemeisterEquiv_toOrientedPDCode_of_forgetBasepoint_eq
    (BasedOrientedGaussCode.forgetBasepoint_rotateBasepoint_pow _ k)

end Polygon
