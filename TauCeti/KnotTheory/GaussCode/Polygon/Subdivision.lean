/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Polygon.Subdivision
public import TauCeti.KnotTheory.GaussCode.Polygon.Basic

/-!
# Subdividing an edge does not change the Gauss code of a polygonal knot

Subdividing an edge of a polygonal knot `poly` at one of its points `c`,
`poly.insertVertex i c`, is the degenerate Δ-move
`TauCeti.SimplePolygon.IsElementaryMove.subdivide`. It does not move the knot, so it should not
change its diagram. This file proves that it does not change the based oriented Gauss code read
off from a regular projection (`Polygon.gaussCode`): when the projection along `d` is regular both
before and after subdividing, the two Gauss codes are equal
(`Polygon.gaussCode_insertVertex`). The projection after subdividing is regular exactly when it
is regular before and `c` is not a double point
(`Polygon.isRegularProjection_insertVertex_edgePath_iff`).

The number of crossings of `Polygon.gaussCode` is computed from the double points of the
polygon, so the two codes have equal but not definitionally equal numbers of crossings, and the
equality is stated for the codes paired with their numbers of crossings.

The proof compares the two traversals through the increasing change of time
`Polygon.exists_strictMono_boundaryParam_insertVertex_edgePath`. It carries the crossing times of
`poly` onto those of the subdivided polygon in increasing order, so the visits correspond, with
the same partners (`Polygon.visitTime_cast_eq_of_strictMono`,
`Polygon.gaussCode_partner_cast_eq_of_strictMono`), the same over/under data and crossings
numbered in the same order. The edges
through a crossing keep their directions up to positive factors, so the crossing signs agree.

## Main results

* `Polygon.gaussCode_insertVertex`: subdividing an edge of a polygonal knot does not change the
  Gauss code of a regular projection.

## References

* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, for Δ-moves and regular projections of polygonal knots.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1, for
  knot diagrams obtained from projections in general position.
-/

public section

open Set Function AffineMap Module TauCeti

namespace Polygon

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P] {n : ℕ} [NeZero n]
  {poly : Polygon P n} {p₀ : P} {d : V}

/-- **Subdividing an edge does not change the Gauss code.** Let `poly` be a simple polygon in a
three-dimensional real affine space, and `c` a point of its edge `i` such that the polygon
`poly.insertVertex i c`, with `c` inserted as a new vertex after vertex `i`, is still simple. If
the projection along `d` is regular for both polygons, then their Gauss codes are equal. The
numbers of crossings agree, and the codes are compared together with them. -/
theorem gaussCode_insertVertex (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {i : Fin n} {c : P}
    (hc : c ∈ poly.edgeSet ℝ i) (hs' : (poly.insertVertex i c).IsSimple ℝ)
    (hπ' : (poly.insertVertex i c).IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (b : Basis (Fin 3) ℝ V) :
    (⟨_, gaussCode hs' hπ' b⟩ : Σ m, BasedOrientedGaussCode m) = ⟨_, gaussCode hs hπ b⟩ := by
  rw [edgeSet_eq_image_edgePath] at hc
  obtain ⟨s, hs01, rfl⟩ := hc
  have hs01' := mem_Ioo_of_hasNondegenerateEdges_insertVertex_edgePath poly i hs01
    hs'.hasNondegenerateEdges
  obtain ⟨φ, hφ, hφt⟩ := exists_strictMono_boundaryParam_insertVertex_edgePath poly i hs01'
  set poly' := poly.insertVertex i (poly.edgePath ℝ i s)
  set π := projAlong ℝ p₀ d
  set D := gaussCode hs hπ b
  set D' := gaussCode hs' hπ' b
  have hb : poly'.boundary ℝ = poly.boundary ℝ := boundary_insertVertex_edgePath poly i hs01
  have hDP : poly'.doublePoints ℝ π = poly.doublePoints ℝ π :=
    doublePoints_insertVertex_edgePath poly i π hs01
  have hm : (poly.doublePoints ℝ π).ncard / 2 = (poly'.doublePoints ℝ π).ncard / 2 := by rw [hDP]
  have h2 : 2 * ((poly.doublePoints ℝ π).ncard / 2) = 2 * ((poly'.doublePoints ℝ π).ncard / 2) := by
    rw [hm]
  -- The change of time carries the visits of `poly` to those of `poly'`, with their partners.
  have hφt' (t) (ht : t ∈ Ico (0 : ℝ) n) := And.intro (hφt t ht).1 (hφt t ht).2.1
  have hvt := visitTime_cast_eq_of_strictMono hs hπ hs' hπ' hb hφ hφt' h2
  have hpartner := gaussCode_partner_cast_eq_of_strictMono b hs hπ hs' hπ' hb hφ hφt' h2
  have hmem (j) : visitTime hs hπ j ∈ Ico (0 : ℝ) n :=
    (mem_crossingTimes.1 (visitTime_mem_crossingTimes hs hπ j)).1
  have hbp (j) : poly'.boundaryParam (visitTime hs' hπ' (Fin.cast h2 j)) =
      poly.boundaryParam (visitTime hs hπ j) := by
    rw [hvt, (hφt _ (hmem j)).2.1]
  have hvt' (j) : visitTime hs' hπ' (D'.partner.val (Fin.cast h2 j)) =
      φ (visitTime hs hπ (D.partner.val j)) := by
    rw [hpartner, hvt]
  have hbp' (j) : poly'.boundaryParam (visitTime hs' hπ' (D'.partner.val (Fin.cast h2 j))) =
      poly.boundaryParam (visitTime hs hπ (D.partner.val j)) := by
    rw [hpartner, hbp]
  have hover (j) : D'.over (Fin.cast h2 j) = D.over j := by
    rw [Bool.eq_iff_iff, gaussCode_over_eq_true_iff, gaussCode_over_eq_true_iff, hbp, hbp']
  -- The crossing signs agree at an over visit.
  have hsign (j) (hj : D.over j = true) :
      D'.sign (D'.visit (Fin.cast h2 j)) = D.sign (D.visit j) := by
    have hj' : D'.over (Fin.cast h2 j) = true := by rw [hover, hj]
    obtain ⟨-, -, r, hr, hdir⟩ := hφt _ (hmem j)
    obtain ⟨-, -, r', hr', hdir'⟩ := hφt _ (hmem (D.partner.val j))
    -- The determinant of the edge directions is rescaled by the positive factor `r * r'`.
    have hdet (u w : V) : b.det ![r • u, r' • w, d] = r * r' * b.det ![u, w, d] := by
      have hv : ![r • u, r' • w, d] = fun k ↦ ![r, r', 1] k • ![u, w, d] k := by
        ext k
        fin_cases k <;> simp
      rw [hv, AlternatingMap.map_smul_univ, Fin.prod_univ_three]
      simp
    refine Units.ext ?_
    rw [gaussCode_sign_visit b hs' hπ' hj', gaussCode_sign_visit b hs hπ hj, hvt, hvt', hdir,
      hdir', hdet, sign_mul, sign_mul, sign_pos hr, sign_pos hr', one_mul, one_mul]
  refine (BasedOrientedGaussCode.sigma_mk_eq_of_visit_lt_visit_iff hm (fun j k ↦ ?_)
    (fun j ↦ (hover j).symm) (fun j hj ↦ (hsign j hj).symm)).symm
  rw [gaussCode_visit_lt_visit_iff, gaussCode_visit_lt_visit_iff, hvt, hvt, hvt', hvt',
    ← hφ.monotone.map_min, ← hφ.monotone.map_min, hφ.lt_iff_lt]

end Polygon
