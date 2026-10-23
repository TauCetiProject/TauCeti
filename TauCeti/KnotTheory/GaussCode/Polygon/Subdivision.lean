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
the same partners, the same over/under data and crossings numbered in the same order. The edges
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
  -- The change of time carries the crossing times of `poly` onto those of `poly'`.
  have hct : poly'.crossingTimes p₀ d = φ '' poly.crossingTimes p₀ d := by
    refine Subset.antisymm (fun t' ht' ↦ ?_) ?_
    · obtain ⟨ht'₁, ht'₂⟩ := mem_crossingTimes.1 ht'
      rw [hDP] at ht'₂
      obtain ⟨t, ht, hbt⟩ := exists_mem_Ico_boundaryParam_eq (doublePoints_subset_boundary ht'₂)
      refine ⟨t, mem_crossingTimes.2 ⟨ht, hbt ▸ ht'₂⟩, hs'.injOn_boundaryParam (hφt t ht).1 ht'₁ ?_⟩
      rw [(hφt t ht).2.1, hbt]
    · rintro _ ⟨t, ht, rfl⟩
      obtain ⟨ht₁, ht₂⟩ := mem_crossingTimes.1 ht
      exact mem_crossingTimes.2 ⟨(hφt t ht₁).1, by rw [(hφt t ht₁).2.1, hDP]; exact ht₂⟩
  -- So the visit times of `poly'` are those of `poly` after the change of time.
  have hvt (j) : visitTime hs' hπ' (Fin.cast h2 j) = φ (visitTime hs hπ j) := by
    have hf : StrictMono (visitTime hs' hπ' ∘ Fin.cast h2) :=
      (strictMono_visitTime hs' hπ').comp (Fin.cast_strictMono h2)
    have hrange : range (visitTime hs' hπ' ∘ Fin.cast h2) = range (φ ∘ visitTime hs hπ) := by
      have hcast : Surjective (Fin.cast h2) := fun x ↦ ⟨Fin.cast h2.symm x, by simp⟩
      rw [range_comp, range_comp, hcast.range_eq, image_univ, range_visitTime, range_visitTime,
        hct]
    exact congrFun ((hf.range_inj_of_wellFoundedLT (hφ.comp (strictMono_visitTime hs hπ))).1
      hrange) j
  have hmem (j) : visitTime hs hπ j ∈ Ico (0 : ℝ) n :=
    (mem_crossingTimes.1 (visitTime_mem_crossingTimes hs hπ j)).1
  have hbp (j) : poly'.boundaryParam (visitTime hs' hπ' (Fin.cast h2 j)) =
      poly.boundaryParam (visitTime hs hπ j) := by
    rw [hvt, (hφt _ (hmem j)).2.1]
  -- Partner visits correspond.
  have hpartner (j) : D'.partner.val (Fin.cast h2 j) = Fin.cast h2 (D.partner.val j) := by
    refine (strictMono_visitTime hs' hπ').injective (hs'.injOn_boundaryParam
      (mem_crossingTimes.1 (visitTime_mem_crossingTimes hs' hπ' _)).1
      (mem_crossingTimes.1 (visitTime_mem_crossingTimes hs' hπ' _)).1 ?_)
    rw [boundaryParam_visitTime_partner, hbp, hbp, boundaryParam_visitTime_partner]
    have hx := (mem_crossingTimes.1 (visitTime_mem_crossingTimes hs hπ j)).2
    have hx' : poly.boundaryParam (visitTime hs hπ j) ∈ poly'.doublePoints ℝ π := hDP ▸ hx
    refine hπ.eq_doublePointPartner (doublePoints_subset_boundary hx)
      (hb ▸ doublePointPartner_mem_boundary (doublePoints_subset_boundary hx'))
      (doublePointPartner_ne hx') (apply_doublePointPartner _)
  have hvt' (j) : visitTime hs' hπ' (D'.partner.val (Fin.cast h2 j)) =
      φ (visitTime hs hπ (D.partner.val j)) := by
    rw [hpartner, hvt]
  have hbp' (j) : poly'.boundaryParam (visitTime hs' hπ' (D'.partner.val (Fin.cast h2 j))) =
      poly.boundaryParam (visitTime hs hπ (D.partner.val j)) := by
    rw [hpartner, hbp]
  have hover (j) : D'.over (Fin.cast h2 j) = D.over j := by
    rw [Bool.eq_iff_iff, gaussCode_over_eq_true_iff, gaussCode_over_eq_true_iff, hbp, hbp']
  -- The crossing signs agree, first at an over visit and then at its partner.
  have hsign_over (j) (hj : D.over j = true) :
      D'.sign (D'.visit (Fin.cast h2 j)) = D.sign (D.visit j) := by
    have hj' : D'.over (Fin.cast h2 j) = true := by rw [hover, hj]
    obtain ⟨-, -, r, hr, hdir⟩ := hφt _ (hmem j)
    obtain ⟨-, -, r', hr', hdir'⟩ := hφt _ (hmem (D.partner.val j))
    -- The determinant of the edge directions is rescaled by the positive factor `r * r'`.
    have hdet (u w : V) : b.det ![r • u, r' • w, d] = r * r' * b.det ![u, w, d] := by
      simp only [Basis.det_apply, Matrix.det_fin_three, Basis.toMatrix_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_smul,
        Finsupp.smul_apply, smul_eq_mul]
      ring
    refine Units.ext ?_
    rw [gaussCode_sign_visit b hs' hπ' hj', gaussCode_sign_visit b hs hπ hj, hvt, hvt', hdir,
      hdir', hdet, sign_mul, sign_mul, sign_pos hr, sign_pos hr', one_mul, one_mul]
  have hsign (j) : D'.sign (D'.visit (Fin.cast h2 j)) = D.sign (D.visit j) := by
    cases hj : D.over j
    · have hp : D.over (D.partner.val j) = true := by rw [D.over_partner, hj, Bool.not_false]
      rw [← D.visit_partner, ← hsign_over _ hp, ← hpartner, D'.visit_partner]
    · exact hsign_over j hj
  refine (BasedOrientedGaussCode.sigma_mk_eq_of_visit_lt_visit_iff hm (fun j k ↦ ?_)
    (fun j ↦ (hover j).symm) (fun j ↦ (hsign j).symm)).symm
  rw [gaussCode_visit_lt_visit_iff, gaussCode_visit_lt_visit_iff, hvt, hvt, hvt', hvt',
    ← hφ.monotone.map_min, ← hφ.monotone.map_min, hφ.lt_iff_lt]

end Polygon
