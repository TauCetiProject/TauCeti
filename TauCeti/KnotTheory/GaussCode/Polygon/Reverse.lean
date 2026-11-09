/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.GaussCode.Polygon.Basic

/-!
# Reversing a polygonal knot reverses its Gauss code

The reversal `poly.reverse` of a polygonal knot `poly`, whose vertex `i` is vertex `-i` of `poly`,
has the same edges as `poly` (`Polygon.boundary_reverse`) but runs through them in the opposite
direction, starting from the same vertex `0`: it is the same knot with the opposite orientation.
This file proves that its Gauss code is the reversal `TauCeti.BasedOrientedGaussCode.reverse` of
the Gauss code of `poly`, up to a relabelling of the crossings
(`Polygon.exists_gaussCode_reverse_eq_relabel_reverse`). So the two polygons have the same
unoriented Gauss code, up to relabelling the crossings
(`Polygon.exists_forgetOrientation_gaussCode_reverse_eq_relabel`): reading off the diagram of a
regular projection is compatible with forgetting the orientation of the knot.

Reversal keeps a polygon simple (`Polygon.isSimple_reverse_iff`) and a projection regular
(`Polygon.isRegularProjection_reverse_iff`). As for the cyclic relabelling of the vertices
(`Polygon.exists_gaussCode_rotate_eq_relabel_rotateBasepoint_pow`), the numbers of crossings of
the two codes are equal but not definitionally equal, and the codes are compared together with
them.

The traversal of `poly.reverse` at time `t` is the traversal of `poly` at time `-t`
(`Polygon.boundaryParam_reverse`). No crossing time is an integer, since no vertex is a double
point, so the change of time `t ↦ n - t` carries the crossing times of `poly` in `[0, n)` onto
those of `poly.reverse`, reversing their order: the `i`-th visit of `poly.reverse` is at the point
of the `i`-th visit from the end of `poly`. Corresponding visits are at the same point, so they
have the same over/under data. The two strands through a crossing both run in the opposite
direction, which does not change the orientation of the frame formed by their directions and the
direction of projection, so the crossing signs agree. This is the sign convention of Lickorish,
Chapter 1: the sign of a crossing of an oriented link does not change when the orientations of
both strands are reversed.

## Main results

* `Polygon.exists_gaussCode_reverse_eq_relabel_reverse`: the Gauss code of `poly.reverse` is the
  reversed Gauss code of `poly`, with the crossings relabelled.
* `Polygon.exists_forgetOrientation_gaussCode_reverse_eq_relabel`: the unoriented Gauss codes of
  `poly` and `poly.reverse` differ by a relabelling of the crossings.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1, for
  oriented link diagrams, the reverse of a knot, and the sign of a crossing.
* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, for regular projections of polygonal knots.
-/

public section

open Set Function Module TauCeti

namespace Polygon

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P] {n : ℕ} [NeZero n]
  {poly : Polygon P n} {p₀ : P} {d : V}

/-! ### The change of time -/

/-- The traversal of `poly.reverse` at time `n - t` is the traversal of `poly` at time `t`. -/
private theorem boundaryParam_reverse_natCast_sub (t : ℝ) :
    poly.reverse.boundaryParam (n - t) = poly.boundaryParam t := by
  rw [boundaryParam_reverse, neg_sub, poly.periodic_boundaryParam.sub_eq]

omit [Module ℝ V] in
/-- At time `n - t`, off the vertices, the reversal runs along an edge of `poly` in the opposite
direction to the edge along which `poly` runs at time `t`. -/
private theorem reverse_edge_vsub_natCast_sub {t : ℝ} (ht : Int.fract t ≠ 0) :
    poly.reverse (finRotate n (edgeIndexAt n (n - t))) -ᵥ poly.reverse (edgeIndexAt n (n - t)) =
      -(poly (finRotate n (edgeIndexAt n t)) -ᵥ poly (edgeIndexAt n t)) := by
  rw [periodic_edgeIndexAt.sub_eq', edgeIndexAt_neg ht]
  simp only [reverse_apply, Fin.finRotate_neg_finRotate, neg_neg, neg_vsub_eq_vsub_rev]

/-- The change of time `t ↦ n - t` carries the crossing times of `poly` onto those of
`poly.reverse`. -/
private theorem image_natCast_sub_crossingTimes
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) :
    (fun t ↦ (n : ℝ) - t) '' poly.crossingTimes p₀ d = poly.reverse.crossingTimes p₀ d := by
  have hDP : poly.reverse.doublePoints ℝ (projAlong ℝ p₀ d) =
      poly.doublePoints ℝ (projAlong ℝ p₀ d) :=
    doublePoints_eq_of_boundary_eq (boundary_reverse poly)
  -- A crossing time is positive, since it is not an integer.
  have hpos {q : Polygon P n} (hq : q.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {t : ℝ}
      (ht : t ∈ q.crossingTimes p₀ d) : 0 < t :=
    (mem_crossingTimes.1 ht).1.1.lt_of_ne' fun h ↦ by
      simpa [h] using (fract_mem_Ioo_of_mem_crossingTimes hq ht).1
  refine Subset.antisymm ?_ fun t' ht' ↦ ?_
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨⟨-, htn⟩, ht₂⟩ := mem_crossingTimes.1 ht
    have := hpos hπ ht
    exact mem_crossingTimes.2 ⟨⟨by linarith, by linarith⟩,
      by rw [boundaryParam_reverse_natCast_sub, hDP]; exact ht₂⟩
  · obtain ⟨⟨-, ht'n⟩, ht'₂⟩ := mem_crossingTimes.1 ht'
    have := hpos hπ.reverse ht'
    refine ⟨n - t', mem_crossingTimes.2 ⟨⟨by linarith, by linarith⟩, ?_⟩, sub_sub_cancel _ _⟩
    rw [← boundaryParam_reverse_natCast_sub, sub_sub_cancel, ← hDP]
    exact ht'₂

/-- **Visit times after reversal.** The `j`-th visit of `poly.reverse` is at time `n - t`, where
`t` is the time of the `j`-th visit from the end of `poly`. -/
private theorem visitTime_reverse (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) (hs' : poly.reverse.IsSimple ℝ)
    (hπ' : poly.reverse.IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (h : 2 * ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2) =
      2 * ((poly.reverse.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2)) (j) :
    visitTime hs' hπ' (Fin.cast h j) = n - visitTime hs hπ (Fin.rev j) := by
  have hf : StrictMono (visitTime hs' hπ' ∘ Fin.cast h) :=
    (strictMono_visitTime hs' hπ').comp (Fin.cast_strictMono h)
  have hg : StrictMono ((fun t ↦ (n : ℝ) - t) ∘ visitTime hs hπ ∘ Fin.rev) := fun i j hij ↦ by
    have := strictMono_visitTime hs hπ (Fin.rev_lt_rev.2 hij)
    simp only [comp_apply]
    linarith
  have hrange : range (visitTime hs' hπ' ∘ Fin.cast h) =
      range ((fun t ↦ (n : ℝ) - t) ∘ visitTime hs hπ ∘ Fin.rev) := by
    have hcast : Surjective (Fin.cast h) := fun x ↦ ⟨Fin.cast h.symm x, by simp⟩
    rw [range_comp, hcast.range_eq, image_univ, range_visitTime, range_comp, range_comp,
      Fin.rev_surjective.range_eq, image_univ, range_visitTime, image_natCast_sub_crossingTimes hπ]
  exact congrFun ((hf.range_inj_of_wellFoundedLT hg).1 hrange) j

/-! ### The Gauss code -/

/-- **Reversing a polygonal knot reverses its Gauss code.** Let `poly` be a simple polygon in a
three-dimensional real affine space, oriented by the basis `b`, and let the projection along `d`
be regular. Then the Gauss code of its reversal `poly.reverse`, which traverses the same knot in
the opposite direction from the same vertex, is the reversed Gauss code of `poly`, with the
crossings relabelled. The numbers of crossings agree, and the codes are compared together with
them. -/
theorem exists_gaussCode_reverse_eq_relabel_reverse (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) (b : Basis (Fin 3) ℝ V) :
    ∃ e : Equiv.Perm (Fin ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2)),
      (⟨_, gaussCode hs.reverse hπ.reverse b⟩ : Σ m, BasedOrientedGaussCode m) =
        ⟨_, (gaussCode hs hπ b).reverse.relabel e⟩ := by
  have hs' := hs.reverse
  have hπ' := hπ.reverse
  set π := projAlong ℝ p₀ d
  set D := gaussCode hs hπ b
  set D' := gaussCode hs' hπ' b
  have hb : poly.reverse.boundary ℝ = poly.boundary ℝ := boundary_reverse poly
  have hDP : poly.reverse.doublePoints ℝ π = poly.doublePoints ℝ π :=
    doublePoints_eq_of_boundary_eq hb
  have hm : (poly.doublePoints ℝ π).ncard / 2 = (poly.reverse.doublePoints ℝ π).ncard / 2 := by
    rw [hDP]
  have h2 : 2 * ((poly.doublePoints ℝ π).ncard / 2) =
      2 * ((poly.reverse.doublePoints ℝ π).ncard / 2) := by
    rw [hm]
  have hvt := visitTime_reverse hs hπ hs' hπ' h2
  -- Corresponding visits are at the same point.
  have hbp (j) : poly.reverse.boundaryParam (visitTime hs' hπ' (Fin.cast h2 j)) =
      poly.boundaryParam (visitTime hs hπ (Fin.rev j)) := by
    rw [hvt, boundaryParam_reverse_natCast_sub]
  -- Their partner visits correspond in the same way.
  have hpartner (j) :
      D'.partner.val (Fin.cast h2 j) = Fin.cast h2 (Fin.rev (D.partner.val (Fin.rev j))) := by
    simpa only [Fin.revPerm_symm, Fin.revPerm_apply] using
      gaussCode_partner_cast_eq_of_boundaryParam_eq b hs hπ b hs' hπ' (injOn_id _)
        (fun _ hx ↦ hb ▸ doublePoints_subset_boundary hx) (fun _ _ _ _ hxy ↦ hxy) h2 Fin.revPerm
        (fun j ↦ by rw [Fin.revPerm_apply, hbp, id_eq]) j
  have hvisit (i j) : D.visit (Fin.rev i) = D.visit (Fin.rev j) ↔
      D'.visit (Fin.cast h2 i) = D'.visit (Fin.cast h2 j) := by
    rw [gaussCode_visit_eq_visit_iff, gaussCode_visit_eq_visit_iff, hbp, hbp]
  have hover (i) : D.over (Fin.rev i) = D'.over (Fin.cast h2 i) := by
    rw [Bool.eq_iff_iff, gaussCode_over_eq_true_iff, gaussCode_over_eq_true_iff, hbp, hpartner,
      hbp, Fin.rev_rev]
  -- Both strands of a crossing run backwards, which keeps the crossing sign.
  have hdet (u w : V) : b.det ![-u, -w, d] = b.det ![u, w, d] := by
    simpa using b.det_smul_smul_vecCons (-1) (-1) u w d
  have hfract (j) : Int.fract (visitTime hs hπ j) ≠ 0 :=
    (fract_mem_Ioo_of_mem_crossingTimes hπ (visitTime_mem_crossingTimes hs hπ j)).1.ne'
  have hsign (i) (hi : D.over (Fin.rev i) = true) :
      D.sign (D.visit (Fin.rev i)) = D'.sign (D'.visit (Fin.cast h2 i)) := by
    have hi' : D'.over (Fin.cast h2 i) = true := by rw [← hover, hi]
    refine Units.ext ?_
    rw [gaussCode_sign_visit b hs hπ hi, gaussCode_sign_visit b hs' hπ' hi', hpartner, hvt, hvt,
      Fin.rev_rev, reverse_edge_vsub_natCast_sub (hfract _),
      reverse_edge_vsub_natCast_sub (hfract _), hdet]
  exact BasedOrientedGaussCode.exists_sigma_mk_eq_relabel_of_visit_eq_visit_iff hm
    (fun i j ↦ by simpa only [BasedOrientedGaussCode.visit_reverse] using hvisit i j)
    (fun i ↦ by simpa only [BasedOrientedGaussCode.over_reverse] using hover i)
    (fun i ↦ by simpa only [BasedOrientedGaussCode.over_reverse,
      BasedOrientedGaussCode.visit_reverse, BasedOrientedGaussCode.sign_reverse] using hsign i)

/-- **Reversing a polygonal knot keeps its unoriented Gauss code.** Under the hypotheses of
`Polygon.exists_gaussCode_reverse_eq_relabel_reverse`, the unoriented Gauss codes of `poly` and of
its reversal `poly.reverse` differ by a relabelling of the crossings. -/
theorem exists_forgetOrientation_gaussCode_reverse_eq_relabel (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) (b : Basis (Fin 3) ℝ V) :
    ∃ e : Equiv.Perm (Fin ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2)),
      (⟨_, (gaussCode hs.reverse hπ.reverse b).forgetOrientation⟩ :
          Σ m, BasedUnorientedGaussCode m) =
        ⟨_, (gaussCode hs hπ b).forgetOrientation.relabel e⟩ := by
  obtain ⟨e, h⟩ := exists_gaussCode_reverse_eq_relabel_reverse hs hπ b
  refine ⟨e, ?_⟩
  have := congrArg (fun D : Σ m, BasedOrientedGaussCode m ↦
    (⟨D.1, D.2.forgetOrientation⟩ : Σ m, BasedUnorientedGaussCode m)) h
  simpa only [← BasedOrientedGaussCode.reverse_relabel,
    BasedOrientedGaussCode.forgetOrientation_reverse,
    BasedUnorientedGaussCode.relabel_forgetOrientation] using this

end Polygon
