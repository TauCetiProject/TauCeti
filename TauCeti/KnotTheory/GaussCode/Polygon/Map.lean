/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Orientation
public import TauCeti.KnotTheory.GaussCode.Polygon.Basic

/-!
# The Gauss code of a polygonal knot is natural

The Gauss code `Polygon.gaussCode hs hπ b` of a regular projection of a polygonal knot `poly`
along a direction `d` is read off from three pieces of data: the polygon, the direction `d` with
the origin of the projection, and the basis `b` orienting the ambient space. This file shows that
it depends on them only as it should.

* **Affine equivalences.** Moving the knot, the direction and the basis together by an affine
  equivalence `e` does not change the diagram: the Gauss code of `poly.map e` projected along
  `e.linear d`, oriented by `b.map e.linear`, is the Gauss code of `poly`
  (`Polygon.gaussCode_map`). The traversals of the two polygons pass through corresponding points
  at the same times (`Polygon.boundaryParam_map`), so they have the same crossing times
  (`Polygon.crossingTimes_map`), and `e` carries the over/under data and the oriented frames of
  the crossings along.
* **The orientation.** Only the orientation `b.orientation` matters: two bases defining the same
  orientation give the same Gauss code (`Polygon.gaussCode_eq_of_orientation_eq`).
* **The direction.** Only the ray of `d` matters, and not the origin of the projection:
  projecting along `c • d`, for `c > 0`, from any origin, gives the same Gauss code
  (`Polygon.gaussCode_smul`).

So the diagram of a regular projection of a polygonal knot in an oriented three-dimensional real
affine space depends only on the knot, the ray of the direction and the orientation, and is
transported by affine equivalences. For instance, projecting a polygonal knot along a direction
`d'` gives the same Gauss code as projecting its image under a rotation carrying `d'` to `d` along
`d`. This lets a comparison of the diagrams of polygonal knots along one fixed direction be applied
to projections along different directions (Burde and Zieschang, Chapter 1).

The numbers of crossings of the compared codes are computed from different sets of double points,
so they are equal but not definitionally equal, and the codes are compared together with them, as
in `Polygon.gaussCode_insertVertex`.

## Main results

* `Polygon.crossingTimes_map`: an affine map with injective linear part does not change the
  crossing times.
* `Polygon.gaussCode_map`: the Gauss code is invariant under affine equivalences of the ambient
  space, moving the direction and the basis along.
* `Polygon.gaussCode_eq_of_orientation_eq`: the Gauss code only depends on the orientation of the
  ambient space.
* `Polygon.gaussCode_smul`: the Gauss code only depends on the ray of the direction of the
  projection, and not on its origin.

## References

* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, for regular projections of polygonal knots.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1, for
  knot diagrams and the sign of a crossing.
-/

public section

open Set Function AffineMap Module TauCeti

namespace Polygon

variable {V V' P P' : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P] [AddCommGroup V']
  [Module ℝ V'] [AddTorsor V' P'] {n : ℕ} [NeZero n] {poly : Polygon P n} {p₀ : P} {d : V}

/-! ### Comparing two Gauss codes -/

/-- **Comparison of Gauss codes.** Let `g` be an injective map carrying the traversal of `poly` to
that of `poly'`, time by time. If `g` carries the fibres of the projection along `d` to those of
the projection along `d'`, the relation "lies above, seen from `d`" to "lies above, seen from
`d'`", and the orientation of the frames formed by two edge directions and `d` with respect to `b`
to that with respect to `b'`, then the two Gauss codes agree. -/
private theorem gaussCode_eq_of_boundaryParam_eq_comp {poly' : Polygon P' n} {q₀ : P'} {d' : V'}
    (hs : poly.IsSimple ℝ) (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (hs' : poly'.IsSimple ℝ) (hπ' : poly'.IsRegularProjection ℝ (projAlong ℝ q₀ d'))
    (b : Basis (Fin 3) ℝ V) (b' : Basis (Fin 3) ℝ V') {g : P → P'} (hg : Injective g)
    (hbp : ∀ t, poly'.boundaryParam t = g (poly.boundaryParam t))
    (hfib : ∀ x y, projAlong ℝ q₀ d' (g x) = projAlong ℝ q₀ d' (g y) ↔
      projAlong ℝ p₀ d x = projAlong ℝ p₀ d y)
    (hover : ∀ x y, (∃ c : ℝ, 0 < c ∧ c • d' = g x -ᵥ g y) ↔ ∃ c : ℝ, 0 < c ∧ c • d = x -ᵥ y)
    (hsign : ∀ i j : Fin n,
      SignType.sign (b'.det ![poly' (finRotate n i) -ᵥ poly' i,
        poly' (finRotate n j) -ᵥ poly' j, d']) =
      SignType.sign (b.det ![poly (finRotate n i) -ᵥ poly i, poly (finRotate n j) -ᵥ poly j, d])) :
    (⟨_, gaussCode hs' hπ' b'⟩ : Σ m, BasedOrientedGaussCode m) = ⟨_, gaussCode hs hπ b⟩ := by
  -- `g` carries the boundary and the double points of `poly` onto those of `poly'`.
  have hbd : poly'.boundary ℝ = g '' poly.boundary ℝ := by
    rw [← range_boundaryParam, ← range_boundaryParam, ← range_comp]
    exact congrArg range (funext hbp)
  have hDP : poly'.doublePoints ℝ (projAlong ℝ q₀ d') =
      g '' poly.doublePoints ℝ (projAlong ℝ p₀ d) := by
    rw [doublePoints_eq_image_of_boundary_eq_image hg hbd]
    exact congrArg _ (doublePoints_congr fun x _ y _ ↦ hfib x y)
  have hm : (poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2 =
      (poly'.doublePoints ℝ (projAlong ℝ q₀ d')).ncard / 2 := by
    rw [hDP, ncard_image_of_injective _ hg]
  have h2 : 2 * ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2) =
      2 * ((poly'.doublePoints ℝ (projAlong ℝ q₀ d')).ncard / 2) := by
    rw [hm]
  -- The two traversals have the same crossing times, hence their visits at the same times.
  have hct : poly'.crossingTimes q₀ d' = poly.crossingTimes p₀ d := by
    ext t
    rw [mem_crossingTimes, mem_crossingTimes, hbp, hDP, hg.mem_set_image]
  have hvt (j) : visitTime hs' hπ' (Fin.cast h2 j) = visitTime hs hπ j :=
    visitTime_cast_eq_of_crossingTimes_eq hs hπ hs' hπ' strictMono_id (by rw [hct, image_id])
      h2 j
  -- The partner visits correspond, since `g` carries partner points to partner points.
  have hpartner (j) : (gaussCode hs' hπ' b').partner.val (Fin.cast h2 j) =
      Fin.cast h2 ((gaussCode hs hπ b).partner.val j) :=
    gaussCode_partner_cast_eq_of_boundaryParam_eq b hs hπ b' hs' hπ' hg.injOn
      (fun _ hx ↦ hbd ▸ mem_image_of_mem g (doublePoints_subset_boundary hx))
      (fun x _ y _ ↦ (hfib x y).2) h2 (Equiv.refl _)
      (fun k ↦ by rw [hvt, hbp, Equiv.refl_apply]) j
  have hover' (j) : (gaussCode hs' hπ' b').over (Fin.cast h2 j) = (gaussCode hs hπ b).over j := by
    rw [Bool.eq_iff_iff, gaussCode_over_eq_true_iff, gaussCode_over_eq_true_iff, hpartner, hvt,
      hvt, hbp, hbp, hover]
  have hsign' (j) (hj : (gaussCode hs hπ b).over j = true) :
      (gaussCode hs' hπ' b').sign ((gaussCode hs' hπ' b').visit (Fin.cast h2 j)) =
        (gaussCode hs hπ b).sign ((gaussCode hs hπ b).visit j) := by
    refine Units.ext ?_
    rw [gaussCode_sign_visit b' hs' hπ' (by rw [hover', hj]), gaussCode_sign_visit b hs hπ hj,
      hpartner, hvt, hvt, hsign]
  refine (BasedOrientedGaussCode.sigma_mk_eq_of_visit_lt_visit_iff hm (fun j k ↦ ?_)
    (fun j ↦ (hover' j).symm) (fun j hj ↦ (hsign' j hj).symm)).symm
  rw [gaussCode_visit_lt_visit_iff, gaussCode_visit_lt_visit_iff, hpartner, hpartner, hvt, hvt,
    hvt, hvt]

/-! ### Affine maps -/

/-- **An affine map does not change the crossing times.** For an affine map `f` with injective
linear part, the traversal of `poly.map f` passes through double points of the projection along
`f.linear d` at the same times as the traversal of `poly` passes through double points of the
projection along `d`. -/
theorem crossingTimes_map {f : P →ᵃ[ℝ] P'} (hf : Injective f.linear) (q₀ : P') :
    (poly.map f).crossingTimes q₀ (f.linear d) = poly.crossingTimes p₀ d := by
  ext t
  rw [mem_crossingTimes, mem_crossingTimes, boundaryParam_map,
    doublePoints_map_projAlong hf q₀ p₀ d, ((linear_injective_iff f).1 hf).mem_set_image]

/-- **The Gauss code is invariant under affine equivalences.** Let `e` be an affine equivalence
between three-dimensional real affine spaces, and `poly` a simple polygon with a regular projection
along `d`. Then the Gauss code of its image `poly.map e`, projected along `e.linear d` and oriented
by the image `b.map e.linear` of the basis `b`, is the Gauss code of `poly`. The numbers of
crossings agree, and the codes are compared together with them. -/
theorem gaussCode_map (hs : poly.IsSimple ℝ) (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (e : P ≃ᵃ[ℝ] P') {q₀ : P'} (hs' : (poly.map e).IsSimple ℝ)
    (hπ' : (poly.map e).IsRegularProjection ℝ (projAlong ℝ q₀ (e.linear d)))
    (b : Basis (Fin 3) ℝ V) :
    (⟨_, gaussCode hs' hπ' (b.map e.linear)⟩ : Σ m, BasedOrientedGaussCode m) =
      ⟨_, gaussCode hs hπ b⟩ := by
  have hlin (x y : P) : e x -ᵥ e y = e.linear (x -ᵥ y) :=
    (e.toAffineMap.linear_apply_vsub x y).symm
  refine gaussCode_eq_of_boundaryParam_eq_comp hs hπ hs' hπ' b _ e.injective
    (boundaryParam_map e.toAffineMap poly)
    (fun x y ↦ projAlong_map_eq_projAlong_map_iff (f := e.toAffineMap) e.linear.injective q₀ p₀ d)
    (fun x y ↦ exists_congr fun c ↦ and_congr_right fun _ ↦ ?_) fun i j ↦ ?_
  · rw [hlin, ← LinearEquiv.map_smul, e.linear.injective.eq_iff]
  · simp only [map_apply, hlin, Basis.det_map]
    congr 3
    ext k
    fin_cases k <;> simp

/-! ### The orientation -/

/-- **The Gauss code only depends on the orientation.** Two bases `b` and `b'` defining the same
orientation of the ambient space give the same Gauss code. -/
theorem gaussCode_eq_of_orientation_eq (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {b b' : Basis (Fin 3) ℝ V}
    (h : b.orientation = b'.orientation) : gaussCode hs hπ b = gaussCode hs hπ b' := by
  have hpos : 0 < b'.det b := (b'.orientation_eq_iff_det_pos b).1 h.symm
  have := gaussCode_eq_of_boundaryParam_eq_comp hs hπ hs hπ b' b injective_id (fun _ ↦ rfl)
    (fun _ _ ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl) fun i j ↦ by
      rw [b'.det.eq_smul_basis_det b, smul_apply, smul_eq_mul, sign_mul, sign_pos hpos, one_mul]
  exact eq_of_heq (Sigma.mk.inj_iff.1 this).2

/-! ### The direction of the projection -/

/-- **The Gauss code only depends on the ray of the direction.** Projecting along `c • d`, for
`c > 0`, from an arbitrary origin `p₀'`, gives the same Gauss code as projecting along `d` from
`p₀`. The numbers of crossings agree, and the codes are compared together with them. -/
theorem gaussCode_smul (hs : poly.IsSimple ℝ) (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d))
    {c : ℝ} (hc : 0 < c) {p₀' : P} (hπ' : poly.IsRegularProjection ℝ (projAlong ℝ p₀' (c • d)))
    (b : Basis (Fin 3) ℝ V) :
    (⟨_, gaussCode hs hπ' b⟩ : Σ m, BasedOrientedGaussCode m) = ⟨_, gaussCode hs hπ b⟩ := by
  -- The multiples of `c • d` satisfying a condition stable under scaling by `c` are the
  -- multiples of `d` satisfying it.
  have hmul {v : V} {p : ℝ → Prop} (hp : ∀ a, p (a * c) ↔ p a) :
      (∃ a : ℝ, p a ∧ a • c • d = v) ↔ ∃ a : ℝ, p a ∧ a • d = v := by
    simp only [smul_smul]
    exact ⟨fun ⟨a, ha, h⟩ ↦ ⟨a * c, (hp a).2 ha, h⟩,
      fun ⟨a, ha, h⟩ ↦ ⟨a / c, (hp _).1 (by rwa [div_mul_cancel₀ a hc.ne']),
        by rwa [div_mul_cancel₀ a hc.ne']⟩⟩
  refine gaussCode_eq_of_boundaryParam_eq_comp hs hπ hs hπ' b b injective_id (fun _ ↦ rfl)
    (fun x y ↦ ?_) (fun x y ↦ hmul fun a ↦ mul_pos_iff_of_pos_right hc) fun i j ↦ ?_
  · simpa only [projAlong_eq_projAlong_iff, true_and, id_eq] using
      hmul (p := fun _ ↦ True) (v := x -ᵥ y) fun _ ↦ Iff.rfl
  · have hv : ![poly (finRotate n i) -ᵥ poly i, poly (finRotate n j) -ᵥ poly j, c • d] =
        update ![poly (finRotate n i) -ᵥ poly i, poly (finRotate n j) -ᵥ poly j, d] 2
          (c • ![poly (finRotate n i) -ᵥ poly i, poly (finRotate n j) -ᵥ poly j, d] 2) := by
      ext k
      fin_cases k <;> simp
    rw [hv, AlternatingMap.map_update_smul, update_eq_self, smul_eq_mul, sign_mul, sign_pos hc,
      one_mul]

end Polygon
