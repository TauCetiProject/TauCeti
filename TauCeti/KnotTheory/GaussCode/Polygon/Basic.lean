/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Geometry.Polygon.DoublePoint
public import TauCeti.KnotTheory.GaussCode.Basic

/-!
# The Gauss code of a regular projection of a polygonal knot

A knot diagram is read off a polygonal knot `k ⊆ ℝ³` by projecting it to a plane in regular
position (Crowell and Fox, Chapter I). Traversing `k` from a base point, one meets each crossing of
the diagram twice, once on the over-strand and once on the under-strand, and records the crossings
in the order met: this is the Gauss code of the diagram. This file constructs it,
`Polygon.gaussCode`, for a simple polygon `poly : Polygon P n` in a three-dimensional real affine
space and a regular projection `Polygon.projAlong ℝ p₀ d` along a direction `d`
(`Polygon.IsRegularProjection`).

The traversal is the boundary parametrization `Polygon.boundaryParam`, starting at vertex `0` and
running along the edges in order. The visits are the *crossing times*
`Polygon.crossingTimes poly p₀ d`, the times in `[0, n)` at which the polygon passes through a
double point of the projection (`Polygon.doublePoints`); there are finitely many, and the `i`-th of
them in increasing order is `Polygon.visitTime hs hπ i`. The two visits of a crossing are the
times of a double point and of its partner (`Polygon.doublePointPartner`), and the crossings are
numbered in the order of their first visits. The polygon is viewed from the side into which `d`
points: at a crossing, the over-strand is the one whose point differs from the point on the other
strand by a positive multiple of `d` (`Polygon.gaussCode_over_eq_true_iff`).

The sign of a crossing compares the directions of its two strands with an orientation of the
ambient space, given by a basis `b`. At a crossing whose over- and under-strands run along edges
with directions `u` and `w`, the vectors `u`, `w`, `d` are linearly independent: crossings of a
regular projection are transverse (`Polygon.IsRegularProjection.linearIndependent_of_projAlong_eq`).
The crossing is positive exactly when `b.det ![u, w, d]` is positive
(`Polygon.gaussCode_sign_visit`). For the standard basis of `ℝ³` and `d` the third basis vector,
this is the right-hand rule of Lickorish, Chapter 1: seen from above, a counterclockwise quarter
turn takes the over-strand to the under-strand.

The resulting code can be passed to an oriented PD-code by
`TauCeti.BasedOrientedGaussCode.toOrientedPDCode`. That the resulting PD-code is planar, and that
regularly projected polygons are combinatorially equivalent exactly when their diagrams are related
by Reidemeister moves, are not proved here.

## Main definitions

* `Polygon.crossingTimes poly p₀ d`: the times in `[0, n)` at which the boundary parametrization
  passes through a double point of the projection along `d`.
* `Polygon.visitTime hs hπ`: the crossing times in increasing order.
* `Polygon.gaussCode hs hπ b`: the based oriented Gauss code of the regular projection.

## Main results

* `Polygon.range_visitTime` and `Polygon.strictMono_visitTime`: the visits are the crossing times,
  in increasing order.
* `Polygon.gaussCode_visit_eq_visit_iff`: two visits belong to the same crossing exactly when
  their points have the same projection.
* `Polygon.gaussCode_visit_lt_visit_iff`: the crossings are numbered in the order of their first
  visits.
* `Polygon.boundaryParam_visitTime_partner`: the partner visit is at the partner double point.
* `Polygon.gaussCode_over_eq_true_iff`: the over/under convention.
* `Polygon.gaussCode_sign_visit`: the sign of a crossing is the sign of `b.det ![u, w, d]`.
* `Polygon.visitTime_cast_eq_of_strictMono` and `Polygon.gaussCode_partner_cast_eq_of_strictMono`:
  an increasing change of time between the traversals of two simple polygons with the same boundary
  matches their visits and partner visits.
* `Polygon.gaussCode_partner_cast_eq_of_boundaryParam_eq`: visits of two simple polygons with the
  same boundary that are at the same points have partner visits at the same points.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Springer GTM 57 (1977), Chapter I,
  for regular projections and the crossings of a knot diagram.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1, for
  knot diagrams and crossing signs.
* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, for regular projections of polygonal knots.
-/

public section

open Set Function AffineMap Module TauCeti

namespace Polygon

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P] {n : ℕ}
  {poly : Polygon P n} {p₀ : P} {d : V}

/-! ### Crossing times -/

variable [NeZero n]

variable (poly p₀ d) in
/-- The **crossing times** of a polygon under the projection along `d`: the times in one period
`[0, n)` at which the boundary parametrization passes through a double point of the projection.
For a regular projection of a polygonal knot, these are the times at which a traversal of the
knot from vertex `0` meets the crossings of its diagram. -/
def crossingTimes : Set ℝ :=
  {t | t ∈ Ico (0 : ℝ) n ∧ poly.boundaryParam t ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d)}

/-- A crossing time is a time in `[0, n)` at which the polygon passes through a double point. -/
@[simp]
theorem mem_crossingTimes {t : ℝ} :
    t ∈ poly.crossingTimes p₀ d ↔
      t ∈ Ico (0 : ℝ) n ∧ poly.boundaryParam t ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d) :=
  Iff.rfl

/-- The crossing times lie in one period `[0, n)`. -/
theorem crossingTimes_subset_Ico : poly.crossingTimes p₀ d ⊆ Ico (0 : ℝ) n :=
  fun _ ht ↦ ht.1

/-- The boundary parametrization maps the crossing times onto the double points. -/
theorem image_boundaryParam_crossingTimes :
    poly.boundaryParam '' poly.crossingTimes p₀ d = poly.doublePoints ℝ (projAlong ℝ p₀ d) := by
  refine Subset.antisymm (image_subset_iff.2 fun t ht ↦ ht.2) fun x hx ↦ ?_
  obtain ⟨t, ht, rfl⟩ := exists_mem_Ico_boundaryParam_eq (doublePoints_subset_boundary hx)
  exact ⟨t, ⟨ht, hx⟩, rfl⟩

/-- For a simple polygon, there are as many crossing times as double points. -/
theorem ncard_crossingTimes (hs : poly.IsSimple ℝ) :
    (poly.crossingTimes p₀ d).ncard = (poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard := by
  rw [← image_boundaryParam_crossingTimes,
    (hs.injOn_boundaryParam.mono crossingTimes_subset_Ico).ncard_image]

/-- A regular projection of a simple polygon has finitely many crossing times. -/
theorem finite_crossingTimes (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) : (poly.crossingTimes p₀ d).Finite :=
  Finite.of_finite_image
    (by rw [image_boundaryParam_crossingTimes]; exact hπ.finite_doublePoints hs)
    (hs.injOn_boundaryParam.mono crossingTimes_subset_Ico)

variable (poly p₀ d) in
/-- The time in `[0, n)` at which the boundary parametrization reaches the partner of the point
reached at time `t`. -/
private noncomputable def partnerTime (t : ℝ) : ℝ :=
  (exists_mem_Ico_boundaryParam_eq
    (doublePointPartner_mem_boundary (π := projAlong ℝ p₀ d)
      (poly.boundaryParam_mem_boundary t))).choose

private theorem partnerTime_mem_Ico (t : ℝ) : partnerTime poly p₀ d t ∈ Ico (0 : ℝ) n :=
  (exists_mem_Ico_boundaryParam_eq
    (doublePointPartner_mem_boundary (π := projAlong ℝ p₀ d)
      (poly.boundaryParam_mem_boundary t))).choose_spec.1

private theorem boundaryParam_partnerTime (t : ℝ) :
    poly.boundaryParam (partnerTime poly p₀ d t) =
      poly.doublePointPartner ℝ (projAlong ℝ p₀ d) (poly.boundaryParam t) :=
  (exists_mem_Ico_boundaryParam_eq
    (doublePointPartner_mem_boundary (π := projAlong ℝ p₀ d)
      (poly.boundaryParam_mem_boundary t))).choose_spec.2

private theorem partnerTime_mem_crossingTimes {t : ℝ} (ht : t ∈ poly.crossingTimes p₀ d) :
    partnerTime poly p₀ d t ∈ poly.crossingTimes p₀ d :=
  ⟨partnerTime_mem_Ico t, by
    rw [boundaryParam_partnerTime]
    exact doublePointPartner_mem_doublePoints ht.2⟩

private theorem partnerTime_partnerTime (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) n) :
    partnerTime poly p₀ d (partnerTime poly p₀ d t) = t :=
  hs.injOn_boundaryParam (partnerTime_mem_Ico _) ht <| by
    rw [boundaryParam_partnerTime, boundaryParam_partnerTime, hπ.involutive_doublePointPartner]

private theorem partnerTime_ne {t : ℝ} (ht : t ∈ poly.crossingTimes p₀ d) :
    partnerTime poly p₀ d t ≠ t := fun h ↦
  doublePointPartner_ne ht.2 (by rw [← boundaryParam_partnerTime, h])

/-- The two times of the double points of a crossing differ by a nonzero multiple of `d`. -/
private theorem exists_smul_eq_vsub_partnerTime {t : ℝ} (ht : t ∈ poly.crossingTimes p₀ d) :
    ∃ a : ℝ, a ≠ 0 ∧
      a • d = poly.boundaryParam t -ᵥ poly.boundaryParam (partnerTime poly p₀ d t) := by
  rw [boundaryParam_partnerTime]
  obtain ⟨a, ha⟩ := projAlong_eq_projAlong_iff.1 (apply_doublePointPartner (R := ℝ)
    (π := projAlong ℝ p₀ d) (poly := poly) (poly.boundaryParam t)).symm
  refine ⟨a, ?_, ha⟩
  rintro rfl
  rw [zero_smul, eq_comm, vsub_eq_zero_iff_eq] at ha
  exact doublePointPartner_ne ht.2 ha.symm

/-- A crossing time is not a vertex time: its point lies in the interior of an edge. -/
private theorem fract_mem_Ioo (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {t : ℝ}
    (ht : t ∈ poly.crossingTimes p₀ d) : Int.fract t ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨(Int.fract_nonneg t).lt_of_ne fun h ↦ ?_, Int.fract_lt_one t⟩
  have hv := ht.2
  rw [boundaryParam_eq_edgePath_edgeIndexAt, ← h, edgePath, lineMap_apply_zero] at hv
  exact hπ.apply_notMem_doublePoints _ hv

/-- At a crossing time, the directions of the edges through the double point and its partner,
followed by `d`, are linearly independent. -/
private theorem linearIndependent_of_mem_crossingTimes (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {t : ℝ}
    (ht : t ∈ poly.crossingTimes p₀ d) :
    LinearIndependent ℝ ![poly (finRotate n (edgeIndexAt n t)) -ᵥ poly (edgeIndexAt n t),
      poly (finRotate n (edgeIndexAt n (partnerTime poly p₀ d t))) -ᵥ
        poly (edgeIndexAt n (partnerTime poly p₀ d t)), d] := by
  have ht' := partnerTime_mem_crossingTimes ht
  refine hπ.linearIndependent_of_projAlong_eq hs (fract_mem_Ioo hπ ht) (fract_mem_Ioo hπ ht') ?_ ?_
  · rw [← boundaryParam_eq_edgePath_edgeIndexAt, ← boundaryParam_eq_edgePath_edgeIndexAt]
    exact fun h ↦ partnerTime_ne ht (hs.injOn_boundaryParam ht'.1 ht.1 h.symm)
  · rw [← boundaryParam_eq_edgePath_edgeIndexAt, ← boundaryParam_eq_edgePath_edgeIndexAt,
      boundaryParam_partnerTime,
      apply_doublePointPartner (R := ℝ) (poly := poly) (π := projAlong ℝ p₀ d)]

/-! ### The Gauss code -/

variable (poly p₀ d) in
/-- Whether the point at time `t` lies over its partner, viewed from the side into which `d`
points. -/
private noncomputable def crossingOver (t : ℝ) : Bool :=
  open Classical in
  decide (∃ c : ℝ, 0 < c ∧
    c • d = poly.boundaryParam t -ᵥ poly.boundaryParam (partnerTime poly p₀ d t))

private theorem crossingOver_partnerTime (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {t : ℝ}
    (ht : t ∈ poly.crossingTimes p₀ d) :
    crossingOver poly p₀ d (partnerTime poly p₀ d t) = !crossingOver poly p₀ d t := by
  obtain ⟨a, ha₀, ha⟩ := exists_smul_eq_vsub_partnerTime ht
  have hd : d ≠ 0 := by
    rintro rfl
    rw [smul_zero, eq_comm, vsub_eq_zero_iff_eq] at ha
    exact partnerTime_ne ht (hs.injOn_boundaryParam (partnerTime_mem_Ico t) ht.1 ha.symm)
  have key (r : ℝ) : (∃ c : ℝ, 0 < c ∧ c • d = r • d) ↔ 0 < r :=
    ⟨fun ⟨c, hc, h⟩ ↦ smul_left_injective ℝ hd h ▸ hc, fun h ↦ ⟨r, h, rfl⟩⟩
  rw [crossingOver, crossingOver, partnerTime_partnerTime hs hπ ht.1,
    ← neg_vsub_eq_vsub_rev (poly.boundaryParam t), ← ha, ← neg_smul, key, key]
  rcases ha₀.lt_or_gt with h | h
  · simp [h, h.le]
  · simp [h, h.not_gt]

variable (b : Basis (Fin 3) ℝ V)

variable (poly p₀ d) in
/-- The sign of the crossing met at time `t`: positive when the directions of the over- and
under-strands, followed by `d`, are positively oriented with respect to `b`. -/
private noncomputable def crossingSign (t : ℝ) : ℤˣ :=
  if crossingOver poly p₀ d t then
    if 0 < b.det ![poly (finRotate n (edgeIndexAt n t)) -ᵥ poly (edgeIndexAt n t),
      poly (finRotate n (edgeIndexAt n (partnerTime poly p₀ d t))) -ᵥ
        poly (edgeIndexAt n (partnerTime poly p₀ d t)), d] then 1 else -1
  else
    if 0 < b.det ![poly (finRotate n (edgeIndexAt n (partnerTime poly p₀ d t))) -ᵥ
        poly (edgeIndexAt n (partnerTime poly p₀ d t)),
      poly (finRotate n (edgeIndexAt n t)) -ᵥ poly (edgeIndexAt n t), d] then 1 else -1

private theorem crossingSign_partnerTime (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {t : ℝ}
    (ht : t ∈ poly.crossingTimes p₀ d) :
    crossingSign poly p₀ d b (partnerTime poly p₀ d t) = crossingSign poly p₀ d b t := by
  rw [crossingSign, crossingSign, crossingOver_partnerTime hs hπ ht,
    partnerTime_partnerTime hs hπ ht.1]
  cases crossingOver poly p₀ d t <;> rfl

private theorem det_ne_zero_of_mem_crossingTimes (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {t : ℝ}
    (ht : t ∈ poly.crossingTimes p₀ d) :
    b.det ![poly (finRotate n (edgeIndexAt n t)) -ᵥ poly (edgeIndexAt n t),
      poly (finRotate n (edgeIndexAt n (partnerTime poly p₀ d t))) -ᵥ
        poly (edgeIndexAt n (partnerTime poly p₀ d t)), d] ≠ 0 := by
  have hli := linearIndependent_of_mem_crossingTimes hs hπ ht
  exact (b.is_basis_iff_det.1 ⟨hli, hli.span_eq_top_of_card_eq_finrank
    (by simp [finrank_eq_card_basis b])⟩).ne_zero

private theorem involutive_partnerTime (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) :
    Involutive fun t : poly.crossingTimes p₀ d ↦
      (⟨partnerTime poly p₀ d t, partnerTime_mem_crossingTimes t.2⟩ : poly.crossingTimes p₀ d) :=
  fun t ↦ Subtype.ext (partnerTime_partnerTime hs hπ t.2.1)

/-- The crossing times, paired by the partner map. -/
private noncomputable def crossingMatching (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) :
    PerfectMatching (poly.crossingTimes p₀ d) :=
  .mk ((involutive_partnerTime hs hπ).toPerm _)
    (fun t ↦ by rw [Involutive.coe_toPerm]; exact involutive_partnerTime hs hπ t)
    (fun t h ↦ partnerTime_ne t.2 <| by
      rw [Involutive.coe_toPerm] at h
      exact congrArg Subtype.val h)

private theorem coe_crossingMatching_apply (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) (t : poly.crossingTimes p₀ d) :
    ((crossingMatching hs hπ).val t : ℝ) = partnerTime poly p₀ d t := by
  rw [crossingMatching, PerfectMatching.val_mk, Involutive.coe_toPerm]

private theorem crossingOver_crossingMatching (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) (t : poly.crossingTimes p₀ d) :
    crossingOver poly p₀ d ((crossingMatching hs hπ).val t) = !crossingOver poly p₀ d t := by
  rw [coe_crossingMatching_apply]
  exact crossingOver_partnerTime hs hπ t.2

private theorem crossingSign_crossingMatching (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) (t : poly.crossingTimes p₀ d) :
    crossingSign poly p₀ d b ((crossingMatching hs hπ).val t) = crossingSign poly p₀ d b t := by
  rw [coe_crossingMatching_apply]
  exact crossingSign_partnerTime b hs hπ t.2

private theorem card_crossingTimes [Fintype (poly.crossingTimes p₀ d)] (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) :
    Fintype.card (poly.crossingTimes p₀ d) =
      2 * ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2) := by
  have hcard : Fintype.card (poly.crossingTimes p₀ d) =
      (poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ncard_crossingTimes hs]
  have heven := even_card_of_nonempty_perfectMatching _ ⟨crossingMatching hs hπ⟩
  rw [hcard] at heven ⊢
  exact (Nat.two_mul_div_two_of_even heven).symm

/-- The crossing times in increasing order. -/
private noncomputable def visitOrderIso (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) :
    Fin (2 * ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2)) ≃o poly.crossingTimes p₀ d :=
  haveI := (finite_crossingTimes hs hπ).fintype
  Fintype.orderIsoFinOfCardEq _ (card_crossingTimes hs hπ)

/-- The time of the `i`-th visit of `Polygon.gaussCode`: the `i`-th crossing time in increasing
order. -/
noncomputable def visitTime (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (i : Fin (2 * ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2))) : ℝ :=
  visitOrderIso hs hπ i

/-- **The Gauss code of a regular projection of a polygonal knot.** For a simple polygon `poly`
in a three-dimensional real affine space, oriented by the basis `b`, and a regular projection
along `d`, this is the based oriented Gauss code read off by traversing the boundary from
vertex `0`. Its visits are the crossing times in increasing order, the two visits of a crossing
are at a double point and its partner, and the crossings are numbered in the order of their first
visits. A visit is over when its point lies above the partner point, viewed from the side into
which `d` points, and a crossing is positive when the directions of its over- and under-strands,
followed by `d`, are positively oriented. The number of crossings is half the number of double
points. -/
noncomputable def gaussCode (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) (b : Basis (Fin 3) ℝ V) :
    BasedOrientedGaussCode ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2) :=
  haveI := (finite_crossingTimes hs hπ).fintype
  BasedOrientedGaussCode.ofPerfectMatching (card_crossingTimes hs hπ) (crossingMatching hs hπ)
    (fun t ↦ crossingOver poly p₀ d t)
    (crossingOver_crossingMatching hs hπ)
    (fun t ↦ crossingSign poly p₀ d b t)

variable (hs : poly.IsSimple ℝ) (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d))

private theorem gaussCode_eq [Fintype (poly.crossingTimes p₀ d)] :
    gaussCode hs hπ b = BasedOrientedGaussCode.ofPerfectMatching (card_crossingTimes hs hπ)
      (crossingMatching hs hπ) (fun t ↦ crossingOver poly p₀ d t)
      (crossingOver_crossingMatching hs hπ) (fun t ↦ crossingSign poly p₀ d b t) := by
  obtain rfl : ‹Fintype (poly.crossingTimes p₀ d)› = (finite_crossingTimes hs hπ).fintype :=
    Subsingleton.elim _ _
  rfl

private theorem visitTime_eq [Fintype (poly.crossingTimes p₀ d)] (i) :
    visitTime hs hπ i = Fintype.orderIsoFinOfCardEq _ (card_crossingTimes hs hπ) i := by
  obtain rfl : ‹Fintype (poly.crossingTimes p₀ d)› = (finite_crossingTimes hs hπ).fintype :=
    Subsingleton.elim _ _
  rfl

/-- The visits are met in increasing order of time. -/
theorem strictMono_visitTime : StrictMono (visitTime hs hπ) :=
  fun _ _ h ↦ Subtype.coe_lt_coe.2 ((visitOrderIso hs hπ).strictMono h)

/-- The visit times are exactly the crossing times. -/
@[simp]
theorem range_visitTime : range (visitTime hs hπ) = poly.crossingTimes p₀ d := by
  have : visitTime hs hπ = Subtype.val ∘ visitOrderIso hs hπ := rfl
  rw [this, range_comp, (visitOrderIso hs hπ).range_eq, image_univ, Subtype.range_coe]

/-- Every visit time is a crossing time. -/
theorem visitTime_mem_crossingTimes (i) : visitTime hs hπ i ∈ poly.crossingTimes p₀ d :=
  range_visitTime hs hπ ▸ mem_range_self i

private theorem visitTime_partner (i) :
    visitTime hs hπ ((gaussCode hs hπ b).partner.val i) =
      partnerTime poly p₀ d (visitTime hs hπ i) := by
  simp only [visitTime, visitOrderIso, gaussCode,
    BasedOrientedGaussCode.orderIsoFinOfCardEq_ofPerfectMatching_partner,
    coe_crossingMatching_apply]

/-- The partner of a visit is at the partner of its double point. -/
theorem boundaryParam_visitTime_partner (i) :
    poly.boundaryParam (visitTime hs hπ ((gaussCode hs hπ b).partner.val i)) =
      poly.doublePointPartner ℝ (projAlong ℝ p₀ d) (poly.boundaryParam (visitTime hs hπ i)) := by
  rw [visitTime_partner, boundaryParam_partnerTime]

/-- Two visits belong to the same crossing exactly when their points have the same projection. -/
theorem gaussCode_visit_eq_visit_iff (i j) :
    (gaussCode hs hπ b).visit i = (gaussCode hs hπ b).visit j ↔
      projAlong ℝ p₀ d (poly.boundaryParam (visitTime hs hπ i)) =
        projAlong ℝ p₀ d (poly.boundaryParam (visitTime hs hπ j)) := by
  rw [BasedOrientedGaussCode.visit_eq_iff]
  constructor
  · rintro (rfl | rfl)
    · rfl
    · rw [boundaryParam_visitTime_partner,
        apply_doublePointPartner (R := ℝ) (poly := poly) (π := projAlong ℝ p₀ d)]
  · intro h
    by_cases heq : poly.boundaryParam (visitTime hs hπ j) = poly.boundaryParam (visitTime hs hπ i)
    · exact .inl ((strictMono_visitTime hs hπ).injective (hs.injOn_boundaryParam
        (visitTime_mem_crossingTimes hs hπ j).1 (visitTime_mem_crossingTimes hs hπ i).1 heq))
    · refine .inr ((strictMono_visitTime hs hπ).injective (hs.injOn_boundaryParam
        (visitTime_mem_crossingTimes hs hπ j).1 (visitTime_mem_crossingTimes hs hπ _).1 ?_))
      rw [boundaryParam_visitTime_partner]
      exact hπ.eq_doublePointPartner (poly.boundaryParam_mem_boundary _)
        (poly.boundaryParam_mem_boundary _) heq h.symm

/-- **Crossings are numbered in the order of their first visits.** The crossing met at visit `i`
has a smaller label than the one met at visit `j` exactly when the first visit time of the first
crossing is less than that of the second. -/
theorem gaussCode_visit_lt_visit_iff (i j) :
    (gaussCode hs hπ b).visit i < (gaussCode hs hπ b).visit j ↔
      min (visitTime hs hπ i) (visitTime hs hπ ((gaussCode hs hπ b).partner.val i)) <
        min (visitTime hs hπ j) (visitTime hs hπ ((gaussCode hs hπ b).partner.val j)) := by
  have : Fintype (poly.crossingTimes p₀ d) := (finite_crossingTimes hs hπ).fintype
  rw [visitTime_partner, visitTime_partner, gaussCode_eq,
    BasedOrientedGaussCode.ofPerfectMatching_visit_lt_visit_iff, visitTime_eq hs hπ,
    visitTime_eq hs hπ, ← coe_crossingMatching_apply hs hπ, ← coe_crossingMatching_apply hs hπ,
    ← (Subtype.mono_coe _).map_min, ← (Subtype.mono_coe _).map_min, Subtype.coe_lt_coe]

/-- **The over/under convention.** A visit is over exactly when its point is obtained from the
point of the partner visit by adding a positive multiple of `d`: the diagram is viewed from the
side into which `d` points. -/
theorem gaussCode_over_eq_true_iff (i) :
    (gaussCode hs hπ b).over i = true ↔ ∃ c : ℝ, 0 < c ∧
      c • d = poly.boundaryParam (visitTime hs hπ i) -ᵥ
        poly.boundaryParam (visitTime hs hπ ((gaussCode hs hπ b).partner.val i)) := by
  rw [visitTime_partner]
  simp only [gaussCode, BasedOrientedGaussCode.ofPerfectMatching_over, crossingOver,
    decide_eq_true_eq, visitTime, visitOrderIso]

/-- **The sign of a crossing.** At a crossing whose over-visit `i` runs along an edge with
direction `u` and whose under-visit runs along an edge with direction `w`, the crossing sign is the
sign of `b.det ![u, w, d]`, which is nonzero by transversality. -/
theorem gaussCode_sign_visit {i} (hi : (gaussCode hs hπ b).over i = true) :
    (((gaussCode hs hπ b).sign ((gaussCode hs hπ b).visit i) : ℤˣ) : ℤ) =
      SignType.sign (b.det
        ![poly (finRotate n (edgeIndexAt n (visitTime hs hπ i))) -ᵥ
            poly (edgeIndexAt n (visitTime hs hπ i)),
          poly (finRotate n
              (edgeIndexAt n (visitTime hs hπ ((gaussCode hs hπ b).partner.val i)))) -ᵥ
            poly (edgeIndexAt n (visitTime hs hπ ((gaussCode hs hπ b).partner.val i))), d]) := by
  have ht := visitTime_mem_crossingTimes hs hπ i
  have : Fintype (poly.crossingTimes p₀ d) := (finite_crossingTimes hs hπ).fintype
  have hover : crossingOver poly p₀ d (visitTime hs hπ i) = true := by
    rwa [gaussCode_eq, BasedOrientedGaussCode.ofPerfectMatching_over, ← visitTime_eq hs hπ] at hi
  have hdet := det_ne_zero_of_mem_crossingTimes b hs hπ ht
  rw [visitTime_partner, gaussCode_eq, BasedOrientedGaussCode.ofPerfectMatching_sign_visit _ _ _ _ _
    (crossingSign_crossingMatching b hs hπ), ← visitTime_eq hs hπ, crossingSign]
  rcases hdet.lt_or_gt with h | h
  · simp only [hover, h.not_gt, ↓reduceIte, sign_neg h]
    simp
  · simp only [hover, h, ↓reduceIte, sign_pos h]
    simp

/-! ### Changing the time of the traversal -/

section ChangeOfTime

variable {m : ℕ} [NeZero m] {poly' : Polygon P m} (hs' : poly'.IsSimple ℝ)
  (hπ' : poly'.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {φ : ℝ → ℝ}

/-- **Visit times under a change of time.** Let `poly'` be a simple polygon with the same boundary
as `poly`, and `φ` an increasing change of time carrying one period `[0, n)` of the boundary
parametrization of `poly` into one period `[0, m)` of that of `poly'`, through the same points.
Then `φ` carries each visit time of `poly` to the visit time of `poly'` with the same index, the
visits being identified by `Fin.cast h`. -/
theorem visitTime_cast_eq_of_strictMono (hb : poly'.boundary ℝ = poly.boundary ℝ)
    (hφ : StrictMono φ) (hφt : ∀ t ∈ Ico (0 : ℝ) n,
      φ t ∈ Ico (0 : ℝ) m ∧ poly'.boundaryParam (φ t) = poly.boundaryParam t)
    (h : 2 * ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2) =
      2 * ((poly'.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2)) (j) :
    visitTime hs' hπ' (Fin.cast h j) = φ (visitTime hs hπ j) := by
  have hDP : poly'.doublePoints ℝ (projAlong ℝ p₀ d) = poly.doublePoints ℝ (projAlong ℝ p₀ d) :=
    doublePoints_eq_of_boundary_eq hb
  -- The change of time carries the crossing times of `poly` onto those of `poly'`.
  have hct : poly'.crossingTimes p₀ d = φ '' poly.crossingTimes p₀ d := by
    refine Subset.antisymm (fun t' ht' ↦ ?_) ?_
    · obtain ⟨ht'₁, ht'₂⟩ := mem_crossingTimes.1 ht'
      rw [hDP] at ht'₂
      obtain ⟨t, ht, hbt⟩ := exists_mem_Ico_boundaryParam_eq (doublePoints_subset_boundary ht'₂)
      refine ⟨t, mem_crossingTimes.2 ⟨ht, hbt ▸ ht'₂⟩, hs'.injOn_boundaryParam (hφt t ht).1 ht'₁ ?_⟩
      rw [(hφt t ht).2, hbt]
    · rintro _ ⟨t, ht, rfl⟩
      obtain ⟨ht₁, ht₂⟩ := mem_crossingTimes.1 ht
      exact mem_crossingTimes.2 ⟨(hφt t ht₁).1, by rw [(hφt t ht₁).2, hDP]; exact ht₂⟩
  have hf : StrictMono (visitTime hs' hπ' ∘ Fin.cast h) :=
    (strictMono_visitTime hs' hπ').comp (Fin.cast_strictMono h)
  have hrange : range (visitTime hs' hπ' ∘ Fin.cast h) = range (φ ∘ visitTime hs hπ) := by
    have hcast : Surjective (Fin.cast h) := fun x ↦ ⟨Fin.cast h.symm x, by simp⟩
    rw [range_comp, range_comp, hcast.range_eq, image_univ, range_visitTime, range_visitTime, hct]
  exact congrFun ((hf.range_inj_of_wellFoundedLT (hφ.comp (strictMono_visitTime hs hπ))).1
    hrange) j

/-- **Partners of visits at the same points.** Let `poly'` be a simple polygon with the same
boundary as `poly`, and `σ` a permutation of the visits of `poly` such that the visit of `poly'`
identified by `Fin.cast h` with `j` is at the same point as the `σ j`-th visit of `poly`. Then the
partner visits correspond in the same way. -/
theorem gaussCode_partner_cast_eq_of_boundaryParam_eq (hb : poly'.boundary ℝ = poly.boundary ℝ)
    (h : 2 * ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2) =
      2 * ((poly'.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2))
    (σ : Equiv.Perm (Fin (2 * ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2))))
    (hbp : ∀ j, poly'.boundaryParam (visitTime hs' hπ' (Fin.cast h j)) =
      poly.boundaryParam (visitTime hs hπ (σ j))) (j) :
    (gaussCode hs' hπ' b).partner.val (Fin.cast h j) =
      Fin.cast h (σ.symm ((gaussCode hs hπ b).partner.val (σ j))) := by
  refine (strictMono_visitTime hs' hπ').injective (hs'.injOn_boundaryParam
    (visitTime_mem_crossingTimes hs' hπ' _).1 (visitTime_mem_crossingTimes hs' hπ' _).1 ?_)
  rw [boundaryParam_visitTime_partner, hbp, hbp, Equiv.apply_symm_apply,
    boundaryParam_visitTime_partner]
  have hx := (mem_crossingTimes.1 (visitTime_mem_crossingTimes hs hπ (σ j))).2
  have hx' : poly.boundaryParam (visitTime hs hπ (σ j)) ∈
      poly'.doublePoints ℝ (projAlong ℝ p₀ d) := by
    rw [doublePoints_eq_of_boundary_eq hb]
    exact hx
  exact hπ.eq_doublePointPartner (doublePoints_subset_boundary hx)
    (hb ▸ doublePointPartner_mem_boundary (doublePoints_subset_boundary hx'))
    (doublePointPartner_ne hx') (apply_doublePointPartner _)

/-- **Partners under a change of time.** Under the hypotheses of
`Polygon.visitTime_cast_eq_of_strictMono`, the visits of the Gauss codes of `poly` and `poly'`
identified by `Fin.cast h` have partner visits identified by `Fin.cast h`. -/
theorem gaussCode_partner_cast_eq_of_strictMono (hb : poly'.boundary ℝ = poly.boundary ℝ)
    (hφ : StrictMono φ) (hφt : ∀ t ∈ Ico (0 : ℝ) n,
      φ t ∈ Ico (0 : ℝ) m ∧ poly'.boundaryParam (φ t) = poly.boundaryParam t)
    (h : 2 * ((poly.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2) =
      2 * ((poly'.doublePoints ℝ (projAlong ℝ p₀ d)).ncard / 2)) (j) :
    (gaussCode hs' hπ' b).partner.val (Fin.cast h j) =
      Fin.cast h ((gaussCode hs hπ b).partner.val j) :=
  gaussCode_partner_cast_eq_of_boundaryParam_eq b hs hπ hs' hπ' hb h (Equiv.refl _)
    (fun k ↦ by rw [visitTime_cast_eq_of_strictMono hs hπ hs' hπ' hb hφ hφt,
      (hφt _ (visitTime_mem_crossingTimes hs hπ k).1).2, Equiv.refl_apply]) j

end ChangeOfTime

end Polygon
