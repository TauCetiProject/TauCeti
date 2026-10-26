/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Polygon.RegularProjection
public import TauCeti.Geometry.Polygon.Simple
import TauCeti.Analysis.Convex.Segment

/-!
# Double points of regular projections of polygons

The crossings of a knot diagram obtained by projecting a polygonal knot `k ⊆ ℝ³` to a plane sit
over the *double points* of the projection: the points of `k` that have the same image as another
point of `k`. This file defines them, `Polygon.doublePoints R poly π`, for a polygon
`poly : Polygon P n` and an arbitrary map `π` out of its ambient affine space, and proves two
basic facts about them for a regular projection (`Polygon.IsRegularProjection`).

First, the double points come in pairs. Every double point `x` has a *partner*
`Polygon.doublePointPartner R poly π x`, another point of the polygon with the same image. For a
regular projection the partner is unique (`Polygon.IsRegularProjection.eq_doublePointPartner`),
so the partner map is an involution (`Polygon.IsRegularProjection.involutive_doublePointPartner`)
whose non-fixed points on the polygon are exactly the double points; no vertex is a double point.

Second, for a simple polygon over a linearly ordered field and an affine regular projection, there
are only finitely many double points (`Polygon.IsRegularProjection.finite_doublePoints`). The key
step is that two distinct edges contain at most one pair of points with the same image
(`Polygon.IsRegularProjection.subsingleton_setOf_mem_edgeSet`): if the projections of two edges
overlapped in a segment, an end of the overlap would be the image of a vertex of one edge and of
a point of the other, which regularity forces to be a common point of the two edges, and two
distinct edges of a simple polygon share at most one point. The projection along a direction,
`Polygon.projAlong`, is affine, so these results apply to it.

Third, for a simple real polygon and the projection along a direction `d`, the crossings are
transverse: at a double point and its partner, the directions of the two edges through them and
`d` are linearly independent
(`Polygon.IsRegularProjection.linearIndependent_of_projAlong_eq`). This is what makes the sign of
a crossing of the knot diagram well defined.

## Main definitions

* `Polygon.doublePoints R poly π`: the points of the polygon with the same image under `π` as
  another point of the polygon.
* `Polygon.doublePointPartner R poly π`: the map sending a double point to another point of the
  polygon with the same image, and fixing every other point.

## Main results

* `Polygon.IsRegularProjection.eq_doublePointPartner`: for a regular projection, the partner is
  the only other point of the polygon with the same image.
* `Polygon.IsRegularProjection.involutive_doublePointPartner`: for a regular projection, the
  partner map is an involution.
* `Polygon.IsRegularProjection.apply_notMem_doublePoints`: no vertex is a double point.
* `Polygon.IsRegularProjection.subsingleton_setOf_mem_edgeSet`: two distinct edges of a simple
  polygon contain at most one pair of points with the same image under an affine regular
  projection.
* `Polygon.IsRegularProjection.finite_doublePoints`: an affine regular projection of a simple
  polygon has finitely many double points.
* `Polygon.IsRegularProjection.linearIndependent_of_projAlong_eq`: the crossings of a regular
  projection along a direction are transverse.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Springer GTM 57 (1977), Chapter I,
  for regular projections and their double points.
* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, for regular projections of polygonal knots.
-/

public section

open Set Function AffineMap

namespace Polygon

variable {R V P W Q : Type*} {n : ℕ}

section Defs

variable [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]
  {poly : Polygon P n} {π : P → Q} {x y : P}

variable (R) in
/-- The **double points** of the polygon `poly` under a map `π`: the points of the polygon that
have the same image under `π` as another point of the polygon. For a regular projection of a
polygonal knot to a plane, these are the points of the knot lying over the crossings of the
diagram. -/
def doublePoints (poly : Polygon P n) (π : P → Q) : Set P :=
  {x | x ∈ poly.boundary R ∧ ∃ y ∈ poly.boundary R, y ≠ x ∧ π y = π x}

/-- A double point is a point of the polygon with the same image as another point of the
polygon. -/
@[simp]
theorem mem_doublePoints :
    x ∈ poly.doublePoints R π ↔ x ∈ poly.boundary R ∧ ∃ y ∈ poly.boundary R, y ≠ x ∧ π y = π x :=
  Iff.rfl

/-- Polygons with the same boundary have the same double points under any map. -/
theorem doublePoints_eq_of_boundary_eq {m : ℕ} {poly' : Polygon P m}
    (hb : poly'.boundary R = poly.boundary R) :
    poly'.doublePoints R π = poly.doublePoints R π := by
  ext x
  simp only [mem_doublePoints, hb]

/-- Double points lie on the polygon. -/
theorem doublePoints_subset_boundary : poly.doublePoints R π ⊆ poly.boundary R :=
  fun _ hx ↦ hx.1

open Classical in
variable (R) in
/-- The **partner** of a double point `x` of `poly` under `π`: a point of the polygon other than
`x` with the same image under `π`. It is unique when `π` is a regular projection
(`IsRegularProjection.eq_doublePointPartner`). Points that are not double points are their own
partner. -/
noncomputable def doublePointPartner (poly : Polygon P n) (π : P → Q) (x : P) : P :=
  if hx : x ∈ poly.doublePoints R π then hx.2.choose else x

private theorem doublePointPartner_spec (hx : x ∈ poly.doublePoints R π) :
    poly.doublePointPartner R π x ∈ poly.boundary R ∧ poly.doublePointPartner R π x ≠ x ∧
      π (poly.doublePointPartner R π x) = π x := by
  rw [doublePointPartner, dite_eq_left_of_eq_true (eq_true hx)]
  exact hx.2.choose_spec

/-- A point that is not a double point is its own partner. -/
@[simp]
theorem doublePointPartner_of_notMem (hx : x ∉ poly.doublePoints R π) :
    poly.doublePointPartner R π x = x := by
  rw [doublePointPartner, dite_eq_right_of_eq_false (eq_false hx)]

/-- The partner of a point has the same image. -/
theorem apply_doublePointPartner (x : P) : π (poly.doublePointPartner R π x) = π x := by
  by_cases hx : x ∈ poly.doublePoints R π
  · exact (doublePointPartner_spec hx).2.2
  · rw [doublePointPartner_of_notMem hx]

/-- The partner of a double point is a different point. -/
theorem doublePointPartner_ne (hx : x ∈ poly.doublePoints R π) :
    poly.doublePointPartner R π x ≠ x :=
  (doublePointPartner_spec hx).2.1

/-- The partner of a point of the polygon lies on the polygon. -/
theorem doublePointPartner_mem_boundary (hx : x ∈ poly.boundary R) :
    poly.doublePointPartner R π x ∈ poly.boundary R := by
  by_cases hx' : x ∈ poly.doublePoints R π
  · exact (doublePointPartner_spec hx').1
  · rwa [doublePointPartner_of_notMem hx']

/-- A point is its own partner exactly when it is not a double point. -/
@[simp]
theorem doublePointPartner_eq_self_iff :
    poly.doublePointPartner R π x = x ↔ x ∉ poly.doublePoints R π :=
  ⟨fun h hx ↦ doublePointPartner_ne hx h, doublePointPartner_of_notMem⟩

/-- The partner of a double point is a double point. -/
theorem doublePointPartner_mem_doublePoints (hx : x ∈ poly.doublePoints R π) :
    poly.doublePointPartner R π x ∈ poly.doublePoints R π := by
  exact ⟨doublePointPartner_mem_boundary hx.1, x, hx.1, (doublePointPartner_ne hx).symm,
    (apply_doublePointPartner x).symm⟩

/-- For a regular projection, the partner of `x` is the only point of the polygon other than `x`
with the same image as `x`. -/
theorem IsRegularProjection.eq_doublePointPartner (hπ : poly.IsRegularProjection R π)
    (hx : x ∈ poly.boundary R) (hy : y ∈ poly.boundary R) (hne : y ≠ x) (h : π y = π x) :
    y = poly.doublePointPartner R π x := by
  obtain ⟨hz, hzx, hπz⟩ := doublePointPartner_spec (π := π) ⟨hx, y, hy, hne, h⟩
  rcases hπ.eq_or_eq_or_eq_of_apply_eq hx hy hz h.symm hπz.symm with h' | h' | h'
  exacts [(hne h'.symm).elim, (hzx h'.symm).elim, h']

/-- For a regular projection, the partner map is an involution: the double points come in pairs. -/
theorem IsRegularProjection.involutive_doublePointPartner (hπ : poly.IsRegularProjection R π) :
    Involutive (poly.doublePointPartner R π) := by
  intro x
  by_cases hx : x ∈ poly.doublePoints R π
  · exact (hπ.eq_doublePointPartner (doublePointPartner_mem_boundary hx.1) hx.1
      (doublePointPartner_ne hx).symm (apply_doublePointPartner x).symm).symm
  · rw [doublePointPartner_of_notMem hx, doublePointPartner_of_notMem hx]

/-- For a regular projection, no vertex of the polygon is a double point. -/
theorem IsRegularProjection.apply_notMem_doublePoints (hπ : poly.IsRegularProjection R π)
    (i : Fin n) : poly i ∉ poly.doublePoints R π := by
  rintro ⟨-, y, hy, hne, h⟩
  exact hne (hπ.eq_vertex_of_apply_eq i hy h)

end Defs

section Finite

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V]
  [AddTorsor V P] [AddCommGroup W] [Module R W] [AddTorsor W Q] {poly : Polygon P n} {π : P →ᵃ[R] Q}

/-- **Two distinct edges cross at most once.** For an affine regular projection `π` of a simple
polygon, two distinct edges contain at most one pair of points with the same image under `π`. For
consecutive edges this pair is their common vertex, taken twice. -/
theorem IsRegularProjection.subsingleton_setOf_mem_edgeSet (hs : poly.IsSimple R)
    (hπ : poly.IsRegularProjection R π) {i j : Fin n} (hij : i ≠ j) :
    {p : P × P | p.1 ∈ poly.edgeSet R i ∧ p.2 ∈ poly.edgeSet R j ∧ π p.1 = π p.2}.Subsingleton := by
  have hinj := hπ.injOn_edgeSet
  rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩ ⟨x', y'⟩ ⟨hx', hy', hxy'⟩
  dsimp only at hx hy hxy hx' hy' hxy'
  suffices hxx : x = x' by
    subst hxx
    rw [hinj j hy hy' (hxy.symm.trans hxy')]
  by_contra hne
  obtain ⟨s, hsI, rfl⟩ := hx
  obtain ⟨s', hsI', rfl⟩ := hx'
  obtain ⟨t, ht, rfl⟩ := hy
  obtain ⟨t', ht', rfl⟩ := hy'
  have hss' : s ≠ s' := by rintro rfl; exact hne rfl
  have htt' : t ≠ t' := by
    rintro rfl
    exact hne (hinj i ⟨s, hsI, rfl⟩ ⟨s', hsI', rfl⟩ (hxy.trans hxy'.symm))
  have htt'₀ : t' - t ≠ 0 := sub_ne_zero.2 htt'.symm
  -- Under `π`, edge `j` at the parameter `u` lies over edge `i` at the parameter `h u`, an
  -- affine function of `u`.
  set h : R → R := fun u ↦ lineMap s s' ((u - t) / (t' - t)) with h_def
  have hh (u : R) : h u = lineMap (h 0) (h 1) u := by
    simp only [h_def, lineMap_apply_ring']
    field_simp
    ring
  have hrel (u : R) : π (lineMap (poly i) (poly (finRotate n i)) (h u)) =
      π (lineMap (poly j) (poly (finRotate n j)) u) := by
    have hu : lineMap t t' ((u - t) / (t' - t)) = u := by
      rw [lineMap_apply_ring']
      field_simp
      ring
    conv_rhs => rw [← hu]
    simp only [h_def, AffineMap.apply_lineMap, hxy, hxy']
  have ht₀ : h t = s := by simp [h_def]
  have ht₁ : h t' = s' := by simp [h_def, div_self htt'₀]
  -- The overlap of the two edges under `π` has two distinct ends.
  obtain ⟨u₁, u₂, hne₁₂, hu⟩ := TauCeti.exists_lineMap_endpoint ht ht'
    (by rw [← hh, ht₀]; exact hsI) (by rw [← hh, ht₁]; exact hsI')
    (by rw [← hh, ← hh, ht₀, ht₁]; exact hss')
  -- By regularity, each end of the overlap is a common point of the two edges.
  have hcommon (u : R) (hu' : u ∈ ({u₁, u₂} : Set R)) :
      lineMap (poly i) (poly (finRotate n i)) (h u) ∈ poly.edgeSet R i ∩ poly.edgeSet R j := by
    obtain ⟨hu, hhu, hend⟩ := hu u hu'
    rw [← hh] at hhu hend
    have hX : lineMap (poly i) (poly (finRotate n i)) (h u) ∈ poly.edgeSet R i := ⟨_, hhu, rfl⟩
    have hY : lineMap (poly j) (poly (finRotate n j)) u ∈ poly.edgeSet R j := ⟨_, hu, rfl⟩
    have hXb := mem_iUnion.2 ⟨i, hX⟩
    have hYb := mem_iUnion.2 ⟨j, hY⟩
    suffices lineMap (poly i) (poly (finRotate n i)) (h u) =
        lineMap (poly j) (poly (finRotate n j)) u from ⟨hX, this ▸ hY⟩
    rcases hend with rfl | rfl | h0 | h1
    · rw [lineMap_apply_zero]
      exact hπ.eq_vertex_of_apply_eq j hXb (by simpa only [lineMap_apply_zero] using hrel 0)
    · rw [lineMap_apply_one]
      exact hπ.eq_vertex_of_apply_eq _ hXb (by simpa only [lineMap_apply_one] using hrel 1)
    · rw [h0, lineMap_apply_zero]
      exact (hπ.eq_vertex_of_apply_eq i hYb
        ((hrel u).symm.trans (by rw [h0, lineMap_apply_zero]))).symm
    · rw [h1, lineMap_apply_one]
      exact (hπ.eq_vertex_of_apply_eq _ hYb
        ((hrel u).symm.trans (by rw [h1, lineMap_apply_one]))).symm
  -- Two distinct common points of two distinct edges contradict simplicity.
  refine hne₁₂ ?_
  rw [← hh, ← hh]
  exact lineMap_injective R (hs.hasNondegenerateEdges i)
    (hs.subsingleton_edgeSet_inter hij (hcommon u₁ (.inl rfl)) (hcommon u₂ (.inr rfl)))

/-- **An affine regular projection of a simple polygon has finitely many double points.** Each
double point lies on an edge sharing its image with a point of another edge, and two distinct edges
contain at most one such pair (`IsRegularProjection.subsingleton_setOf_mem_edgeSet`). -/
theorem IsRegularProjection.finite_doublePoints (hs : poly.IsSimple R)
    (hπ : poly.IsRegularProjection R π) : (poly.doublePoints R π).Finite := by
  refine Finite.subset (finite_iUnion fun i : Fin n ↦ finite_iUnion fun j : Fin n ↦
    finite_iUnion fun hij : i ≠ j ↦ ((hπ.subsingleton_setOf_mem_edgeSet hs hij).image
      Prod.fst).finite) ?_
  rintro x ⟨hx, y, hy, hyx, hπyx⟩
  obtain ⟨i, hxi⟩ := mem_iUnion.1 hx
  obtain ⟨j, hyj⟩ := mem_iUnion.1 hy
  have hij : i ≠ j := by
    rintro rfl
    exact hyx (hπ.injOn_edgeSet i hyj hxi hπyx)
  exact mem_iUnion₂.2 ⟨i, j, mem_iUnion.2 ⟨hij, (x, y), ⟨hxi, hyj, hπyx.symm⟩, rfl⟩⟩

end Finite

section Transversality

open Filter Topology

variable [AddCommGroup V] [Module ℝ V] [AddTorsor V P] {poly : Polygon P n} {p₀ : P} {d : V}

/-- **Crossings of a regular projection are transverse.** Let `x` and `y` be distinct points in
the interiors of edges `i` and `j` of a simple polygon with the same projection along `d`, a
regular projection. Then the directions of the two edges and `d` are linearly independent:
otherwise either an edge would be parallel to `d`, or moving `x` and `y` along their edges would
give a second pair of points of the two edges with the same projection. -/
theorem IsRegularProjection.linearIndependent_of_projAlong_eq (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {i j : Fin n} {s t : ℝ}
    (hsI : s ∈ Ioo (0 : ℝ) 1) (htI : t ∈ Ioo (0 : ℝ) 1)
    (hne : poly.edgePath ℝ i s ≠ poly.edgePath ℝ j t)
    (h : projAlong ℝ p₀ d (poly.edgePath ℝ i s) = projAlong ℝ p₀ d (poly.edgePath ℝ j t)) :
    LinearIndependent ℝ ![poly (finRotate n i) -ᵥ poly i, poly (finRotate n j) -ᵥ poly j, d] := by
  have hmem (k : Fin n) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
      poly.edgePath ℝ k r ∈ poly.edgeSet ℝ k := by
    rw [edgeSet_eq_image_edgePath]
    exact mem_image_of_mem _ (Ioo_subset_Icc_self hr)
  have hij : i ≠ j := by
    rintro rfl
    exact hne (hπ.injOn_edgeSet i (hmem i hsI) (hmem i htI) h)
  -- Moving along an edge by `c` translates a point of it by `c` times the edge direction.
  have hpath (k : Fin n) (r c : ℝ) : poly.edgePath ℝ k (r + c) =
      c • (poly (finRotate n k) -ᵥ poly k) +ᵥ poly.edgePath ℝ k r := by
    simp only [edgePath, lineMap_apply, vadd_vadd, ← add_smul, add_comm]
  -- No edge is parallel to `d`, since the projection is injective on the vertices.
  have hnpar (k : Fin n) (a : ℝ) (ha : a • d = poly (finRotate n k) -ᵥ poly k) : False :=
    hs.hasNondegenerateEdges k (hπ.eq_vertex_of_apply_eq k
      (mem_iUnion.2 ⟨k, poly.apply_finRotate_mem_edgeSet ℝ k⟩)
      (projAlong_eq_projAlong_iff.2 ⟨a, ha⟩)).symm
  obtain ⟨a, ha⟩ := projAlong_eq_projAlong_iff.1 h
  have hd : d ≠ 0 := by
    rintro rfl
    rw [smul_zero, eq_comm, vsub_eq_zero_iff_eq] at ha
    exact hne ha
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
  suffices h01 : g 0 = 0 ∧ g 1 = 0 by
    obtain ⟨h0, h1⟩ := h01
    have h2 : g 2 = 0 := by
      rw [h0, h1, zero_smul, zero_smul, zero_add, zero_add, smul_eq_zero] at hg
      exact hg.resolve_right hd
    intro k
    fin_cases k <;> assumption
  by_cases h0 : g 0 = 0
  · refine ⟨h0, by_contra fun h1 ↦ hnpar j (-((g 1)⁻¹ * g 2)) ?_⟩
    rw [h0, zero_smul, zero_add] at hg
    have := congrArg ((g 1)⁻¹ • ·) hg
    simp only [smul_add, smul_smul, inv_mul_cancel₀ h1, one_smul, smul_zero] at this
    rw [neg_smul, neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero, add_comm, this]
  by_cases h1 : g 1 = 0
  · refine (hnpar i (-((g 0)⁻¹ * g 2)) ?_).elim
    rw [h1, zero_smul, add_zero] at hg
    have := congrArg ((g 0)⁻¹ • ·) hg
    simp only [smul_add, smul_smul, inv_mul_cancel₀ h0, one_smul, smul_zero] at this
    rw [neg_smul, neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero, add_comm, this]
  -- Both edges move: for small `l ≠ 0`, the points of the edges at the parameters `s + l * g 0`
  -- and `t - l * g 1` again have the same projection.
  exfalso
  have hev : ∀ᶠ l in 𝓝 (0 : ℝ), s + l * g 0 ∈ Ioo (0 : ℝ) 1 ∧ t + -(l * g 1) ∈ Ioo (0 : ℝ) 1 := by
    refine (Tendsto.eventually_mem ?_ (Ioo_mem_nhds hsI.1 hsI.2)).and
      (Tendsto.eventually_mem ?_ (Ioo_mem_nhds htI.1 htI.2))
    · have : Continuous fun l : ℝ ↦ s + l * g 0 := by fun_prop
      simpa using this.tendsto 0
    · have : Continuous fun l : ℝ ↦ t + -(l * g 1) := by fun_prop
      simpa using this.tendsto 0
  obtain ⟨l, ⟨hl₁, hl₂⟩, hl₀⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := {0}ᶜ))).exists
  have hl₀ : l ≠ 0 := hl₀
  have hproj : projAlong ℝ p₀ d (poly.edgePath ℝ i (s + l * g 0)) =
      projAlong ℝ p₀ d (poly.edgePath ℝ j (t + -(l * g 1))) := by
    refine projAlong_eq_projAlong_iff.2 ⟨a - l * g 2, ?_⟩
    rw [hpath, hpath, vadd_vsub_vadd_comm, ← ha]
    linear_combination (norm := module) (-l) • hg
  let S : Set (P × P) := {q | q.1 ∈ poly.edgeSet ℝ i ∧ q.2 ∈ poly.edgeSet ℝ j ∧
    projAlong ℝ p₀ d q.1 = projAlong ℝ p₀ d q.2}
  have hq₀ : (poly.edgePath ℝ i s, poly.edgePath ℝ j t) ∈ S := ⟨hmem i hsI, hmem j htI, h⟩
  have hq₁ : (poly.edgePath ℝ i (s + l * g 0), poly.edgePath ℝ j (t + -(l * g 1))) ∈ S :=
    ⟨hmem i hl₁, hmem j hl₂, hproj⟩
  have hpair := hπ.subsingleton_setOf_mem_edgeSet hs hij hq₀ hq₁
  have hx := congrArg Prod.fst hpair
  dsimp only at hx
  rw [hpath, eq_comm] at hx
  have hv := (vadd_vsub _ _).symm.trans ((congrArg (· -ᵥ poly.edgePath ℝ i s) hx).trans
    (vsub_self _))
  rw [smul_eq_zero, vsub_eq_zero_iff_eq] at hv
  exact hv.elim (mul_ne_zero hl₀ h0) fun hx ↦ hs.hasNondegenerateEdges i hx.symm

end Transversality

end Polygon
