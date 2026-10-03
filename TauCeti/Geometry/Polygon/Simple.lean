/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Polygon.Basic
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Instances.AddCircle.Defs
public import TauCeti.Topology.JordanCurve.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.Order.Floor
import TauCeti.Analysis.Convex.Between

/-!
# Simple polygons

A polygon `poly : Polygon P n` (Mathlib's `Polygon`, a cyclic list of `n` vertices of an affine
space) is **simple** when its edges are nondegenerate and two distinct edges meet only when they
are consecutive, and then only at their common vertex. Over the reals, the boundary of a simple
polygon is a Jordan curve: running along the edges in order, one unit of time per edge, parametrizes
the boundary by the circle `AddCircle n`, and simplicity makes this parametrization injective.

A simple closed polygon in `ℝ³` is the polygonal presentation of an oriented knot (Burde and
Zieschang, Definition 1.3; Lickorish, Definition 1.1): the cyclic order of the vertices is the
orientation, and the parametrization `Polygon.boundaryParamCircle` is the corresponding
topological embedding of the circle. The bundled type `TauCeti.SimplePolygon` carries the number of
vertices as data, so that polygons with different numbers of vertices are presentations of the
same type, and `TauCeti.SimplePolygon.realize` is its realization as a topological embedding of
the unit circle `Circle`. A framing is not part of this presentation: a framing of a polygonal
knot is a chosen push-off, which is separate data on top of the simple polygon, as for
`TauCeti.SmoothCircleEmbedding`. Nothing here depends on the dimension of the ambient space.

The first simple polygons are the triangles: `Affine.Triangle.toPolygon_isSimple`. The polygon with
no vertices is vacuously simple and has empty boundary, so the results about the boundary assume
`NeZero n`.

## Main definitions

* `Polygon.IsSimple`: the edges are nondegenerate, and distinct edges meet only at the common
  vertex of consecutive edges.
* `Polygon.boundaryParam`: the periodic map `ℝ → P` running along edge `i` on `[i, i + 1]`.
* `Polygon.boundaryParamCircle`: the induced map from the circle `AddCircle n` to `P`.
* `TauCeti.SimplePolygon`: a simple polygon bundled with its number of vertices, the polygonal
  presentation of a knot when `P = ℝ³`.
* `TauCeti.SimplePolygon.realize`: the realization of a simple real polygon as a map from the
  unit circle `Circle`.

## Main results

* `Polygon.range_boundaryParam`: the parametrization runs over the whole boundary.
* `Polygon.IsSimple.boundaryParam_eq_boundaryParam_iff`: for a simple polygon, two parameters
  give the same point exactly when they agree modulo `n`.
* `Polygon.IsSimple.isClosedEmbedding_boundaryParamCircle`: a simple real polygon is a closed
  embedding of the circle.
* `Polygon.IsSimple.isJordanCurve_boundary`: the boundary of a simple real polygon is a Jordan
  curve.
* `TauCeti.SimplePolygon.isClosedEmbedding_realize`: the realization of a simple real polygon is a
  closed embedding of the circle.
* `Affine.Triangle.toPolygon_isSimple`: a triangle is a simple polygon.

## References

* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, Definition 1.3.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1,
  Definition 1.1.
-/

public section

open Set Function Topology

namespace Polygon

variable {R V P : Type*} {n : ℕ}

section IsSimple

variable [Ring R] [PartialOrder R] [ZeroLEOneClass R] [AddCommGroup V] [Module R V]
  [AddTorsor V P]

variable (R) in
/-- A polygon is **simple** when its edges are nondegenerate and two distinct edges meet only when
they are consecutive, and then only at their common vertex. -/
structure IsSimple (poly : Polygon P n) : Prop where
  /-- Consecutive vertices are distinct. -/
  hasNondegenerateEdges : poly.HasNondegenerateEdges
  /-- A point on two distinct edges is the common vertex of two consecutive edges: the end of
  the first and the start of the second. -/
  eq_vertex_of_mem_edgeSet : ∀ ⦃i j : Fin n⦄ ⦃x : P⦄, i ≠ j → x ∈ poly.edgeSet R i →
    x ∈ poly.edgeSet R j → (j = finRotate n i ∧ x = poly j) ∨ (i = finRotate n j ∧ x = poly i)

end IsSimple

/-! ### The boundary parametrization -/

section Param

variable [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- The vertex index `k mod n` of an integer `k`. -/
private def vertexIndex (n : ℕ) [NeZero n] (k : ℤ) : Fin n :=
  (ZMod.finEquiv n).symm k

private theorem vertexIndex_add_one [NeZero n] (k : ℤ) :
    vertexIndex n (k + 1) = finRotate n (vertexIndex n k) := by
  rw [finRotate_apply, vertexIndex, vertexIndex, Int.cast_add, Int.cast_one, map_add, map_one]

private theorem vertexIndex_add_natCast_self [NeZero n] (k : ℤ) :
    vertexIndex n (k + n) = vertexIndex n k := by
  simp [vertexIndex]

private theorem vertexIndex_natCast [NeZero n] (i : Fin n) : vertexIndex n (i : ℕ) = i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  -- `ZMod.finEquiv (m + 1)` is the identity of `Fin (m + 1) = ZMod (m + 1)`, and Mathlib has no
  -- lemma evaluating it, so this step unfolds it.
  exact (Int.cast_natCast (R := ZMod (m + 1)) i).trans (@ZMod.natCast_zmod_val (m + 1) _ i)

private theorem vertexIndex_eq_vertexIndex_iff [NeZero n] {k l : ℤ} :
    vertexIndex n k = vertexIndex n l ↔ (n : ℤ) ∣ l - k := by
  rw [vertexIndex, vertexIndex, (ZMod.finEquiv n).symm.injective.eq_iff,
    ZMod.intCast_eq_intCast_iff_dvd_sub]

variable [NeZero n] (poly : Polygon P n)

/-- The boundary parametrization of a polygon with `n` vertices: the periodic map `ℝ → P` that
runs along the edge from vertex `i` to the next one in one unit of time, on `[i, i + 1]`, for every
integer `i` read modulo `n`. -/
noncomputable def boundaryParam (t : ℝ) : P :=
  poly.edgePath ℝ (vertexIndex n ⌊t⌋) (Int.fract t)

/-- On `[k, k + 1]` the boundary parametrization runs along the edge starting at vertex `k mod n`,
including at the right end point, where the next edge starts at the same vertex. -/
theorem boundaryParam_eq_edgePath (k : ℤ) {t : ℝ} (ht : t ∈ Icc (k : ℝ) (k + 1)) :
    poly.boundaryParam t = poly.edgePath ℝ ((ZMod.finEquiv n).symm k) (t - k) := by
  -- `vertexIndex n k` is `(ZMod.finEquiv n).symm k` by definition.
  change _ = poly.edgePath ℝ (vertexIndex n k) _
  rcases ht.2.lt_or_eq with htk | rfl
  · have hfloor : ⌊t⌋ = k := Int.floor_eq_iff.2 ⟨ht.1, htk⟩
    rw [boundaryParam, hfloor, Int.fract, hfloor]
  · have hfloor : ⌊(k : ℝ) + 1⌋ = k + 1 := by exact_mod_cast Int.floor_intCast (k + 1)
    simp [boundaryParam, edgePath, hfloor, vertexIndex_add_one]

/-- The boundary parametrization runs along edge `i` on `[i, i + 1]`. -/
theorem boundaryParam_natCast_add (i : Fin n) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    poly.boundaryParam ((i : ℕ) + s) = poly.edgePath ℝ i s := by
  have h := poly.boundaryParam_eq_edgePath (i : ℕ) (t := (i : ℕ) + s)
    ⟨by simpa using hs.1, by simpa using hs.2⟩
  rw [← vertexIndex, vertexIndex_natCast] at h
  simpa using h

/-- The boundary parametrization passes through vertex `i` at time `i`. -/
@[simp]
theorem boundaryParam_natCast (i : Fin n) : poly.boundaryParam (i : ℕ) = poly i := by
  simpa [edgePath] using poly.boundaryParam_natCast_add i (s := 0) ⟨le_rfl, zero_le_one⟩

/-- The boundary parametrization has period `n`. -/
theorem periodic_boundaryParam : Periodic poly.boundaryParam n := fun t => by
  rw [boundaryParam, boundaryParam, Int.floor_add_natCast, Int.fract_add_natCast,
    vertexIndex_add_natCast_self]

/-- The boundary parametrization runs over the whole boundary of the polygon. -/
theorem range_boundaryParam : range poly.boundaryParam = poly.boundary ℝ := by
  refine Subset.antisymm ?_ fun x hx => ?_
  · rintro _ ⟨t, rfl⟩
    refine mem_iUnion.2 ⟨vertexIndex n ⌊t⌋, ?_⟩
    rw [edgeSet_eq_image_edgePath]
    exact mem_image_of_mem _ ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    rw [edgeSet_eq_image_edgePath] at hi
    obtain ⟨s, hs, rfl⟩ := hi
    exact mem_range.2 ⟨_, poly.boundaryParam_natCast_add i hs⟩

/-- The boundary parametrization induces a map from the circle `AddCircle n`, of length the number
of vertices. -/
noncomputable def boundaryParamCircle : AddCircle (n : ℝ) → P :=
  poly.periodic_boundaryParam.lift

@[simp]
theorem boundaryParamCircle_coe (t : ℝ) : poly.boundaryParamCircle t = poly.boundaryParam t :=
  poly.periodic_boundaryParam.lift_coe t

/-- The circle parametrization runs over the whole boundary of the polygon. -/
theorem range_boundaryParamCircle : range poly.boundaryParamCircle = poly.boundary ℝ := by
  rw [← poly.range_boundaryParam, ← QuotientAddGroup.mk_surjective.range_comp]
  exact congrArg range (funext poly.boundaryParamCircle_coe)

variable {poly}

omit [NeZero n] in
/-- A point of an edge reached before its end point is not the end vertex. -/
private theorem edgePath_ne_finRotate (h : poly.HasNondegenerateEdges) (i : Fin n) {s : ℝ}
    (hs : s < 1) : poly.edgePath ℝ i s ≠ poly (finRotate n i) := fun heq =>
  hs.ne (AffineMap.lineMap_injective ℝ (h i) (heq.trans (AffineMap.lineMap_apply_one _ _).symm))

/-- **Injectivity of the boundary parametrization.** For a simple polygon, two parameters give the
same boundary point exactly when they agree modulo the number of vertices. -/
theorem IsSimple.boundaryParam_eq_boundaryParam_iff (h : poly.IsSimple ℝ) {s t : ℝ} :
    poly.boundaryParam s = poly.boundaryParam t ↔ (s : AddCircle (n : ℝ)) = t := by
  refine ⟨fun hst => ?_, fun hst => by
    rw [← boundaryParamCircle_coe, hst, boundaryParamCircle_coe]⟩
  have hmem (u : ℝ) : poly.boundaryParam u ∈ poly.edgeSet ℝ (vertexIndex n ⌊u⌋) := by
    rw [edgeSet_eq_image_edgePath]
    exact mem_image_of_mem _ ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩
  by_cases hij : vertexIndex n ⌊s⌋ = vertexIndex n ⌊t⌋
  · -- On a common edge the fractional parts agree, and the integer parts agree modulo `n`.
    have hfract : Int.fract s = Int.fract t := AffineMap.lineMap_injective ℝ
      (h.hasNondegenerateEdges _) (by simpa only [boundaryParam, edgePath, hij] using hst)
    obtain ⟨m, hm⟩ := vertexIndex_eq_vertexIndex_iff.1 hij
    rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
    refine ⟨m, ?_⟩
    rw [← Int.floor_add_fract s, ← Int.floor_add_fract t, hfract, zsmul_eq_mul]
    have hm' : ((⌊t⌋ : ℤ) : ℝ) - ⌊s⌋ = n * m := by exact_mod_cast hm
    linarith
  · -- On distinct edges the common point would be the end vertex of one of them.
    rcases h.eq_vertex_of_mem_edgeSet hij (hmem s) (hst ▸ hmem t) with ⟨hj, hx⟩ | ⟨hi, hx⟩
    · rw [hj, boundaryParam] at hx
      exact absurd hx (edgePath_ne_finRotate h.hasNondegenerateEdges _ (Int.fract_lt_one s))
    · rw [hst, hi, boundaryParam] at hx
      exact absurd hx (edgePath_ne_finRotate h.hasNondegenerateEdges _ (Int.fract_lt_one t))

/-- The circle parametrization of a simple polygon is injective. -/
theorem IsSimple.boundaryParamCircle_injective (h : poly.IsSimple ℝ) :
    Injective poly.boundaryParamCircle := by
  intro x y hxy
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [boundaryParamCircle_coe, boundaryParamCircle_coe] at hxy
  exact h.boundaryParam_eq_boundaryParam_iff.1 hxy

section Topology

variable [TopologicalSpace V] [ContinuousSMul ℝ V] [TopologicalSpace P] [IsTopologicalAddTorsor P]

variable (poly) in
/-- The boundary parametrization is continuous. -/
theorem continuous_boundaryParam : Continuous poly.boundaryParam := by
  -- On each `[k, k + 1]` the parametrization is affine; at `t` these intervals for `k = ⌈t⌉ - 1`
  -- and `k = ⌊t⌋` are neighbourhoods of `t` from the left and from the right.
  have hcont (k : ℤ) : ContinuousOn poly.boundaryParam (Icc (k : ℝ) (k + 1)) :=
    (AffineMap.lineMap_continuous.comp (continuous_sub_right (k : ℝ))).continuousOn.congr
      fun t ht => poly.boundaryParam_eq_edgePath k ht
  refine continuous_iff_continuousAt.2 fun t => continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
  · have ht : t ∈ Ioc ((⌈t⌉ - 1 : ℤ) : ℝ) ((⌈t⌉ - 1 : ℤ) + 1) := by
      push_cast
      exact ⟨by linarith [Int.ceil_lt_add_one t], by linarith [Int.le_ceil t]⟩
    exact ((hcont _).continuousWithinAt (Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE_of_mem ht)
  · have ht : t ∈ Ico (⌊t⌋ : ℝ) (⌊t⌋ + 1) := ⟨Int.floor_le t, Int.lt_floor_add_one t⟩
    exact ((hcont _).continuousWithinAt (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)

variable (poly) in
/-- The circle parametrization is continuous. -/
theorem continuous_boundaryParamCircle : Continuous poly.boundaryParamCircle :=
  (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 <| by
    simpa only [comp_def, boundaryParamCircle_coe] using poly.continuous_boundaryParam

/-- **A simple real polygon is an embedded circle.** The circle parametrization of a simple polygon
is a closed embedding of `AddCircle n` into a Hausdorff ambient space. -/
theorem IsSimple.isClosedEmbedding_boundaryParamCircle [T2Space P] (h : poly.IsSimple ℝ) :
    IsClosedEmbedding poly.boundaryParamCircle :=
  haveI : Fact (0 < (n : ℝ)) := ⟨Nat.cast_pos.2 (Nat.pos_of_neZero n)⟩
  poly.continuous_boundaryParamCircle.isClosedEmbedding h.boundaryParamCircle_injective

/-- **The boundary of a simple real polygon is a Jordan curve.** -/
theorem IsSimple.isJordanCurve_boundary [T2Space P] (h : poly.IsSimple ℝ) :
    TauCeti.IsJordanCurve (poly.boundary ℝ) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have huniv : TauCeti.IsJordanCurve (univ : Set (AddCircle (n : ℝ))) :=
    TauCeti.isJordanCurve_iff.2
      ⟨(Homeomorph.Set.univ (AddCircle (n : ℝ))).trans (AddCircle.homeomorphCircle hn)⟩
  have himage := huniv.image poly.continuous_boundaryParamCircle.continuousOn
    h.boundaryParamCircle_injective.injOn
  rwa [image_univ, range_boundaryParamCircle] at himage

end Topology

end Param

end Polygon

namespace Affine.Triangle

variable {R V P : Type*} [Ring R] [PartialOrder R] [ZeroLEOneClass R]
  [Nontrivial R] [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- **A triangle is a simple polygon.** -/
theorem toPolygon_isSimple (t : Affine.Triangle R P) : t.toPolygon.IsSimple R := by
  have hnd := t.toPolygon_hasNondegenerateVertices
  refine ⟨hnd.hasNondegenerateEdges, fun i j x hij hi hj => ?_⟩
  -- Two distinct sides of a triangle are consecutive one way round, and meet at their common
  -- vertex, the middle one of three consecutive vertices.
  have hside (i : Fin 3) {x : P} (hi : x ∈ t.toPolygon.edgeSet R i)
      (hj : x ∈ t.toPolygon.edgeSet R (finRotate 3 i)) : x = t.toPolygon (finRotate 3 i) := by
    have hx : x ∈ affineSegment R (t.toPolygon i) (t.toPolygon (i + 1)) ∩
        affineSegment R (t.toPolygon (i + 1)) (t.toPolygon (i + 2)) := by
      refine ⟨by simpa [Polygon.edgeSet, finRotate_apply] using hi, ?_⟩
      simpa [Polygon.edgeSet, finRotate_apply, add_assoc] using hj
    rw [(hnd i).affineSegment_inter_eq_endpoint] at hx
    simpa [finRotate_apply] using hx
  fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij
  all_goals first
    | exact Or.inl ⟨by decide, hside _ hi hj⟩
    | exact Or.inr ⟨by decide, hside _ hj hi⟩

end Affine.Triangle

namespace TauCeti

/-- A **simple polygon** in `P` over `R`: a polygon with a positive number of vertices that is
simple over `R`. The number of vertices is part of the data, so that one type contains the simple
polygons with any number of vertices. A simple polygon in `ℝ³` is the polygonal presentation of an
oriented knot, realized as a topological embedding of the circle by `SimplePolygon.realize`. -/
structure SimplePolygon (R : Type*) {V : Type*} (P : Type*) [Ring R] [PartialOrder R]
    [ZeroLEOneClass R] [AddCommGroup V] [Module R V] [AddTorsor V P] where
  /-- The number of vertices. -/
  numVertices : ℕ
  [neZero : NeZero numVertices]
  /-- The underlying polygon. -/
  toPolygon : Polygon P numVertices
  /-- The underlying polygon is simple. -/
  isSimple : toPolygon.IsSimple R

namespace SimplePolygon

attribute [instance] neZero

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P] (p : SimplePolygon ℝ P)

/-- The realization of a simple real polygon as a map from the unit circle: the circle
parametrization `Polygon.boundaryParamCircle` of its boundary, read on `Circle` through the
homeomorphism `AddCircle.homeomorphCircle` from `AddCircle n`, where `n` is the number of
vertices. -/
noncomputable def realize : Circle → P :=
  p.toPolygon.boundaryParamCircle ∘
    (AddCircle.homeomorphCircle (Nat.cast_ne_zero.2 (NeZero.ne p.numVertices))).symm

/-- The realization passes through `Polygon.boundaryParam t` at the image of `t` in the circle. -/
@[simp]
theorem realize_toCircle (t : ℝ) :
    p.realize (AddCircle.toCircle (t : AddCircle (p.numVertices : ℝ))) =
      p.toPolygon.boundaryParam t := by
  rw [realize, comp_apply,
    ← AddCircle.homeomorphCircle_apply (Nat.cast_ne_zero.2 (NeZero.ne p.numVertices)),
    Homeomorph.symm_apply_apply, Polygon.boundaryParamCircle_coe]

/-- The realization runs over the whole boundary of the polygon. -/
theorem range_realize : range p.realize = p.toPolygon.boundary ℝ := by
  rw [realize, (Homeomorph.surjective _).range_comp, Polygon.range_boundaryParamCircle]

/-- **A simple real polygon is an embedded circle.** Its realization is a closed embedding of the
unit circle into a Hausdorff ambient space. -/
theorem isClosedEmbedding_realize [TopologicalSpace V] [ContinuousSMul ℝ V] [TopologicalSpace P]
    [IsTopologicalAddTorsor P] [T2Space P] : IsClosedEmbedding p.realize :=
  p.isSimple.isClosedEmbedding_boundaryParamCircle.comp (Homeomorph.isClosedEmbedding _)

end SimplePolygon

end TauCeti

namespace Affine.Triangle

variable {R V P : Type*} [Ring R] [PartialOrder R] [ZeroLEOneClass R]
  [Nontrivial R] [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- A triangle, as a simple polygon with three vertices. -/
@[expose] def toSimplePolygon (t : Affine.Triangle R P) : TauCeti.SimplePolygon R P where
  numVertices := 3
  toPolygon := t.toPolygon
  isSimple := t.toPolygon_isSimple

@[simp]
theorem toSimplePolygon_numVertices (t : Affine.Triangle R P) :
    t.toSimplePolygon.numVertices = 3 :=
  rfl

@[simp]
theorem toSimplePolygon_toPolygon (t : Affine.Triangle R P) :
    t.toSimplePolygon.toPolygon = t.toPolygon :=
  rfl

end Affine.Triangle
