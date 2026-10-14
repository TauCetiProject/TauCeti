/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Polygon.RegularProjection
public import TauCeti.Geometry.Polygon.Simple

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
* `Polygon.IsRegularProjection.injOn_edgeSet`: an affine regular projection is injective on every
  nondegenerate edge.
* `Polygon.IsRegularProjection.subsingleton_setOf_mem_edgeSet`: two distinct edges of a simple
  polygon contain at most one pair of points with the same image under an affine regular
  projection.
* `Polygon.IsRegularProjection.finite_doublePoints`: an affine regular projection of a simple
  polygon has finitely many double points.

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

section InjOn

variable [Ring R] [PartialOrder R] [ZeroLEOneClass R] [IsDomain R] [AddCommGroup V] [Module R V]
  [AddTorsor V P] [AddCommGroup W] [Module R W] [Module.IsTorsionFree R W] [AddTorsor W Q]
  {poly : Polygon P n} {π : P →ᵃ[R] Q}

/-- An affine regular projection is injective on every nondegenerate edge of the polygon:
otherwise it would identify the two ends of the edge. -/
theorem IsRegularProjection.injOn_edgeSet (hπ : poly.IsRegularProjection R π) {i : Fin n}
    (hi : poly i ≠ poly (finRotate n i)) : InjOn π (poly.edgeSet R i) := by
  have hne : π (poly i) ≠ π (poly (finRotate n i)) := fun h ↦
    hi (hπ.eq_vertex_of_apply_eq i (poly.apply_mem_boundary R _) h.symm).symm
  rintro _ ⟨s, -, rfl⟩ _ ⟨t, -, rfl⟩ hst
  rw [π.apply_lineMap, π.apply_lineMap] at hst
  rw [lineMap_injective R hne hst]

end InjOn

section Finite

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Let `f = lineMap a b` be an affine function on `R` taking distinct values in `[0, 1]` at two
points of `[0, 1]`. Then the overlap of `[0, 1]` with `f '' [0, 1]` is a nondegenerate interval,
and its two ends are values `f u` at points `u ∈ [0, 1]` with `u` or `f u` an end of `[0, 1]`. -/
private theorem exists_lineMap_endpoint {a b t t' : R} (ht : t ∈ Icc 0 1) (ht' : t' ∈ Icc 0 1)
    (hs : lineMap a b t ∈ Icc (0 : R) 1) (hs' : lineMap a b t' ∈ Icc (0 : R) 1)
    (hne : lineMap a b t ≠ lineMap a b t') :
    ∃ u₁ u₂ : R, lineMap a b u₁ ≠ lineMap a b u₂ ∧ ∀ u ∈ ({u₁, u₂} : Set R),
      u ∈ Icc (0 : R) 1 ∧ lineMap a b u ∈ Icc (0 : R) 1 ∧
        (u = 0 ∨ u = 1 ∨ lineMap a b u = 0 ∨ lineMap a b u = 1) := by
  have hab : a ≠ b := by rintro rfl; simp at hne
  have hI : Icc (0 : R) 1 ∩ lineMap a b '' Icc (0 : R) 1 = Icc (0 ⊔ (a ⊓ b)) (1 ⊓ (a ⊔ b)) := by
    rw [← segment_eq_image_lineMap, segment_eq_uIcc, uIcc, Icc_inter_Icc]
  have hmem {u : R} (hu : u ∈ Icc (0 : R) 1) (hfu : lineMap a b u ∈ Icc (0 : R) 1) :
      lineMap a b u ∈ Icc (0 ⊔ (a ⊓ b)) (1 ⊓ (a ⊔ b)) :=
    hI ▸ ⟨hfu, mem_image_of_mem _ hu⟩
  have hlt : 0 ⊔ (a ⊓ b) < 1 ⊓ (a ⊔ b) := by
    obtain ⟨h₁, h₂⟩ := hmem ht hs
    obtain ⟨h₃, h₄⟩ := hmem ht' hs'
    by_contra! hle
    exact hne (le_antisymm (h₂.trans (hle.trans h₃)) (h₄.trans (hle.trans h₁)))
  -- Each end of the overlap is `0`, `1`, `f 0 = a` or `f 1 = b`.
  have key (e : R) (he : e ∈ Icc (0 ⊔ (a ⊓ b)) (1 ⊓ (a ⊔ b)))
      (hcases : e = 0 ∨ e = 1 ∨ e = a ∨ e = b) :
      ∃ u, lineMap a b u = e ∧ u ∈ Icc (0 : R) 1 ∧ lineMap a b u ∈ Icc (0 : R) 1 ∧
        (u = 0 ∨ u = 1 ∨ lineMap a b u = 0 ∨ lineMap a b u = 1) := by
    rw [← hI] at he
    obtain ⟨he₁, u, hu, rfl⟩ := he
    refine ⟨u, rfl, hu, he₁, ?_⟩
    rcases hcases with h | h | h | h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
    · exact .inl ((lineMap_eq_left_iff.1 h).resolve_left hab)
    · exact .inr (.inl ((lineMap_eq_right_iff.1 h).resolve_left hab))
  obtain ⟨u₁, hu₁, h₁⟩ := key _ (left_mem_Icc.2 hlt.le) (by
    rcases max_choice 0 (a ⊓ b) with h | h <;> rw [h]
    · exact .inl rfl
    · rcases min_choice a b with h' | h' <;> rw [h'] <;> simp)
  obtain ⟨u₂, hu₂, h₂⟩ := key _ (right_mem_Icc.2 hlt.le) (by
    rcases min_choice 1 (a ⊔ b) with h | h <;> rw [h]
    · exact .inr (.inl rfl)
    · rcases max_choice a b with h' | h' <;> rw [h'] <;> simp)
  refine ⟨u₁, u₂, hu₁ ▸ hu₂ ▸ hlt.ne, ?_⟩
  rintro u (rfl | rfl)
  exacts [h₁, h₂]

variable [AddCommGroup V] [Module R V] [AddTorsor V P] [AddCommGroup W] [Module R W]
  [AddTorsor W Q] {poly : Polygon P n} {π : P →ᵃ[R] Q}

/-- **Two distinct edges cross at most once.** For an affine regular projection `π` of a simple
polygon, two distinct edges contain at most one pair of points with the same image under `π`. For
consecutive edges this pair is their common vertex, taken twice. -/
theorem IsRegularProjection.subsingleton_setOf_mem_edgeSet (hs : poly.IsSimple R)
    (hπ : poly.IsRegularProjection R π) {i j : Fin n} (hij : i ≠ j) :
    {p : P × P | p.1 ∈ poly.edgeSet R i ∧ p.2 ∈ poly.edgeSet R j ∧ π p.1 = π p.2}.Subsingleton := by
  have hinj (k : Fin n) := hπ.injOn_edgeSet (hs.hasNondegenerateEdges k)
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
  obtain ⟨u₁, u₂, hne₁₂, hu⟩ := exists_lineMap_endpoint ht ht' (by rw [← hh, ht₀]; exact hsI)
    (by rw [← hh, ht₁]; exact hsI') (by rw [← hh, ← hh, ht₀, ht₁]; exact hss')
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
    exact hyx (hπ.injOn_edgeSet (hs.hasNondegenerateEdges i) hyj hxi hπyx)
  exact mem_iUnion₂.2 ⟨i, j, mem_iUnion.2 ⟨hij, (x, y), ⟨hxi, hyj, hπyx.symm⟩, rfl⟩⟩

end Finite

end Polygon
