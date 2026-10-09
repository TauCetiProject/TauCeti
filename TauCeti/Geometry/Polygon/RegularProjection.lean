/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Polygon.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Topology.MetricSpace.HausdorffDimension
import TauCeti.Geometry.Polygon.Basic
import TauCeti.LinearAlgebra.CrossProduct

/-!
# Regular projections of polygons

A knot diagram is the image of a polygonal knot `k ⊆ ℝ³` under a projection to a plane, together
with crossing information, and it can only be read off when the projection is *regular*: every
point of the image has at most two preimages on `k`, and no vertex of `k` is mapped onto a double
point. This is the regular position of Crowell and Fox (Chapter I).

This file defines the regularity condition, `Polygon.IsRegularProjection R poly π`, for an
arbitrary map `π` out of the ambient affine space of a polygon `poly : Polygon P n` (Mathlib's
`Polygon`), and proves that regular projections are generic. Projecting along a direction
`d : V` is the quotient map `V → V ⧸ ℝ ∙ d`, after choosing an origin `p₀ : P`; its fibres are the
lines parallel to `d`. For a polygon in a three-dimensional real affine space, the directions `d`
along which the projection is regular form a dense subset of `V`
(`Polygon.dense_setOf_isRegularProjection`). In particular every polygon, and so every polygonal
knot in `ℝ³`, has a regular projection along a nonzero direction
(`Polygon.exists_ne_zero_isRegularProjection`). Regularity of a projection depends only on its
fibres on the polygon (`Polygon.isRegularProjection_congr`), so the quotient map may be replaced
by any projection onto a plane with the same fibres, such as a coordinate projection. Projecting
along a nondegenerate edge is never regular (`Polygon.not_isRegularProjection_edge`).

## Main definitions

* `Polygon.IsRegularProjection R poly π`: no three distinct points of the polygon have the same
  image under `π`, and no vertex has the same image as another point of the polygon.

## Main results

* `Polygon.isRegularProjection_congr`: regularity only depends on the fibres of the projection on
  the polygon.
* `Polygon.not_isRegularProjection_edge`: projecting along a nondegenerate edge is not regular.
* `Polygon.dense_setOf_isRegularProjection`: the directions of regular projections of a polygon in
  a three-dimensional real affine space are dense.
* `Polygon.exists_ne_zero_isRegularProjection`: every such polygon has a regular projection along
  a nonzero direction.

## Implementation notes

The irregular directions are covered by finitely many ranges of differentiable maps
`ℝ × ℝ → V`, so they have Hausdorff dimension at most `2` and their complement is dense
(`dense_compl_of_dimH_lt_finrank`). A line parallel to `d` through a vertex and a point `x` of
the polygon has direction `x -ᵥ poly i`, with `x` running along an edge. For three points
`x`, `y`, `z` of the edges `i`, `j`, `k` on a line parallel to `d`, the line lies in the plane
through `y` containing the line of edge `i`, and in the one containing the line of edge `k`.
Writing these planes through their normal vectors, `d` is proportional to the cross product of the
two normals, a quadratic function of the position of `y` on edge `j`, unless `d` lies in the plane
spanned by the two edge directions, or the two edges are parallel and `d` lies in the plane
containing both of them. Cross products are taken after identifying `V` with `ℝ³` by a linear
equivalence.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Springer GTM 57 (1977), Chapter I,
  for knot projections in regular position.
* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, for regular projections of polygonal knots.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1,
  for knot diagrams obtained from projections in general position.
-/

public section

open Set Module

namespace Polygon

variable {R V P Q Q' : Type*} {n : ℕ}

section Defs

variable [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable (R) in
/-- A map `π` is a **regular projection** of the polygon `poly` when no three distinct points of
the polygon have the same image under `π`, and no vertex has the same image as another point of
the polygon. -/
structure IsRegularProjection (poly : Polygon P n) (π : P → Q) : Prop where
  /-- No three distinct points of the polygon have the same image. -/
  eq_or_eq_or_eq_of_apply_eq ⦃x y z : P⦄ : x ∈ poly.boundary R → y ∈ poly.boundary R →
    z ∈ poly.boundary R → π x = π y → π x = π z → x = y ∨ x = z ∨ y = z
  /-- No vertex has the same image as another point of the polygon. -/
  eq_vertex_of_apply_eq (i : Fin n) ⦃x : P⦄ : x ∈ poly.boundary R → π x = π (poly i) →
    x = poly i

variable [IsOrderedRing R] {poly : Polygon P n}

/-- Regularity of a projection only depends on its fibres on the polygon. -/
theorem isRegularProjection_congr {π : P → Q} {π' : P → Q'}
    (h : ∀ x ∈ poly.boundary R, ∀ y ∈ poly.boundary R, π x = π y ↔ π' x = π' y) :
    poly.IsRegularProjection R π ↔ poly.IsRegularProjection R π' := by
  refine ⟨fun hπ ↦ ⟨fun x y z hx hy hz hxy hxz ↦ ?_, fun i x hx hxi ↦ ?_⟩,
    fun hπ ↦ ⟨fun x y z hx hy hz hxy hxz ↦ ?_, fun i x hx hxi ↦ ?_⟩⟩
  · exact hπ.eq_or_eq_or_eq_of_apply_eq hx hy hz ((h x hx y hy).2 hxy) ((h x hx z hz).2 hxz)
  · exact hπ.eq_vertex_of_apply_eq i hx ((h x hx _ (poly.apply_mem_boundary R i)).2 hxi)
  · exact hπ.eq_or_eq_or_eq_of_apply_eq hx hy hz ((h x hx y hy).1 hxy) ((h x hx z hz).1 hxz)
  · exact hπ.eq_vertex_of_apply_eq i hx ((h x hx _ (poly.apply_mem_boundary R i)).1 hxi)

/-- Projecting along a nondegenerate edge of a polygon is not a regular projection: both endpoints
of the edge have the same image. -/
theorem not_isRegularProjection_edge (p₀ : P) {i : Fin n} (hi : poly i ≠ poly (finRotate n i)) :
    ¬poly.IsRegularProjection R fun p ↦
      (Submodule.Quotient.mk (p -ᵥ p₀) : V ⧸ R ∙ (poly (finRotate n i) -ᵥ poly i)) := by
  intro h
  refine hi (h.eq_vertex_of_apply_eq i
    (mem_iUnion.2 ⟨i, poly.apply_finRotate_mem_edgeSet R i⟩) ?_).symm
  rw [Submodule.Quotient.eq, vsub_sub_vsub_cancel_right]
  exact Submodule.mem_span_singleton_self _

end Defs

section Dense

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [AddTorsor V P]

/-- The direction `poly (i + 1) -ᵥ poly i` of the edge `i` of a polygon. -/
private def edgeVector (poly : Polygon P n) (i : Fin n) : V :=
  poly (finRotate n i) -ᵥ poly i

private theorem exists_eq_smul_edgeVector_vadd {poly : Polygon P n} {x : P}
    (hx : x ∈ poly.boundary ℝ) : ∃ i : Fin n, ∃ t : ℝ, x = t • poly.edgeVector i +ᵥ poly i := by
  obtain ⟨i, t, -, rfl⟩ := mem_boundary_iff.1 hx
  exact ⟨i, t, AffineMap.lineMap_apply _ _ _⟩

/-- A nonzero vector between two points of a line parallel to `d` is a nonzero multiple of `d`. -/
private theorem ne_zero_of_smul_eq_vsub {a : ℝ} {d : V} {x y : P} (h : a • d = x -ᵥ y)
    (hxy : x ≠ y) : a ≠ 0 := by
  rintro rfl
  exact hxy (eq_of_vsub_eq_zero (by simpa using h.symm))

/-- The `(i, j, k)` term of `irregularCover`: the directions of irregular projections coming from
a vertex `poly i` and a point of edge `j`, or from three points of the edges `i`, `j`, `k`. -/
private def irregularCoverTerm (poly : Polygon P n) (e : V ≃L[ℝ] (Fin 3 → ℝ)) (i j k : Fin n) :
    Set V :=
  (range fun p : ℝ × ℝ ↦ p.1 • ((poly j -ᵥ poly i) + p.2 • poly.edgeVector j)) ∪
  (range fun p : ℝ × ℝ ↦ p.1 • poly.edgeVector i + p.2 • poly.edgeVector k) ∪
  (range fun p : ℝ × ℝ ↦ p.1 • poly.edgeVector i + p.2 • (poly k -ᵥ poly i)) ∪
  (range fun p : ℝ × ℝ ↦ p.1 • e.symm (crossProduct
    (crossProduct (e (poly.edgeVector i)) (e ((poly j -ᵥ poly i) + p.2 • poly.edgeVector j)))
    (crossProduct (e (poly.edgeVector k)) (e ((poly j -ᵥ poly k) + p.2 • poly.edgeVector j)))))

/-- A set of Hausdorff dimension at most `2` containing the directions of the irregular
projections of `poly`. -/
private def irregularCover (poly : Polygon P n) (e : V ≃L[ℝ] (Fin 3 → ℝ)) : Set V :=
  ⋃ ijk : Fin n × Fin n × Fin n, irregularCoverTerm poly e ijk.1 ijk.2.1 ijk.2.2

private theorem dimH_irregularCover_le (poly : Polygon P n) (e : V ≃L[ℝ] (Fin 3 → ℝ)) :
    dimH (irregularCover poly e) ≤ 2 := by
  have hle {f : ℝ × ℝ → V} (hf : Differentiable ℝ f) : dimH (range f) ≤ 2 := by
    simpa using hf.dimH_range_le
  refine (dimH_iUnion _).trans_le (iSup_le fun ijk ↦ ?_)
  simp only [irregularCoverTerm, dimH_union, max_le_iff]
  refine ⟨⟨⟨hle (by fun_prop), hle (by fun_prop)⟩, hle (by fun_prop)⟩, hle ?_⟩
  -- the last parametrization is a quadratic polynomial in the second coordinate
  set A := e (poly.edgeVector ijk.1)
  set B := e (poly.edgeVector ijk.2.2)
  set C := e (poly.edgeVector ijk.2.1)
  set a := e (poly ijk.2.1 -ᵥ poly ijk.1)
  set b := e (poly ijk.2.1 -ᵥ poly ijk.2.2)
  convert (differentiable_fst.smul (e.symm.differentiable.comp
    (f := fun p : ℝ × ℝ ↦ crossProduct (crossProduct A a) (crossProduct B b) +
      p.2 • (crossProduct (crossProduct A a) (crossProduct B C) +
        crossProduct (crossProduct A C) (crossProduct B b)) +
      (p.2 * p.2) • crossProduct (crossProduct A C) (crossProduct B C)) (by fun_prop))) using 1
  ext p : 1
  simp only [Pi.smul_apply', Function.comp_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply]
  module

/-- A line parallel to `d` through a vertex `poly i` and another point `x` of the polygon. -/
private theorem mem_irregularCover_of_vertex {poly : Polygon P n} (e : V ≃L[ℝ] (Fin 3 → ℝ))
    {d : V} {i : Fin n} {x : P} {a : ℝ} (hx : x ∈ poly.boundary ℝ)
    (ha : a • d = x -ᵥ poly i) (hne : x ≠ poly i) : d ∈ irregularCover poly e := by
  obtain ⟨j, t, rfl⟩ := exists_eq_smul_edgeVector_vadd hx
  have ha0 := ne_zero_of_smul_eq_vsub ha hne
  refine mem_iUnion.2 ⟨(i, j, j), Or.inl (Or.inl (Or.inl ⟨(a⁻¹, t), ?_⟩))⟩
  rw [vadd_vsub_assoc] at ha
  simp only
  rw [add_comm, ← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]

/-- Three points of the edges `i`, `j`, `k` on a line parallel to `d`, with linearly independent
directions of the edges `i` and `k`. Here `y = b • edgeVector j +ᵥ poly j` is the point of edge
`j`, and `hyi`, `hyk` express `y` from the points `a • edgeVector i +ᵥ poly i` and
`c • edgeVector k +ᵥ poly k` of the line. -/
private theorem mem_irregularCover_of_linearIndependent {poly : Polygon P n}
    (e : V ≃L[ℝ] (Fin 3 → ℝ)) {d : V} {i j k : Fin n} {a b c α β : ℝ}
    (hind : LinearIndependent ℝ ![poly.edgeVector i, poly.edgeVector k])
    (hyi : (poly j -ᵥ poly i) + b • poly.edgeVector j = a • poly.edgeVector i - α • d)
    (hyk : (poly j -ᵥ poly k) + b • poly.edgeVector j = c • poly.edgeVector k + β • d)
    (hα : α ≠ 0) (hβ : β ≠ 0) : d ∈ irregularCover poly e := by
  by_cases ht : e (poly.edgeVector i) ⬝ᵥ crossProduct (e (poly.edgeVector k)) (e d) = 0
  · -- `d` lies in the plane spanned by the directions of the edges `i` and `k`
    have hind' : LinearIndependent ℝ ![e (poly.edgeVector i), e (poly.edgeVector k)] := by
      convert hind.map' (e : V →ₗ[ℝ] Fin 3 → ℝ) e.toLinearEquiv.ker using 1
      ext m : 1
      fin_cases m <;> simp
    rw [← triple_product_permutation, TauCeti.triple_product_eq_zero_iff_mem_span_pair hind',
      Submodule.mem_span_pair] at ht
    obtain ⟨s, t, hst⟩ := ht
    refine mem_iUnion.2 ⟨(i, j, k), Or.inl (Or.inl (Or.inr ⟨(s, t), ?_⟩))⟩
    apply e.injective
    rw [map_add, map_smul, map_smul]
    exact hst
  · -- `d` is proportional to the cross product of the normals of the planes through `y`
    -- containing the lines of the edges `i` and `k`
    have key : crossProduct
        (crossProduct (e (poly.edgeVector i)) (e ((poly j -ᵥ poly i) + b • poly.edgeVector j)))
        (crossProduct (e (poly.edgeVector k)) (e ((poly j -ᵥ poly k) + b • poly.edgeVector j))) =
        (-(α * β) * (e (poly.edgeVector i) ⬝ᵥ crossProduct (e (poly.edgeVector k)) (e d))) •
          e d := by
      rw [hyi, hyk]
      simp only [map_sub, map_add, map_smul, cross_self, smul_zero, zero_sub, zero_add,
        LinearMap.smul_apply, map_neg, LinearMap.neg_apply, TauCeti.cross_cross_cross_eq_smul]
      module
    refine mem_iUnion.2 ⟨(i, j, k), Or.inr ⟨((-(α * β) *
      (e (poly.edgeVector i) ⬝ᵥ crossProduct (e (poly.edgeVector k)) (e d)))⁻¹, b), ?_⟩⟩
    simp only
    rw [key, map_smul, e.symm_apply_apply, smul_smul,
      inv_mul_cancel₀ (mul_ne_zero (neg_ne_zero.2 (mul_ne_zero hα hβ)) ht), one_smul]

/-- Three distinct points of the polygon on a line parallel to `d`. -/
private theorem mem_irregularCover_of_triple {poly : Polygon P n} (e : V ≃L[ℝ] (Fin 3 → ℝ))
    {d : V} {x y z : P} {α γ : ℝ} (hx : x ∈ poly.boundary ℝ) (hy : y ∈ poly.boundary ℝ)
    (hz : z ∈ poly.boundary ℝ) (hα : α • d = x -ᵥ y) (hγ : γ • d = x -ᵥ z) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) : d ∈ irregularCover poly e := by
  obtain ⟨i, a, rfl⟩ := exists_eq_smul_edgeVector_vadd hx
  obtain ⟨j, b, rfl⟩ := exists_eq_smul_edgeVector_vadd hy
  obtain ⟨k, c, rfl⟩ := exists_eq_smul_edgeVector_vadd hz
  have hα0 := ne_zero_of_smul_eq_vsub hα hxy
  have hγ0 := ne_zero_of_smul_eq_vsub hγ hxz
  -- relations between the vectors joining the vertices `poly i`, `poly j` and `poly k`
  have hij := neg_vsub_eq_vsub_rev (poly i) (poly j)
  have hik := neg_vsub_eq_vsub_rev (poly i) (poly k)
  have hjk := vsub_sub_vsub_cancel_left (poly j) (poly k) (poly i)
  rw [vadd_vsub_vadd_comm] at hα hγ
  have hγα : γ - α ≠ 0 := by
    intro h
    apply hyz
    rw [← vsub_eq_zero_iff_eq, vadd_vsub_vadd_comm]
    linear_combination (norm := module) hα - hγ + h • d - hjk
  -- the point `y` of edge `j`, seen from the vertices `poly i` and `poly k`
  have hyi : (poly j -ᵥ poly i) + b • poly.edgeVector j = a • poly.edgeVector i - α • d := by
    linear_combination (norm := module) hα - hij
  have hyk : (poly j -ᵥ poly k) + b • poly.edgeVector j = c • poly.edgeVector k + (γ - α) • d := by
    linear_combination (norm := module) hα - hγ - hjk
  by_cases hwi : poly.edgeVector i = 0
  · -- the point of edge `i` is the vertex `poly i`
    rw [hwi, smul_zero, zero_vadd] at hxy
    refine mem_irregularCover_of_vertex e (a := -α) hy ?_ hxy.symm
    rw [vadd_vsub_assoc, add_comm, hyi, hwi, smul_zero, zero_sub, neg_smul]
  by_cases hind : LinearIndependent ℝ ![poly.edgeVector i, poly.edgeVector k]
  · exact mem_irregularCover_of_linearIndependent e hind hyi hyk hα0 hγα
  -- the edges `i` and `k` are parallel, and `d` lies in the plane containing both
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s • poly.edgeVector i = poly.edgeVector k := by
    simpa [LinearIndependent.pair_iff' hwi] using hind
  have hzx : -γ • d = (c * s - a) • poly.edgeVector i + (poly k -ᵥ poly i) := by
    linear_combination (norm := module) -hγ - c • hs + hik
  refine mem_iUnion.2 ⟨(i, j, k), Or.inl (Or.inr ⟨((-γ)⁻¹ * (c * s - a), (-γ)⁻¹), ?_⟩)⟩
  simp only
  rw [mul_smul, ← smul_add, ← hzx, smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 hγ0), one_smul]

/-- **Regular projections of a polygon are dense.** For a polygon in a three-dimensional real
affine space, the directions `d` for which projecting along `d`, the quotient map onto `V ⧸ ℝ ∙ d`
after choosing an origin `p₀`, is a regular projection of the polygon form a dense subset of
`V`. -/
theorem dense_setOf_isRegularProjection (hV : finrank ℝ V = 3) (poly : Polygon P n) (p₀ : P) :
    Dense {d : V | poly.IsRegularProjection ℝ
      fun p ↦ (Submodule.Quotient.mk (p -ᵥ p₀) : V ⧸ ℝ ∙ d)} := by
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hV
  let e : V ≃L[ℝ] (Fin 3 → ℝ) :=
    (LinearEquiv.ofFinrankEq V (Fin 3 → ℝ) (by simp [hV])).toContinuousLinearEquiv
  refine (dense_compl_of_dimH_lt_finrank
    ((dimH_irregularCover_le poly e).trans_lt ?_)).mono fun d hd ↦ ?_
  · rw [hV]
    norm_num
  -- the fibres of the projection along `d` are the lines parallel to `d`
  have hfib {x y : P} (h : (Submodule.Quotient.mk (x -ᵥ p₀) : V ⧸ ℝ ∙ d) =
      Submodule.Quotient.mk (y -ᵥ p₀)) : ∃ a : ℝ, a • d = x -ᵥ y := by
    rwa [Submodule.Quotient.eq, vsub_sub_vsub_cancel_right, Submodule.mem_span_singleton] at h
  refine ⟨fun x y z hx hy hz hxy hxz ↦ ?_, fun i x hx h ↦ ?_⟩
  · obtain ⟨α, hα⟩ := hfib hxy
    obtain ⟨γ, hγ⟩ := hfib hxz
    by_contra! hne
    exact hd (mem_irregularCover_of_triple e hx hy hz hα hγ hne.1 hne.2.1 hne.2.2)
  · obtain ⟨a, ha⟩ := hfib h
    by_contra hne
    exact hd (mem_irregularCover_of_vertex e hx ha hne)

/-- Every polygon in a three-dimensional real affine space has a regular projection along some
nonzero direction `d`. -/
theorem exists_ne_zero_isRegularProjection (hV : finrank ℝ V = 3) (poly : Polygon P n)
    (p₀ : P) : ∃ d : V, d ≠ 0 ∧ poly.IsRegularProjection ℝ
      fun p ↦ (Submodule.Quotient.mk (p -ᵥ p₀) : V ⧸ ℝ ∙ d) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨d, hd0, hd⟩ := (dense_setOf_isRegularProjection hV poly p₀).inter_open_nonempty
    {0}ᶜ isOpen_compl_singleton ⟨v, hv⟩
  exact ⟨d, hd0, hd⟩

end Dense

end Polygon
