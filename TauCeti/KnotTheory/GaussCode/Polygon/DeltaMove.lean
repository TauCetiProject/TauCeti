/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Polygon.DeltaMove
public import TauCeti.Geometry.Polygon.Subdivision
public import TauCeti.KnotTheory.GaussCode.Polygon.Basic
import TauCeti.Analysis.Convex.Combination
import TauCeti.LinearAlgebra.AffineSpace.Basis
import TauCeti.LinearAlgebra.AffineSpace.Triangle.Exit
import TauCeti.Order.Monotone.Basic

/-!
# Δ-moves that do not change the Gauss code

A Δ-move (`Polygon.IsDeltaMove`) replaces edge `i` of a polygonal knot `poly`, from vertex `i` to
the next vertex, by the two other sides of a triangle through a new vertex `c`: the polygon becomes
`poly.insertVertex i c`. In the argument that diagrams of combinatorially equivalent polygonal
knots are related by Reidemeister moves (Lickorish, Chapter 1; Burde–Zieschang, Chapter 1), the
Δ-moves are cut into small ones, and the effect of each on the diagram is read off from how the
projection of its triangle meets the rest of the diagram. This file treats the two cases in which
the diagram only changes by a planar isotopy, so that the Gauss code is unchanged.

**No strand meets the moved edges** (`Polygon.gaussCode_insertVertex_of_disjoint`): if, for the
projection along `d`, edge `i` of `poly` contains no double point, and the two sides through `c`
contain no double point of `poly.insertVertex i c`, then the two Gauss codes are equal whenever the
projection is regular for both polygons. The Δ-move condition itself is not needed: the hypotheses
only concern the edges that change. Under these hypotheses both polygons have the same double
points (`Polygon.doublePoints_insertVertex_of_disjoint`), lying on the edges they share, and away
from edge `i` the two traversals differ by an increasing change of time running along the same
edges (`Polygon.exists_strictMono_boundaryParam_insertVertex`). So the crossing times correspond in
order, at the same points and along edges with the same directions, and
`Polygon.gaussCode_eq_of_strictMono` applies.

**One strand slides across the triangle** (`Polygon.gaussCode_insertVertex_of_crossing`): suppose
that the triangle `D = a a' c`, with `a = poly i` and `a'` the next vertex, projects onto a
nondegenerate triangle `T`, that edge `j` crosses edge `i` in the diagram, and that apart from edges
`i` and `j` the polygon meets the prism over `T` only in `a` and `a'`. Read edge `j` in the
barycentric coordinates of `T` (Mathlib's `AffineBasis.coord`); along the edge they are affine
functions of the parameter. The edge enters `T` across the side `a a'` and its endpoints lie outside
`T`, so it leaves `T` across one of the two other sides, the projections of the new edges, at a
single point, which is not a vertex (`TauCeti.exists_triangle_exit`). So after the move edge `j`
crosses the new edges exactly once, at the point `y` of the new edges over the point `y'` where it
leaves `T`, and every other crossing is unchanged. The crossing has only slid along edge `j`, from
`x'` to `y'`, past no other crossing, and from `x` on edge `i` to `y`. It stays on the same side:
the segment from `x` to `y` lies in `D` and the segment from `x'` to `y'` on edge `j`, which `D`
does not meet, so their difference never crosses zero along the way
(`Affine.Simplex.pos_iff_pos_of_disjoint`). It keeps its sign: the determinant of the edge
directions with `d`, as a function of the direction of the moving strand, vanishes on `y - x`, and
this forces the old and new directions `a' - a` and `c - a` (or `a' - c`) to give determinants of
the same sign. The codes are then compared by `Polygon.gaussCode_eq_of_strictMonoOn`, which allows
crossing points to move.

## Main results

* `Polygon.gaussCode_insertVertex_of_disjoint`: a Δ-move whose moved edges carry no crossings does
  not change the Gauss code of a regular projection.
* `Polygon.gaussCode_insertVertex_of_crossing`: a Δ-move across which a single strand of the
  diagram slides does not change the Gauss code of a regular projection.

## References

* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, for Δ-moves and the Reidemeister moves they induce on regular projections.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1,
  pp. 2–4, for triangle moves and their effect on link diagrams.
-/

public section

open Set Function AffineMap Module TauCeti

namespace Polygon

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P] {n : ℕ} [NeZero n]
  {poly : Polygon P n} {p₀ : P} {d : V}

/-- **A Δ-move away from the crossings does not change the Gauss code.** Let `poly` be a simple
polygon in a three-dimensional real affine space, and `poly.insertVertex i c` the simple polygon in
which edge `i` is replaced by the segments from vertex `i` to `c` and from `c` to the next vertex.
Suppose that the projection along `d` is regular for both polygons, that edge `i` of `poly`
contains no double point of `poly`, and that the two new segments contain no double point of
`poly.insertVertex i c`. Then the two polygons have the same Gauss code. The numbers of crossings
agree, and the codes are compared together with them. -/
theorem gaussCode_insertVertex_of_disjoint (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {i : Fin n} {c : P}
    (hs' : (poly.insertVertex i c).IsSimple ℝ)
    (hπ' : (poly.insertVertex i c).IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (hu : Disjoint (poly.edgeSet ℝ i) (poly.doublePoints ℝ (projAlong ℝ p₀ d)))
    (hvw : Disjoint (affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i)))
      ((poly.insertVertex i c).doublePoints ℝ (projAlong ℝ p₀ d)))
    (b : Basis (Fin 3) ℝ V) :
    (⟨_, gaussCode hs' hπ' b⟩ : Σ m, BasedOrientedGaussCode m) = ⟨_, gaussCode hs hπ b⟩ := by
  obtain ⟨φ, hφ, hφt, -⟩ := exists_strictMono_boundaryParam_insertVertex poly i c
  refine gaussCode_eq_of_strictMono b hs hπ hs' hπ' (doublePoints_insertVertex_of_disjoint hu hvw)
    hφ fun t ht ↦ ?_
  obtain ⟨ht₁, ht₂⟩ := mem_crossingTimes.1 ht
  -- A crossing time is not on edge `i`, which carries no double point.
  have hti : edgeIndexAt n t ≠ i := by
    intro hti
    refine disjoint_left.1 hu ?_ ht₂
    rw [boundaryParam_eq_edgePath_edgeIndexAt, hti]
    exact ⟨Int.fract t, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, rfl⟩
  obtain ⟨h₁, h₂, h₃⟩ := hφt t ht₁ hti
  exact ⟨h₁, h₂, 1, one_pos, by rw [h₃, one_smul]⟩

/-! ### A strand sliding across the triangle

The proof of `Polygon.gaussCode_insertVertex_of_crossing` runs in five stages, each cut into the
private lemmas below: the crossing of edges `i` and `j`; the point `y'` where edge `j` leaves the
projected triangle and the point `y` of the new edges over it; the correspondence of double points;
the change of time; and the over/under and sign checks. These lemmas are steps of that one
argument, stated about the data it constructs, and are not meant to be used on their own. Below,
`π` is the projection along `d`, `a = poly i` and `a' = poly (i + 1)` are the endpoints of edge `i`,
`D` is the triangle of the Δ-move, `N` is the union of the two new edges, `q` is the polygon
`poly.insertVertex i c`, and `x = a + r (a' - a)` on edge `i` crosses `x'` at the parameter `s₀`
of edge `j`. -/

omit [NeZero n] in
/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: if edges `i` and
`j` of a simple polygon cross at `x` over `x'` in a regular projection along `d`, then `d ≠ 0`, the
two edges are distinct, the endpoints of edge `i` do not lie on edge `j`, `x` and `x'` are double
points lying inside the two edges, and they are the only points of the polygon over `π x`. -/
private theorem exists_mem_Ioo_of_crossing (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {i j : Fin n} {x x' : P}
    (hx : x ∈ poly.edgeSet ℝ i) (hx' : x' ∈ poly.edgeSet ℝ j) (hxx' : x ≠ x')
    (hπx : projAlong ℝ p₀ d x = projAlong ℝ p₀ d x') :
    d ≠ 0 ∧ j ≠ i ∧ poly i ∉ poly.edgeSet ℝ j ∧ poly (finRotate n i) ∉ poly.edgeSet ℝ j ∧
      x ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d) ∧
      x' ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d) ∧
      (∀ z ∈ poly.boundary ℝ, projAlong ℝ p₀ d z = projAlong ℝ p₀ d x → z = x ∨ z = x') ∧
      (∃ r ∈ Ioo (0 : ℝ) 1, lineMap (poly i) (poly (finRotate n i)) r = x) ∧
      ∃ s ∈ Ioo (0 : ℝ) 1, poly.edgePath ℝ j s = x' := by
  have hji : j ≠ i := by
    rintro rfl
    exact hxx' (hπ.injOn_edgeSet j hx hx' hπx)
  -- Edges `i` and `j` cross only at `x` over `x'`, so they have no common point.
  have hsub {z : P} (hzi : z ∈ poly.edgeSet ℝ i) (hzj : z ∈ poly.edgeSet ℝ j) : False := by
    have h := Prod.mk.inj (hπ.subsingleton_setOf_mem_edgeSet hs hji.symm
      (show (z, z) ∈ _ from ⟨hzi, hzj, rfl⟩) (show (x, x') ∈ _ from ⟨hx, hx', hπx⟩))
    exact hxx' (h.1.symm.trans h.2)
  have hxb : x ∈ poly.boundary ℝ := subset_iUnion (poly.edgeSet ℝ) i hx
  have hx'b : x' ∈ poly.boundary ℝ := subset_iUnion (poly.edgeSet ℝ) j hx'
  have hxDP : x ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d) :=
    mem_doublePoints.2 ⟨hxb, x', hx'b, hxx'.symm, hπx.symm⟩
  have hx'DP : x' ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d) :=
    mem_doublePoints.2 ⟨hx'b, x, hxb, hxx', hπx⟩
  refine ⟨fun hd ↦ hxx' ?_, hji, hsub (apply_mem_edgeSet_self ℝ poly i),
    hsub (apply_finRotate_mem_edgeSet ℝ poly i), hxDP, hx'DP, fun z hz h ↦ ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := projAlong_eq_projAlong_iff.1 hπx
    rwa [hd, smul_zero, eq_comm, vsub_eq_zero_iff_eq] at ht
  · by_cases hzx : z = x
    · exact .inl hzx
    · exact .inr ((hπ.eq_doublePointPartner hxb hz hzx h).trans
        (hπ.eq_doublePointPartner hxb hx'b hxx'.symm hπx.symm).symm)
  · obtain ⟨r, hr, rfl⟩ := hx
    refine ⟨r, ⟨hr.1.lt_of_ne' ?_, hr.2.lt_of_ne ?_⟩, rfl⟩ <;> rintro rfl
    · exact hπ.apply_notMem_doublePoints i (by simpa using hxDP)
    · exact hπ.apply_notMem_doublePoints _ (by simpa using hxDP)
  · obtain ⟨s, hsI, rfl⟩ := hx'
    refine ⟨s, ⟨hsI.1.lt_of_ne' ?_, hsI.2.lt_of_ne ?_⟩, rfl⟩ <;> rintro rfl
    · exact hπ.apply_notMem_doublePoints j (by simpa using hx'DP)
    · exact hπ.apply_notMem_doublePoints _ (by simpa using hx'DP)

omit [NeZero n] in
/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: when the
triangle of a Δ-move projects onto a nondegenerate triangle of the plane `V ⧸ ℝ ∙ d`, the projected
vertices form an affine basis `β`, the projection is injective on the triangle, and a point of the
plane lies in the projected triangle if and only if its coordinates in `β` are nonnegative. -/
private theorem exists_affineBasis_projAlong {i : Fin n} {c : P} (hΔ : poly.IsDeltaMove ℝ i c)
    (hT : AffineIndependent ℝ ![projAlong ℝ p₀ d (poly i),
      projAlong ℝ p₀ d (poly (finRotate n i)), projAlong ℝ p₀ d c])
    (hd : d ≠ 0) (b : Basis (Fin 3) ℝ V) :
    ∃ β : AffineBasis (Fin 3) ℝ (V ⧸ ℝ ∙ d), projAlong ℝ p₀ d (poly i) = β 0 ∧
      projAlong ℝ p₀ d (poly (finRotate n i)) = β 1 ∧ projAlong ℝ p₀ d c = β 2 ∧
      InjOn (projAlong ℝ p₀ d) hΔ.triangle.closedInterior ∧
      ∀ y, y ∈ projAlong ℝ p₀ d '' hΔ.triangle.closedInterior ↔ ∀ k, 0 ≤ β.coord k y := by
  set π := projAlong ℝ p₀ d
  have : FiniteDimensional ℝ V := Module.Finite.of_basis b
  have hfinQ : finrank ℝ (V ⧸ ℝ ∙ d) = 2 := by
    have h := Submodule.finrank_quotient_add_finrank (ℝ ∙ d)
    rw [finrank_span_singleton hd, finrank_eq_card_basis b, Fintype.card_fin] at h
    omega
  let β : AffineBasis (Fin 3) ℝ (V ⧸ ℝ ∙ d) :=
    ⟨_, hT, hT.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 (by rw [Fintype.card_fin, hfinQ])⟩
  -- Points of the triangle are recovered from the coordinates of their projections.
  have hπcomb (w : Fin 3 → ℝ) (hw : ∑ k, w k = 1) :
      π (Finset.univ.affineCombination ℝ hΔ.triangle.points w) =
        Finset.univ.affineCombination ℝ β w := by
    rw [Finset.map_affineCombination _ _ _ hw, IsDeltaMove.triangle_points]
    congr 1
  have hDrep {p : P} (hp : p ∈ hΔ.triangle.closedInterior) :
      Finset.univ.affineCombination ℝ hΔ.triangle.points (fun k ↦ β.coord k (π p)) = p ∧
        ∀ k, 0 ≤ β.coord k (π p) := by
    obtain ⟨w, hw, hwI, rfl⟩ := hp
    have hc (k) : β.coord k (π (Finset.univ.affineCombination ℝ hΔ.triangle.points w)) = w k := by
      rw [hπcomb w hw, β.coord_apply_combination_of_mem (Finset.mem_univ k) hw]
    exact ⟨by simp only [hc], fun k ↦ by rw [hc]; exact (hwI k).1⟩
  refine ⟨β, rfl, rfl, rfl, fun p₁ hp₁ p₂ hp₂ h ↦ by rw [← (hDrep hp₁).1, ← (hDrep hp₂).1, h],
    fun y ↦ ⟨?_, fun hy ↦ ?_⟩⟩
  · rintro ⟨p, hp, rfl⟩
    exact (hDrep hp).2
  · have hsum := β.sum_coord_apply_eq_one y
    rw [Fin.sum_univ_three] at hsum
    have hw : ∑ k, β.coord k y = 1 := β.sum_coord_apply_eq_one y
    refine ⟨_, (Affine.Simplex.affineCombination_mem_closedInterior_iff hw).2
      fun k ↦ ⟨hy k, ?_⟩, ?_⟩
    · fin_cases k <;> simp <;> linarith [hy 0, hy 1, hy 2]
    · rw [hπcomb _ hw, β.affineCombination_coord_eq_self]

/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: if every point
of an edge other than edges `i` and `j` projecting into `π D` is `a` or `a'`, which do not lie on
edge `j`, then the endpoints of edge `j` project outside `π D`. -/
private theorem projAlong_notMem_image_closedInterior (hs : poly.IsSimple ℝ) {i j : Fin n}
    {c : P} (hΔ : poly.IsDeltaMove ℝ i c)
    (hprism : ∀ k, k ≠ i → k ≠ j → ∀ z ∈ poly.edgeSet ℝ k,
      projAlong ℝ p₀ d z ∈ projAlong ℝ p₀ d '' hΔ.triangle.closedInterior →
        z = poly i ∨ z = poly (finRotate n i))
    (ha : poly i ∉ poly.edgeSet ℝ j) (ha' : poly (finRotate n i) ∉ poly.edgeSet ℝ j) :
    projAlong ℝ p₀ d (poly j) ∉ projAlong ℝ p₀ d '' hΔ.triangle.closedInterior ∧
      projAlong ℝ p₀ d (poly (finRotate n j)) ∉
        projAlong ℝ p₀ d '' hΔ.triangle.closedInterior := by
  have hvj : poly j ∈ poly.edgeSet ℝ j := apply_mem_edgeSet_self ℝ poly j
  have hvj' : poly (finRotate n j) ∈ poly.edgeSet ℝ j := apply_finRotate_mem_edgeSet ℝ poly j
  have hjj : finRotate n j ≠ j := fun h ↦ hs.hasNondegenerateEdges j (by rw [h])
  -- An endpoint of edge `j` lies on a neighbouring edge `k`, which carries no point over `π D`
  -- but `a` and `a'`.
  have key (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) {z : P} (hzk : z ∈ poly.edgeSet ℝ k)
      (hzj : z ∈ poly.edgeSet ℝ j) :
      projAlong ℝ p₀ d z ∉ projAlong ℝ p₀ d '' hΔ.triangle.closedInterior := fun hm ↦ by
    rcases hprism k hki hkj z hzk hm with rfl | rfl
    exacts [ha hzj, ha' hzj]
  refine ⟨key ((finRotate n).symm j) (fun h ↦ ha' ?_)
    (fun h ↦ hjj ((finRotate n).symm_apply_eq.1 h).symm) ?_ hvj,
    key (finRotate n j) (fun h ↦ ha ?_) hjj (apply_mem_edgeSet_self ℝ poly _) hvj'⟩
  · rw [← h, Equiv.apply_symm_apply]
    exact hvj
  · simpa using apply_finRotate_mem_edgeSet ℝ poly ((finRotate n).symm j)
  · rw [← h]
    exact hvj'

omit [NeZero n] in
/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: edge `j` avoids
the projections of the three vertices of the triangle of the Δ-move. -/
private theorem projAlong_edgePath_ne (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d))
    {i j : Fin n} {c : P}
    (hπ' : (poly.insertVertex i c).IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (hΔ : poly.IsDeltaMove ℝ i c) (hji : j ≠ i) (ha : poly i ∉ poly.edgeSet ℝ j)
    (ha' : poly (finRotate n i) ∉ poly.edgeSet ℝ j) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    projAlong ℝ p₀ d (poly.edgePath ℝ j s) ≠ projAlong ℝ p₀ d (poly i) ∧
      projAlong ℝ p₀ d (poly.edgePath ℝ j s) ≠ projAlong ℝ p₀ d (poly (finRotate n i)) ∧
      projAlong ℝ p₀ d (poly.edgePath ℝ j s) ≠ projAlong ℝ p₀ d c := by
  have hpj : poly.edgePath ℝ j s ∈ poly.edgeSet ℝ j := ⟨s, hs, rfl⟩
  have hb : poly.edgePath ℝ j s ∈ poly.boundary ℝ := subset_iUnion (poly.edgeSet ℝ) j hpj
  refine ⟨fun h ↦ ha (hπ.eq_vertex_of_apply_eq i hb h ▸ hpj),
    fun h ↦ ha' (hπ.eq_vertex_of_apply_eq _ hb h ▸ hpj), fun h ↦ ?_⟩
  -- Edge `j` is an edge of the new polygon, of which `c` is a vertex.
  have hjq : poly.edgeSet ℝ j ⊆ (poly.insertVertex i c).boundary ℝ := by
    rw [← edgeSet_insertVertex_succAbove poly i c hji]
    exact subset_iUnion ((poly.insertVertex i c).edgeSet ℝ) _
  have hc := hπ'.eq_vertex_of_apply_eq i.succ (hjq hpj)
  rw [insertVertex_apply_succ_self] at hc
  rcases hΔ.edgeSet_inter_closedInterior_subset hji
      ⟨hc h ▸ hpj, by simpa using hΔ.triangle.point_mem_closedInterior 2⟩ with h | h
  · exact hΔ.left_ne_apex h.symm
  · exact hΔ.apex_ne_right h

/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: in the
coordinates `f k` of an affine basis `β` on the projected vertices of the triangle of the Δ-move,
edge `j`, which crosses edge `i` at the parameter `s₀`, satisfies the hypotheses of
`TauCeti.exists_triangle_exit`, and so leaves the projected triangle at a single parameter
`s₁`. -/
private theorem exists_triangle_exit_edgePath (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {i j : Fin n} {c : P}
    (hπ' : (poly.insertVertex i c).IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (hΔ : poly.IsDeltaMove ℝ i c)
    (hprism : ∀ k, k ≠ i → k ≠ j → ∀ z ∈ poly.edgeSet ℝ k,
      projAlong ℝ p₀ d z ∈ projAlong ℝ p₀ d '' hΔ.triangle.closedInterior →
        z = poly i ∨ z = poly (finRotate n i))
    (hji : j ≠ i) (ha : poly i ∉ poly.edgeSet ℝ j)
    (ha' : poly (finRotate n i) ∉ poly.edgeSet ℝ j) {β : AffineBasis (Fin 3) ℝ (V ⧸ ℝ ∙ d)}
    (hβ0 : projAlong ℝ p₀ d (poly i) = β 0)
    (hβ1 : projAlong ℝ p₀ d (poly (finRotate n i)) = β 1) (hβ2 : projAlong ℝ p₀ d c = β 2)
    (hmemT : ∀ y, y ∈ projAlong ℝ p₀ d '' hΔ.triangle.closedInterior ↔ ∀ k, 0 ≤ β.coord k y)
    {f : Fin 3 → ℝ →ᵃ[ℝ] ℝ}
    (hf : ∀ k s, f k s = β.coord k (projAlong ℝ p₀ d (poly.edgePath ℝ j s)))
    (hsum : ∀ s, f 0 s + f 1 s + f 2 s = 1) {r s₀ : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1)
    (hπx : projAlong ℝ p₀ d (lineMap (poly i) (poly (finRotate n i)) r) =
      projAlong ℝ p₀ d (poly.edgePath ℝ j s₀)) :
    ∃ s₁ ∈ Ioo (0 : ℝ) 1, s₁ ≠ s₀ ∧ 0 < f 2 s₁ ∧
      ((f 1 s₁ = 0 ∧ 0 < f 0 s₁) ∨ (f 0 s₁ = 0 ∧ 0 < f 1 s₁)) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ f 2 s → (f 1 s = 0 ∧ 0 ≤ f 0 s ∨ f 0 s = 0 ∧ 0 ≤ f 1 s) →
        s = s₁) ∧
      ∀ s ∈ uIcc s₀ s₁, 0 ≤ f 0 s ∧ 0 ≤ f 1 s ∧ 0 ≤ f 2 s := by
  -- The endpoints of edge `j` project outside the triangle, and edge `j` avoids its vertices.
  obtain ⟨hout₀, hout₁⟩ := projAlong_notMem_image_closedInterior hs hΔ hprism ha ha'
  have hv {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) := projAlong_edgePath_ne hπ hπ' hΔ hji ha ha' hs
  set π := projAlong ℝ p₀ d
  -- The coordinates of the crossing with edge `i`, on the side from `β 0` to `β 1`.
  have hcl (k : Fin 3) :
      f k s₀ = lineMap (if k = 0 then (1 : ℝ) else 0) (if k = 1 then 1 else 0) r := by
    rw [hf, ← hπx, π.apply_lineMap, hβ0, hβ1, β.coord_lineMap]
  have hext {s : ℝ} (l : Fin 3) (h : ∀ k, f k s = if k = l then 1 else 0) :
      π (poly.edgePath ℝ j s) = β l :=
    β.ext_elem fun k ↦ by rw [← hf, h, β.coord_apply]
  refine exists_triangle_exit hsum hs₀ (by simp [hcl])
    (by simp [hcl, lineMap_apply_ring']; linarith [hr.2])
    (by simpa [hcl, lineMap_apply_ring'] using hr.1) ?_ ?_ ?_ ?_
  · rintro s hs ⟨h0, h1, h2⟩
    have hm : π (poly.edgePath ℝ j s) ∈ π '' hΔ.triangle.closedInterior :=
      (hmemT _).2 fun k ↦ by rw [← hf]; fin_cases k <;> assumption
    rcases hs with rfl | rfl
    · exact hout₀ (by simpa [edgePath] using hm)
    · exact hout₁ (by simpa [edgePath] using hm)
  · rintro s hs ⟨h1, h2⟩
    refine (hv hs).1 ?_
    rw [hext 0 fun k ↦ by fin_cases k <;> simp <;> linarith [hsum s], hβ0]
  · rintro s hs ⟨h0, h2⟩
    refine (hv hs).2.1 ?_
    rw [hext 1 fun k ↦ by fin_cases k <;> simp <;> linarith [hsum s], hβ1]
  · rintro s hs ⟨h0, h1⟩
    refine (hv hs).2.2 ?_
    rw [hext 2 fun k ↦ by fin_cases k <;> simp <;> linarith [hsum s], hβ2]

omit [NeZero n] in
/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: the two new
edges project onto the sides from `β 0` to `β 2` and from `β 2` to `β 1` of the projected
triangle, so on them coordinate `1` or coordinate `0` vanishes, and the others are nonnegative. -/
private theorem coord_projAlong_of_mem_union {i : Fin n} {c : P}
    {β : AffineBasis (Fin 3) ℝ (V ⧸ ℝ ∙ d)}
    (hβ0 : projAlong ℝ p₀ d (poly i) = β 0)
    (hβ1 : projAlong ℝ p₀ d (poly (finRotate n i)) = β 1) (hβ2 : projAlong ℝ p₀ d c = β 2) {z : P}
    (hz : z ∈ affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i))) :
    (β.coord 1 (projAlong ℝ p₀ d z) = 0 ∧ 0 ≤ β.coord 0 (projAlong ℝ p₀ d z) ∨
      β.coord 0 (projAlong ℝ p₀ d z) = 0 ∧ 0 ≤ β.coord 1 (projAlong ℝ p₀ d z)) ∧
      0 ≤ β.coord 2 (projAlong ℝ p₀ d z) := by
  rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · rw [(projAlong ℝ p₀ d).apply_lineMap, hβ0, hβ2, β.coord_lineMap, β.coord_lineMap,
      β.coord_lineMap]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, lineMap_apply_ring']
    exact ⟨.inl ⟨by ring, by linarith [ht.2]⟩, by linarith [ht.1]⟩
  · rw [(projAlong ℝ p₀ d).apply_lineMap, hβ1, hβ2, β.coord_lineMap, β.coord_lineMap,
      β.coord_lineMap]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, lineMap_apply_ring']
    exact ⟨.inr ⟨by ring, by linarith [ht.1]⟩, by linarith [ht.2]⟩

/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: edge `j`, which
crosses edge `i` at the parameter `s₀`, leaves `π D` at a parameter `s₁ ≠ s₀`, at its point `y'`
over a point of one of the new edges. Between `s₀` and `s₁` it runs over `π D`; it meets the
projection of the new edges only at `s₁`; `y'` does not lie over edge `i`; and `x` does not lie
over the new edges. -/
private theorem exists_exit (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {i j : Fin n} {c : P}
    (hπ' : (poly.insertVertex i c).IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (hΔ : poly.IsDeltaMove ℝ i c)
    (hprism : ∀ k, k ≠ i → k ≠ j → ∀ z ∈ poly.edgeSet ℝ k,
      projAlong ℝ p₀ d z ∈ projAlong ℝ p₀ d '' hΔ.triangle.closedInterior →
        z = poly i ∨ z = poly (finRotate n i))
    (hji : j ≠ i) (ha : poly i ∉ poly.edgeSet ℝ j)
    (ha' : poly (finRotate n i) ∉ poly.edgeSet ℝ j) {β : AffineBasis (Fin 3) ℝ (V ⧸ ℝ ∙ d)}
    (hβ0 : projAlong ℝ p₀ d (poly i) = β 0)
    (hβ1 : projAlong ℝ p₀ d (poly (finRotate n i)) = β 1) (hβ2 : projAlong ℝ p₀ d c = β 2)
    (hmemT : ∀ y, y ∈ projAlong ℝ p₀ d '' hΔ.triangle.closedInterior ↔ ∀ k, 0 ≤ β.coord k y)
    {r s₀ : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1)
    (hπx : projAlong ℝ p₀ d (lineMap (poly i) (poly (finRotate n i)) r) =
      projAlong ℝ p₀ d (poly.edgePath ℝ j s₀)) :
    ∃ s₁ ∈ Ioo (0 : ℝ) 1, s₁ ≠ s₀ ∧
      (∀ s ∈ uIcc s₀ s₁, projAlong ℝ p₀ d (poly.edgePath ℝ j s) ∈
        projAlong ℝ p₀ d '' hΔ.triangle.closedInterior) ∧
      (∀ z ∈ affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i)),
        ∀ s ∈ Icc (0 : ℝ) 1, projAlong ℝ p₀ d z = projAlong ℝ p₀ d (poly.edgePath ℝ j s) →
          s = s₁) ∧
      projAlong ℝ p₀ d (poly.edgePath ℝ j s₁) ∉ projAlong ℝ p₀ d '' poly.edgeSet ℝ i ∧
      projAlong ℝ p₀ d (lineMap (poly i) (poly (finRotate n i)) r) ∉ projAlong ℝ p₀ d ''
        (affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i))) ∧
      ((∃ ρ ∈ Ioo (0 : ℝ) 1, projAlong ℝ p₀ d (lineMap (poly i) c ρ) =
          projAlong ℝ p₀ d (poly.edgePath ℝ j s₁)) ∨
        ∃ t ∈ Ioo (0 : ℝ) 1, projAlong ℝ p₀ d (lineMap c (poly (finRotate n i)) t) =
          projAlong ℝ p₀ d (poly.edgePath ℝ j s₁)) := by
  set π := projAlong ℝ p₀ d
  set f : Fin 3 → ℝ →ᵃ[ℝ] ℝ := fun k ↦ (β.coord k).comp (π.comp (poly.edgePath ℝ j))
  have hf (k : Fin 3) (s : ℝ) : f k s = β.coord k (π (poly.edgePath ℝ j s)) := rfl
  have hsum (s : ℝ) : f 0 s + f 1 s + f 2 s = 1 := by
    have h := β.sum_coord_apply_eq_one (π (poly.edgePath ℝ j s))
    rwa [Fin.sum_univ_three, ← hf, ← hf, ← hf] at h
  obtain ⟨s₁, hs₁, hs₁₀, hpos₂, hside, huniq, hin⟩ :=
    exists_triangle_exit_edgePath hs hπ hπ' hΔ hprism hji ha ha' hβ0 hβ1 hβ2 hmemT hf hsum hr hs₀
      hπx
  have hsum := hsum s₁
  refine ⟨s₁, hs₁, hs₁₀, fun s hsu ↦ (hmemT _).2 fun k ↦ ?_, fun z hz s hs h ↦ ?_, ?_, ?_, ?_⟩
  · fin_cases k <;> simp only [← hf] <;> simp [hin s hsu]
  · have hc := coord_projAlong_of_mem_union hβ0 hβ1 hβ2 hz
    exact huniq s hs (by simpa only [hf, ← h] using hc.2) (by simpa only [hf, ← h] using hc.1)
  · -- Coordinate `2` is positive at `y'` and vanishes on edge `i`.
    rintro ⟨z, ⟨t, -, rfl⟩, hz⟩
    have h := congrArg (β.coord 2) hz
    rw [π.apply_lineMap, hβ0, hβ1, β.coord_lineMap, ← hf] at h
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, lineMap_same, AffineMap.const_apply] at h
    exact hpos₂.ne h
  · -- The coordinates of `x` are `1 - r`, `r` and `0`.
    rintro ⟨z, hz, h⟩
    have hc := (coord_projAlong_of_mem_union hβ0 hβ1 hβ2 hz).1
    rw [h, π.apply_lineMap, hβ0, hβ1, β.coord_lineMap, β.coord_lineMap] at hc
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, lineMap_apply_ring'] at hc
    rcases hc with ⟨h1, -⟩ | ⟨h0, -⟩
    · linarith [hr.1]
    · linarith [hr.2]
  · rcases hside with ⟨h1, h0⟩ | ⟨h0, h1⟩
    · refine .inl ⟨f 2 s₁, ⟨hpos₂, by linarith⟩, ?_⟩
      rw [π.apply_lineMap]
      refine β.ext_elem fun k ↦ ?_
      rw [hβ0, hβ2, β.coord_lineMap, ← hf]
      fin_cases k <;> simp [lineMap_apply_ring'] <;> linarith
    · refine .inr ⟨f 1 s₁, ⟨h1, by linarith⟩, ?_⟩
      rw [π.apply_lineMap]
      refine β.ext_elem fun k ↦ ?_
      rw [hβ1, hβ2, β.coord_lineMap, ← hf]
      fin_cases k <;> simp [lineMap_apply_ring'] <;> linarith

omit [NeZero n] in
/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: the linear form
`L v = det (v, w, d)`, for the direction `w` of edge `j`, vanishes on `y - x` for every point `y`
over a point of edge `j`, as it vanishes on `d` and on `w`. -/
private theorem exists_linearMap_det (b : Basis (Fin 3) ℝ V) {i j : Fin n} {r s₀ s₁ : ℝ}
    (hπx : projAlong ℝ p₀ d (lineMap (poly i) (poly (finRotate n i)) r) =
      projAlong ℝ p₀ d (poly.edgePath ℝ j s₀)) :
    ∃ L : V →ₗ[ℝ] ℝ, (∀ v, L v = b.det ![v, poly (finRotate n j) -ᵥ poly j, d]) ∧
      ∀ y, projAlong ℝ p₀ d y = projAlong ℝ p₀ d (poly.edgePath ℝ j s₁) →
        L (y -ᵥ lineMap (poly i) (poly (finRotate n i)) r) = 0 := by
  set w := poly (finRotate n j) -ᵥ poly j
  obtain ⟨L, hL⟩ : ∃ L : V →ₗ[ℝ] ℝ, ∀ v, L v = b.det ![v, w, d] := by
    refine ⟨b.det.toMultilinearMap.toLinearMap ![0, w, d] 0, fun v ↦ ?_⟩
    rw [MultilinearMap.toLinearMap_apply, AlternatingMap.coe_multilinearMap]
    congr 1
    funext k
    fin_cases k <;> rfl
  have hLw : L w = 0 := by
    rw [hL]
    exact b.det.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  have hLd : L d = 0 := by
    rw [hL]
    exact b.det.map_eq_zero_of_eq _ (i := 0) (j := 2) rfl (by decide)
  have hLπ {u v : P} (h : projAlong ℝ p₀ d u = projAlong ℝ p₀ d v) : L (u -ᵥ v) = 0 := by
    obtain ⟨t, ht⟩ := projAlong_eq_projAlong_iff.1 h
    rw [← ht, map_smul, hLd, smul_zero]
  refine ⟨L, hL, fun y hy ↦ ?_⟩
  have hy'x' : L (poly.edgePath ℝ j s₁ -ᵥ poly.edgePath ℝ j s₀) = 0 := by
    rw [edgePath, lineMap_apply, lineMap_apply, vadd_vsub_vadd_cancel_right, ← sub_smul, map_smul,
      hLw, smul_zero]
  rw [← vsub_add_vsub_cancel y (poly.edgePath ℝ j s₁), ← vsub_add_vsub_cancel
    (poly.edgePath ℝ j s₁) (poly.edgePath ℝ j s₀), map_add, map_add, hLπ hy, hy'x', hLπ hπx.symm,
    add_zero, add_zero]

omit [NeZero n] in
/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: a point
`y = a + ρ (c - a)` of the first new edge over `y'`, with `0 < ρ < 1`, lies in `D` and is reached
at the time `i + ρ` of `q`. The direction `c - a` of `q` there gives a linear form `L` vanishing on
`y - x` the sign of `a' - a`, since `ρ L (c - a) = r L (a' - a)`. -/
private theorem exists_lift_left {i : Fin n} {c : P} (hΔ : poly.IsDeltaMove ℝ i c)
    {L : V →ₗ[ℝ] ℝ} {r ρ : ℝ} {y' : P} (hr : r ∈ Ioo (0 : ℝ) 1) (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hπy : projAlong ℝ p₀ d (lineMap (poly i) c ρ) = projAlong ℝ p₀ d y')
    (hL : ∀ y, projAlong ℝ p₀ d y = projAlong ℝ p₀ d y' →
      L (y -ᵥ lineMap (poly i) (poly (finRotate n i)) r) = 0) :
    ∃ y τy, y ∈ hΔ.triangle.closedInterior ∧
      y ∈ affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i)) ∧
      projAlong ℝ p₀ d y = projAlong ℝ p₀ d y' ∧ τy ∈ Ioo ((i : ℕ) : ℝ) ((i : ℕ) + 2) ∧
      (poly.insertVertex i c).boundaryParam τy = y ∧
      SignType.sign (L (poly.insertVertex i c (finRotate (n + 1) (edgeIndexAt (n + 1) τy)) -ᵥ
        poly.insertVertex i c (edgeIndexAt (n + 1) τy))) =
        SignType.sign (L (poly (finRotate n i) -ᵥ poly i)) := by
  have hτ : edgeIndexAt (n + 1) (((i.castSucc : Fin (n + 1)) : ℕ) + ρ) = i.castSucc :=
    edgeIndexAt_natCast_add _ ⟨hρ.1.le, hρ.2⟩
  refine ⟨lineMap (poly i) c ρ, ((i.castSucc : Fin (n + 1)) : ℕ) + ρ,
    hΔ.affineSegment_left_subset_closedInterior ⟨ρ, ⟨hρ.1.le, hρ.2.le⟩, rfl⟩,
    .inl ⟨ρ, ⟨hρ.1.le, hρ.2.le⟩, rfl⟩, hπy, ?_, ?_, ?_⟩
  · rw [Fin.val_castSucc]
    exact ⟨by linarith [hρ.1], by linarith [hρ.2]⟩
  · rw [boundaryParam_natCast_add _ _ ⟨hρ.1.le, hρ.2.le⟩, edgePath_insertVertex_castSucc_self]
  · rw [hτ, Fin.finRotate_castSucc, insertVertex_apply_succ_self,
      insertVertex_apply_castSucc_self]
    have h : ρ * L (c -ᵥ poly i) = r * L (poly (finRotate n i) -ᵥ poly i) := by
      have h := hL _ hπy
      simp only [lineMap_vsub_lineMap_eq_vsub_add_smul_sub_smul, vsub_self,
        map_add, map_sub, map_smul, map_zero, smul_eq_mul] at h
      linear_combination h
    have h := congrArg SignType.sign h
    rwa [sign_mul, sign_mul, sign_pos hρ.1, sign_pos hr.1, one_mul, one_mul] at h

omit [NeZero n] in
/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: a point
`y = c + t (a' - c)` of the second new edge over `y'`, with `0 < t < 1`, lies in `D` and is reached
at the time `i + 1 + t` of `q`. The direction `a' - c` of `q` there gives a linear form `L`
vanishing on `y - x` the sign of `a' - a`, since `(1 - t) L (a' - c) = (1 - r) L (a' - a)`. -/
private theorem exists_lift_right {i : Fin n} {c : P} (hΔ : poly.IsDeltaMove ℝ i c)
    {L : V →ₗ[ℝ] ℝ} {r t : ℝ} {y' : P} (hr : r ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hπy : projAlong ℝ p₀ d (lineMap c (poly (finRotate n i)) t) = projAlong ℝ p₀ d y')
    (hL : ∀ y, projAlong ℝ p₀ d y = projAlong ℝ p₀ d y' →
      L (y -ᵥ lineMap (poly i) (poly (finRotate n i)) r) = 0) :
    ∃ y τy, y ∈ hΔ.triangle.closedInterior ∧
      y ∈ affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i)) ∧
      projAlong ℝ p₀ d y = projAlong ℝ p₀ d y' ∧ τy ∈ Ioo ((i : ℕ) : ℝ) ((i : ℕ) + 2) ∧
      (poly.insertVertex i c).boundaryParam τy = y ∧
      SignType.sign (L (poly.insertVertex i c (finRotate (n + 1) (edgeIndexAt (n + 1) τy)) -ᵥ
        poly.insertVertex i c (edgeIndexAt (n + 1) τy))) =
        SignType.sign (L (poly (finRotate n i) -ᵥ poly i)) := by
  have hτ : edgeIndexAt (n + 1) (((i.succ : Fin (n + 1)) : ℕ) + t) = i.succ :=
    edgeIndexAt_natCast_add _ ⟨ht.1.le, ht.2⟩
  refine ⟨lineMap c (poly (finRotate n i)) t, ((i.succ : Fin (n + 1)) : ℕ) + t,
    hΔ.affineSegment_right_subset_closedInterior ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩,
    .inr ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩, hπy, ?_, ?_, ?_⟩
  · rw [Fin.val_succ, Nat.cast_add_one]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · rw [boundaryParam_natCast_add _ _ ⟨ht.1.le, ht.2.le⟩, edgePath_insertVertex_succ_self]
  · rw [hτ, insertVertex_apply_finRotate_succ_self, insertVertex_apply_succ_self]
    have h : (1 - t) * L (poly (finRotate n i) -ᵥ c) =
        (1 - r) * L (poly (finRotate n i) -ᵥ poly i) := by
      have h := hL _ hπy
      have hca := congrArg L (vsub_sub_vsub_cancel_left c (poly i) (poly (finRotate n i)))
      simp only [lineMap_vsub_lineMap_eq_vsub_add_smul_sub_smul, map_add, map_sub,
        map_smul, smul_eq_mul] at h hca
      linear_combination -h - hca
    have h := congrArg SignType.sign h
    rwa [sign_mul, sign_mul, sign_pos (sub_pos.2 ht.2), sign_pos (sub_pos.2 hr.2), one_mul,
      one_mul] at h

omit [NeZero n] in
/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: the only double
point on edge `i` is its crossing point `x` with edge `j`. The partner of another one would lie on
an edge other than edges `i` and `j`, over `π D`, so it would be `a` or `a'`, which are not double
points. -/
private theorem eq_of_mem_edgeSet_of_mem_doublePoints (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {i j : Fin n} {c : P}
    (hΔ : poly.IsDeltaMove ℝ i c)
    (hprism : ∀ k, k ≠ i → k ≠ j → ∀ z ∈ poly.edgeSet ℝ k,
      projAlong ℝ p₀ d z ∈ projAlong ℝ p₀ d '' hΔ.triangle.closedInterior →
        z = poly i ∨ z = poly (finRotate n i))
    (hji : j ≠ i) {x x' z : P} (hx : x ∈ poly.edgeSet ℝ i) (hx' : x' ∈ poly.edgeSet ℝ j)
    (hπx : projAlong ℝ p₀ d x = projAlong ℝ p₀ d x') (hz : z ∈ poly.edgeSet ℝ i)
    (hzDP : z ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d)) : z = x := by
  obtain ⟨-, w, hw, hne, hπeq⟩ := mem_doublePoints.1 hzDP
  obtain ⟨k, hk⟩ := mem_iUnion.1 hw
  by_cases hki : k = i
  · rw [hki] at hk
    exact (hne (hπ.injOn_edgeSet i hk hz hπeq)).elim
  by_cases hkj : k = j
  · rw [hkj] at hk
    exact (Prod.mk.inj (hπ.subsingleton_setOf_mem_edgeSet hs hji.symm
      (show (z, w) ∈ _ from ⟨hz, hk, hπeq.symm⟩) (show (x, x') ∈ _ from ⟨hx, hx', hπx⟩))).1
  rcases hprism k hki hkj w hk (hπeq ▸ ⟨z, hΔ.edgeSet_subset_closedInterior hz, rfl⟩) with
    rfl | rfl <;>
    exact (hne (hπ.eq_vertex_of_apply_eq _ (subset_iUnion (poly.edgeSet ℝ) i hz)
      hπeq.symm).symm).elim

omit [NeZero n] in
/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: between the
parameters `s₀` and `s₁`, along which edge `j` runs over `π D`, its only double point is `x'`. -/
private theorem eq_of_mem_uIcc_of_mem_doublePoints (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {i j : Fin n} {c : P}
    (hΔ : poly.IsDeltaMove ℝ i c)
    (hprism : ∀ k, k ≠ i → k ≠ j → ∀ z ∈ poly.edgeSet ℝ k,
      projAlong ℝ p₀ d z ∈ projAlong ℝ p₀ d '' hΔ.triangle.closedInterior →
        z = poly i ∨ z = poly (finRotate n i))
    (hji : j ≠ i) {r s₀ s₁ : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1)
    (hs₁ : s₁ ∈ Ioo (0 : ℝ) 1)
    (hπx : projAlong ℝ p₀ d (lineMap (poly i) (poly (finRotate n i)) r) =
      projAlong ℝ p₀ d (poly.edgePath ℝ j s₀))
    (hin : ∀ s ∈ uIcc s₀ s₁, projAlong ℝ p₀ d (poly.edgePath ℝ j s) ∈
      projAlong ℝ p₀ d '' hΔ.triangle.closedInterior) {s : ℝ} (hsu : s ∈ uIcc s₀ s₁)
    (hDP : poly.edgePath ℝ j s ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d)) : s = s₀ := by
  have hsI : s ∈ Icc (0 : ℝ) 1 :=
    uIcc_subset_Icc (Ioo_subset_Icc_self hs₀) (Ioo_subset_Icc_self hs₁) hsu
  obtain ⟨-, w, hw, hne, hπeq⟩ := mem_doublePoints.1 hDP
  obtain ⟨k, hk⟩ := mem_iUnion.1 hw
  by_cases hki : k = i
  · rw [hki] at hk
    have h := (Prod.mk.inj (hπ.subsingleton_setOf_mem_edgeSet hs hji.symm
      (show (w, poly.edgePath ℝ j s) ∈ _ from ⟨hk, ⟨s, hsI, rfl⟩, hπeq⟩)
      (show (lineMap (poly i) (poly (finRotate n i)) r, poly.edgePath ℝ j s₀) ∈ _ from
        ⟨⟨r, Ioo_subset_Icc_self hr, rfl⟩, ⟨s₀, Ioo_subset_Icc_self hs₀, rfl⟩, hπx⟩))).2
    exact lineMap_injective ℝ (hs.hasNondegenerateEdges j) h
  by_cases hkj : k = j
  · rw [hkj] at hk
    exact (hne (hπ.injOn_edgeSet j hk ⟨s, hsI, rfl⟩ hπeq)).elim
  rcases hprism k hki hkj w hk (hπeq ▸ hin s hsu) with rfl | rfl <;>
    exact (hne (hπ.eq_vertex_of_apply_eq _ (subset_iUnion (poly.edgeSet ℝ) j ⟨s, hsI, rfl⟩)
      hπeq.symm).symm).elim

omit [NeZero n] in
/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: a point `w` of
`q` other than a point `z` of the new edges, with the same projection, is the point `y'` of edge
`j`, and then `z` is the point `y` over `y'`. The point `w` cannot lie on the new edges, on which
`π` is injective, nor on an edge of `poly` other than edges `i` and `j`, which carries no point over
`π D` but the vertices `a` and `a'` of `q`. -/
private theorem eq_of_mem_union_of_apply_eq {i j : Fin n} {c : P}
    (hπ' : (poly.insertVertex i c).IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (hΔ : poly.IsDeltaMove ℝ i c)
    (hprism : ∀ k, k ≠ i → k ≠ j → ∀ z ∈ poly.edgeSet ℝ k,
      projAlong ℝ p₀ d z ∈ projAlong ℝ p₀ d '' hΔ.triangle.closedInterior →
        z = poly i ∨ z = poly (finRotate n i))
    (hinjD : InjOn (projAlong ℝ p₀ d) hΔ.triangle.closedInterior) {s₁ : ℝ} {y : P}
    (hyD : y ∈ hΔ.triangle.closedInterior)
    (hπy : projAlong ℝ p₀ d y = projAlong ℝ p₀ d (poly.edgePath ℝ j s₁))
    (huniq : ∀ z ∈ affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i)),
      ∀ s ∈ Icc (0 : ℝ) 1, projAlong ℝ p₀ d z = projAlong ℝ p₀ d (poly.edgePath ℝ j s) →
        s = s₁)
    {z w : P} (hz : z ∈ affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i)))
    (hw : w ∈ (poly.insertVertex i c).boundary ℝ) (hne : w ≠ z)
    (h : projAlong ℝ p₀ d w = projAlong ℝ p₀ d z) : z = y ∧ w = poly.edgePath ℝ j s₁ := by
  have hND := union_subset hΔ.affineSegment_left_subset_closedInterior
    hΔ.affineSegment_right_subset_closedInterior
  have hzq : z ∈ (poly.insertVertex i c).boundary ℝ := by
    rw [boundary_insertVertex]
    exact .inr hz
  rw [boundary_insertVertex] at hw
  obtain ⟨k, hki, hk⟩ :=
    mem_iUnion₂.1 (hw.resolve_right fun hw ↦ hne (hinjD (hND hw) (hND hz) h))
  by_cases hkj : k = j
  · rw [hkj] at hk
    obtain ⟨s, hs, rfl⟩ := hk
    obtain rfl := huniq z hz s hs h.symm
    exact ⟨hinjD (hND hz) hyD (h.symm.trans hπy.symm), rfl⟩
  rcases hprism k hki hkj w hk (h ▸ ⟨z, hND hz, rfl⟩) with rfl | rfl
  · have := hπ'.eq_vertex_of_apply_eq i.castSucc hzq
    rw [insertVertex_apply_castSucc_self] at this
    exact (hne (this h.symm).symm).elim
  · have := hπ'.eq_vertex_of_apply_eq (finRotate (n + 1) i.succ) hzq
    rw [insertVertex_apply_finRotate_succ_self] at this
    exact (hne (this h.symm).symm).elim

/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: edge `j` leaves
`π D` at its point `y'` at a parameter `s₁ ≠ s₀`, over a point `y` of the new edges, reached at a
time `τy` of `q` along an edge whose direction gives `L = det (·, w, d)` the sign of `a' - a`, for
the direction `w` of edge `j`. The points `y` and `y'` form a double point of `q`, `y` does not lie
on `poly` and `x` does not lie on `q`; the only double point of `poly` on edge `j` from `x'` to
`y'` is `x'`; and a point of the new edges sharing its projection with another point of `q` is
`y`, the other point being `y'`. -/
private theorem exists_slide (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {i j : Fin n} {c : P}
    (hπ' : (poly.insertVertex i c).IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (hΔ : poly.IsDeltaMove ℝ i c)
    (hT : AffineIndependent ℝ ![projAlong ℝ p₀ d (poly i),
      projAlong ℝ p₀ d (poly (finRotate n i)), projAlong ℝ p₀ d c])
    (hprism : ∀ k, k ≠ i → k ≠ j → ∀ z ∈ poly.edgeSet ℝ k,
      projAlong ℝ p₀ d z ∈ projAlong ℝ p₀ d '' hΔ.triangle.closedInterior →
        z = poly i ∨ z = poly (finRotate n i))
    (b : Basis (Fin 3) ℝ V) (hd : d ≠ 0) (hji : j ≠ i) (ha : poly i ∉ poly.edgeSet ℝ j)
    (ha' : poly (finRotate n i) ∉ poly.edgeSet ℝ j) {r s₀ : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1)
    (hxDP : lineMap (poly i) (poly (finRotate n i)) r ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d))
    (hπx : projAlong ℝ p₀ d (lineMap (poly i) (poly (finRotate n i)) r) =
      projAlong ℝ p₀ d (poly.edgePath ℝ j s₀)) :
    ∃ s₁ ∈ Ioo (0 : ℝ) 1, s₁ ≠ s₀ ∧ ∃ y τy, ∃ L : V →ₗ[ℝ] ℝ,
      (∀ v, L v = b.det ![v, poly (finRotate n j) -ᵥ poly j, d]) ∧
      y ∈ hΔ.triangle.closedInterior ∧
      projAlong ℝ p₀ d y = projAlong ℝ p₀ d (poly.edgePath ℝ j s₁) ∧
      y ≠ poly.edgePath ℝ j s₁ ∧ y ∉ poly.boundary ℝ ∧
      y ∈ (poly.insertVertex i c).doublePoints ℝ (projAlong ℝ p₀ d) ∧
      poly.edgePath ℝ j s₁ ∈ (poly.insertVertex i c).doublePoints ℝ (projAlong ℝ p₀ d) ∧
      lineMap (poly i) (poly (finRotate n i)) r ∉ (poly.insertVertex i c).boundary ℝ ∧
      τy ∈ Ioo ((i : ℕ) : ℝ) ((i : ℕ) + 2) ∧ (poly.insertVertex i c).boundaryParam τy = y ∧
      SignType.sign (L (poly.insertVertex i c (finRotate (n + 1) (edgeIndexAt (n + 1) τy)) -ᵥ
        poly.insertVertex i c (edgeIndexAt (n + 1) τy))) =
        SignType.sign (L (poly (finRotate n i) -ᵥ poly i)) ∧
      (∀ s ∈ uIcc s₀ s₁, poly.edgePath ℝ j s ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d) →
        s = s₀) ∧
      ∀ z ∈ affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i)),
        ∀ w ∈ (poly.insertVertex i c).boundary ℝ, w ≠ z →
          projAlong ℝ p₀ d w = projAlong ℝ p₀ d z → z = y ∧ w = poly.edgePath ℝ j s₁ := by
  obtain ⟨β, hβ0, hβ1, hβ2, hinjD, hmemT⟩ := exists_affineBasis_projAlong hΔ hT hd b
  obtain ⟨s₁, hs₁, hs₁₀, hin, huniq, hy'i, hxN, hside⟩ :=
    exists_exit hs hπ hπ' hΔ hprism hji ha ha' hβ0 hβ1 hβ2 hmemT hr hs₀ hπx
  obtain ⟨L, hL, hLyx⟩ := exists_linearMap_det b (s₁ := s₁) hπx
  obtain ⟨y, τy, hyD, hyN, hπy, hτy, hbpy, hdiry⟩ := hside.elim
    (fun ⟨ρ, hρ, h⟩ ↦ exists_lift_left hΔ hr hρ h hLyx)
    fun ⟨t, ht, h⟩ ↦ exists_lift_right hΔ hr ht h hLyx
  have hy'j : poly.edgePath ℝ j s₁ ∈ poly.edgeSet ℝ j := ⟨s₁, Ioo_subset_Icc_self hs₁, rfl⟩
  have hyy' : y ≠ poly.edgePath ℝ j s₁ := fun h ↦ by
    rcases hΔ.edgeSet_inter_closedInterior_subset hji ⟨hy'j, h ▸ hyD⟩ with h' | h'
    exacts [ha (h' ▸ hy'j), ha' (h' ▸ hy'j)]
  have hyq : y ∈ (poly.insertVertex i c).boundary ℝ := by
    rw [boundary_insertVertex]
    exact .inr hyN
  have hy'q : poly.edgePath ℝ j s₁ ∈ (poly.insertVertex i c).boundary ℝ := by
    rw [← edgeSet_insertVertex_succAbove poly i c hji] at hy'j
    exact subset_iUnion ((poly.insertVertex i c).edgeSet ℝ) _ hy'j
  refine ⟨s₁, hs₁, hs₁₀, y, τy, L, hL, hyD, hπy, hyy',
    fun h ↦ hy'i ⟨y, hΔ.closedInterior_inter_boundary ▸ ⟨hyD, h⟩, hπy⟩,
    mem_doublePoints.2 ⟨hyq, _, hy'q, hyy'.symm, hπy.symm⟩,
    mem_doublePoints.2 ⟨hy'q, y, hyq, hyy', hπy⟩, fun h ↦ ?_, hτy, hbpy, hdiry,
    fun s hsu ↦ eq_of_mem_uIcc_of_mem_doublePoints hs hπ hΔ hprism hji hr hs₀ hs₁ hπx hin hsu,
    fun z hz w ↦ eq_of_mem_union_of_apply_eq hπ' hΔ hprism hinjD hyD hπy huniq hz⟩
  -- `x` lies neither on the new edges nor on another edge of `poly`, as it is not a vertex.
  rw [boundary_insertVertex] at h
  obtain ⟨k, hki, hk⟩ := mem_iUnion₂.1 (h.resolve_right fun h ↦ hxN ⟨_, h, rfl⟩)
  rcases hs.eq_vertex_of_mem_edgeSet (Ne.symm hki) ⟨r, Ioo_subset_Icc_self hr, rfl⟩ hk with
    ⟨-, h'⟩ | ⟨-, h'⟩ <;>
    exact hπ.apply_notMem_doublePoints _ (h' ▸ hxDP)

omit [NeZero n] in
/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: the
correspondence `g`, sending `x ↦ y` and `x' ↦ y'` and fixing every other point, maps the double
points of `poly` to those of `q`. A double point other than `x` and `x'` lies, with its partner,
off edge `i`, whose only double point is `x`; so both lie on `q`. -/
private theorem mapsTo_doublePoints_insertVertex {i : Fin n} {c : P} {g : P → P}
    {x x' y y' : P} (hgx : g x = y) (hgx' : g x' = y') (hgo : ∀ z, z ≠ x → z ≠ x' → g z = z)
    (hDPi : ∀ z ∈ poly.edgeSet ℝ i, z ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d) → z = x)
    (hpair : ∀ z ∈ poly.boundary ℝ, projAlong ℝ p₀ d z = projAlong ℝ p₀ d x → z = x ∨ z = x')
    (hyq : y ∈ (poly.insertVertex i c).doublePoints ℝ (projAlong ℝ p₀ d))
    (hy'q : y' ∈ (poly.insertVertex i c).doublePoints ℝ (projAlong ℝ p₀ d)) :
    MapsTo g (poly.doublePoints ℝ (projAlong ℝ p₀ d))
      ((poly.insertVertex i c).doublePoints ℝ (projAlong ℝ p₀ d)) := by
  intro z hz
  by_cases h₁ : z = x
  · rwa [h₁, hgx]
  by_cases h₂ : z = x'
  · rwa [h₂, hgx']
  rw [hgo z h₁ h₂]
  obtain ⟨hzb, w, hw, hne, hπeq⟩ := mem_doublePoints.1 hz
  have hoff {u : P} (hu : u ∈ poly.boundary ℝ) (hui : u ∉ poly.edgeSet ℝ i) :
      u ∈ (poly.insertVertex i c).boundary ℝ := by
    obtain ⟨k, hk⟩ := mem_iUnion.1 hu
    rw [boundary_insertVertex]
    exact .inl (mem_iUnion₂.2 ⟨k, fun h ↦ hui (h ▸ hk), hk⟩)
  have hwi : w ∉ poly.edgeSet ℝ i := fun h ↦ by
    have hwx := hDPi w h (mem_doublePoints.2 ⟨hw, z, hzb, hne.symm, hπeq.symm⟩)
    rw [hwx] at hπeq
    rcases hpair z hzb hπeq.symm with h' | h'
    exacts [h₁ h', h₂ h']
  exact mem_doublePoints.2 ⟨hoff hzb fun h ↦ h₁ (hDPi z h hz), w, hoff hw hwi, hne, hπeq⟩

omit [NeZero n] in
/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: every double
point of `q` comes from a double point of `poly` under the correspondence `g`. One on the new edges
is `y`, its partner being `y'`; otherwise both points lie on edges of `poly` other than edge `i`,
and form a double point of `poly` other than `x` and `x'`. -/
private theorem exists_mem_doublePoints_eq {i : Fin n} {c : P}
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {g : P → P} {x x' y y' : P}
    (hgx : g x = y) (hgx' : g x' = y') (hgo : ∀ z, z ≠ x → z ≠ x' → g z = z)
    (hxDP : x ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d))
    (hx'DP : x' ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d)) (hxx' : x ≠ x')
    (hπx : projAlong ℝ p₀ d x = projAlong ℝ p₀ d x')
    (hxq : x ∉ (poly.insertVertex i c).boundary ℝ)
    (hN : ∀ z ∈ affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i)),
      ∀ w ∈ (poly.insertVertex i c).boundary ℝ, w ≠ z →
        projAlong ℝ p₀ d w = projAlong ℝ p₀ d z → z = y ∧ w = y')
    {z : P} (hz : z ∈ (poly.insertVertex i c).doublePoints ℝ (projAlong ℝ p₀ d)) :
    ∃ z₀ ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d), g z₀ = z := by
  obtain ⟨hzb, w, hw, hne, hπeq⟩ := mem_doublePoints.1 hz
  by_cases hzN : z ∈ affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i))
  · obtain ⟨rfl, -⟩ := hN z hzN w hw hne hπeq
    exact ⟨x, hxDP, hgx⟩
  by_cases hwN : w ∈ affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i))
  · obtain ⟨-, rfl⟩ := hN w hwN z hzb hne.symm hπeq.symm
    exact ⟨x', hx'DP, hgx'⟩
  -- Both points lie on edges of `poly` other than edge `i`.
  have hpoly {u : P} (hu : u ∈ (poly.insertVertex i c).boundary ℝ)
      (huN : u ∉ affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i))) :
      u ∈ poly.boundary ℝ := by
    rw [boundary_insertVertex] at hu
    obtain ⟨k, -, hk⟩ := mem_iUnion₂.1 (hu.resolve_right huN)
    exact mem_iUnion.2 ⟨k, hk⟩
  refine ⟨z, mem_doublePoints.2 ⟨hpoly hzb hzN, w, hpoly hw hwN, hne, hπeq⟩,
    hgo z (fun h ↦ hxq (h ▸ hzb)) fun h ↦ ?_⟩
  -- If `z = x'`, then `x`, `x'` and `w` would be three points over the same crossing.
  subst h
  rcases hπ.eq_or_eq_or_eq_of_apply_eq (doublePoints_subset_boundary hxDP)
    (doublePoints_subset_boundary hx'DP) (hpoly hw hwN) hπx (hπx.trans hπeq.symm) with h | h | h
  · exact hxx' h
  · exact hxq (h ▸ hw)
  · exact hne h.symm

omit [NeZero n] in
/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: the
correspondence `g` is injective on the double points of `poly`, since `y ≠ y'` are not double
points of `poly`, and it keeps the fibres of `π` on them, since the double points over `π x` are
`x` and `x'`, which it sends over `π y`. -/
private theorem injOn_doublePoints_and_apply_eq {g : P → P} {x x' y y' : P} (hgx : g x = y)
    (hgx' : g x' = y') (hgo : ∀ z, z ≠ x → z ≠ x' → g z = z)
    (hgoff : ∀ z, projAlong ℝ p₀ d z ≠ projAlong ℝ p₀ d x → g z = z) (hyy' : y ≠ y')
    (hπy : projAlong ℝ p₀ d y = projAlong ℝ p₀ d y')
    (hy : y ∉ poly.doublePoints ℝ (projAlong ℝ p₀ d))
    (hy' : y' ∉ poly.doublePoints ℝ (projAlong ℝ p₀ d))
    (hpair : ∀ z ∈ poly.boundary ℝ, projAlong ℝ p₀ d z = projAlong ℝ p₀ d x → z = x ∨ z = x') :
    InjOn g (poly.doublePoints ℝ (projAlong ℝ p₀ d)) ∧
      ∀ z ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d), ∀ w ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d),
        projAlong ℝ p₀ d z = projAlong ℝ p₀ d w →
          projAlong ℝ p₀ d (g z) = projAlong ℝ p₀ d (g w) := by
  -- Only `x` is sent to `y`, and only `x'` to `y'`.
  have hgy {z : P} (hz : z ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d)) (h : g z = y) : z = x := by
    by_contra h₁
    by_cases h₂ : z = x'
    · rw [h₂, hgx'] at h
      exact hyy' h.symm
    · exact hy (by rwa [← h, hgo z h₁ h₂])
  have hgy' {z : P} (hz : z ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d)) (h : g z = y') :
      z = x' := by
    by_contra h₂
    by_cases h₁ : z = x
    · rw [h₁, hgx] at h
      exact hyy' h
    · exact hy' (by rwa [← h, hgo z h₁ h₂])
  refine ⟨fun z₁ hz₁ z₂ hz₂ h ↦ ?_, fun z hz w hw h ↦ ?_⟩
  · by_cases h₁ : z₁ = x
    · rw [h₁, hgx] at h
      rw [h₁, hgy hz₂ h.symm]
    by_cases h₂ : z₁ = x'
    · rw [h₂, hgx'] at h
      rw [h₂, hgy' hz₂ h.symm]
    rw [hgo z₁ h₁ h₂] at h
    by_cases h₃ : z₂ = x
    · rw [h₃, hgx] at h
      exact (hy (h ▸ hz₁)).elim
    by_cases h₄ : z₂ = x'
    · rw [h₄, hgx'] at h
      exact (hy' (h ▸ hz₁)).elim
    rw [h, hgo z₂ h₃ h₄]
  · have hgπ {u : P} (hu : u ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d))
        (hux : projAlong ℝ p₀ d u = projAlong ℝ p₀ d x) :
        projAlong ℝ p₀ d (g u) = projAlong ℝ p₀ d y := by
      rcases hpair u (doublePoints_subset_boundary hu) hux with rfl | rfl
      · rw [hgx]
      · rw [hgx', hπy]
    by_cases hzx : projAlong ℝ p₀ d z = projAlong ℝ p₀ d x
    · rw [hgπ hz hzx, hgπ hw (h ▸ hzx)]
    · rw [hgoff z hzx, hgoff w (h ▸ hzx), h]

/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: `i + r` and
`j + s₀`, the times of `x` and `x'`, are crossing times; the only crossing time on edge `i` is
`i + r`; and the only crossing time between `j + s₀` and `j + s₁` is `j + s₀`. -/
private theorem natCast_add_mem_crossingTimes (hs : poly.IsSimple ℝ) {i j : Fin n}
    {r s₀ s₁ : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) (hs₁ : s₁ ∈ Ioo (0 : ℝ) 1)
    (hxDP : lineMap (poly i) (poly (finRotate n i)) r ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d))
    (hx'DP : poly.edgePath ℝ j s₀ ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d))
    (hDPi : ∀ z ∈ poly.edgeSet ℝ i, z ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d) →
      z = lineMap (poly i) (poly (finRotate n i)) r)
    (hDPj : ∀ s ∈ uIcc s₀ s₁, poly.edgePath ℝ j s ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d) →
      s = s₀) :
    (((i : ℕ) : ℝ) + r ∈ poly.crossingTimes p₀ d ∧ ((j : ℕ) : ℝ) + s₀ ∈ poly.crossingTimes p₀ d) ∧
      (∀ t ∈ poly.crossingTimes p₀ d, edgeIndexAt n t = i → t = (i : ℕ) + r) ∧
      ∀ t ∈ poly.crossingTimes p₀ d, t ∈ uIcc (((j : ℕ) : ℝ) + s₀) (((j : ℕ) : ℝ) + s₁) →
        t = (j : ℕ) + s₀ := by
  have hin {k : Fin n} {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : ((k : ℕ) : ℝ) + u ∈ Ico (0 : ℝ) n := by
    have hk : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast k.isLt
    exact ⟨add_nonneg (Nat.cast_nonneg _) hu.1.le, by linarith [hu.2]⟩
  refine ⟨⟨mem_crossingTimes.2 ⟨hin hr, ?_⟩, mem_crossingTimes.2 ⟨hin hs₀, ?_⟩⟩,
    fun t ht hti ↦ ?_, fun t ht htu ↦ ?_⟩
  · rwa [boundaryParam_natCast_add _ _ (Ioo_subset_Icc_self hr)]
  · rwa [boundaryParam_natCast_add _ _ (Ioo_subset_Icc_self hs₀)]
  · obtain ⟨k, u, hu, rfl⟩ :=
      TauCeti.exists_eq_natCast_add_of_mem_Ico (crossingTimes_subset_Ico ht)
    rw [edgeIndexAt_natCast_add _ hu] at hti
    subst hti
    have hDP := (mem_crossingTimes.1 ht).2
    rw [boundaryParam_natCast_add _ _ (Ico_subset_Icc_self hu)] at hDP
    rw [lineMap_injective ℝ (hs.hasNondegenerateEdges k)
      (hDPi _ ⟨u, Ico_subset_Icc_self hu, rfl⟩ hDP)]
  · -- The parameter `t - j` lies between `s₀` and `s₁`.
    have hsu : t - (j : ℕ) ∈ uIcc s₀ s₁ := by
      rw [mem_uIcc] at htu ⊢
      rcases htu with h | h
      exacts [.inl ⟨by linarith [h.1], by linarith [h.2]⟩,
        .inr ⟨by linarith [h.1], by linarith [h.2]⟩]
    have hbp : poly.boundaryParam t = poly.edgePath ℝ j (t - (j : ℕ)) := by
      conv_lhs => rw [← add_sub_cancel ((j : ℕ) : ℝ) t]
      exact boundaryParam_natCast_add _ _
        (uIcc_subset_Icc (Ioo_subset_Icc_self hs₀) (Ioo_subset_Icc_self hs₁) hsu)
    rw [← hDPj _ hsu (hbp ▸ (mem_crossingTimes.1 ht).2), add_sub_cancel]

/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: moving the
crossing time `j + s₀` of `x'` to the time `j + s₁` of `y'` passes no other crossing time, so it is
increasing on the crossing times. Every crossing time `t` other than `i + r` is moved to a time
off edge `i`, on the same edge and on the same side of edge `i`, at which `poly` is at the image
under `g` of its point at time `t`. -/
private theorem exists_strictMonoOn_update
    (hbpinj : InjOn poly.boundaryParam (poly.crossingTimes p₀ d)) {i j : Fin n} (hji : j ≠ i)
    {r s₀ s₁ : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) (hs₁ : s₁ ∈ Ioo (0 : ℝ) 1)
    {g : P → P} (hgx' : g (poly.edgePath ℝ j s₀) = poly.edgePath ℝ j s₁)
    (hgo : ∀ z, z ≠ lineMap (poly i) (poly (finRotate n i)) r → z ≠ poly.edgePath ℝ j s₀ →
      g z = z)
    (hτx : ((i : ℕ) : ℝ) + r ∈ poly.crossingTimes p₀ d)
    (hτx' : ((j : ℕ) : ℝ) + s₀ ∈ poly.crossingTimes p₀ d)
    (hCTi : ∀ t ∈ poly.crossingTimes p₀ d, edgeIndexAt n t = i → t = (i : ℕ) + r)
    (hgap : ∀ t ∈ poly.crossingTimes p₀ d,
      t ∈ uIcc (((j : ℕ) : ℝ) + s₀) (((j : ℕ) : ℝ) + s₁) → t = (j : ℕ) + s₀) :
    ∃ θ : ℝ → ℝ, StrictMonoOn θ (poly.crossingTimes p₀ d) ∧
      ∀ t ∈ poly.crossingTimes p₀ d, t ≠ (i : ℕ) + r →
        θ t ∈ Ico (0 : ℝ) n ∧ edgeIndexAt n (θ t) ≠ i ∧
        poly.boundaryParam (θ t) = g (poly.boundaryParam t) ∧
        edgeIndexAt n (θ t) = edgeIndexAt n t ∧
        ((θ t < (i : ℕ) ∧ t < (i : ℕ)) ∨ (((i : ℕ) : ℝ) + 1 ≤ θ t ∧ ((i : ℕ) : ℝ) + 1 ≤ t)) := by
  classical
  refine ⟨update id ((j : ℕ) + s₀) ((j : ℕ) + s₁), (strictMono_id.strictMonoOn _).update
    (fun t ht htlt ↦ ?_) (fun t ht htgt ↦ ?_), fun t ht htx ↦ ?_⟩
  · by_contra! hle
    exact htlt.ne (hgap t ht (mem_uIcc.2 (.inr ⟨hle, htlt.le⟩)))
  · by_contra! hle
    exact htgt.ne' (hgap t ht (mem_uIcc.2 (.inl ⟨htgt.le, hle⟩)))
  by_cases htx' : t = (j : ℕ) + s₀
  · subst htx'
    have hj : ((j : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
    rw [update_self, edgeIndexAt_natCast_add _ ⟨hs₁.1.le, hs₁.2⟩,
      edgeIndexAt_natCast_add _ ⟨hs₀.1.le, hs₀.2⟩,
      boundaryParam_natCast_add _ _ (Ioo_subset_Icc_self hs₁),
      boundaryParam_natCast_add _ _ (Ioo_subset_Icc_self hs₀), hgx']
    refine ⟨⟨add_nonneg (Nat.cast_nonneg _) hs₁.1.le, by linarith [hs₁.2]⟩, hji, rfl, rfl, ?_⟩
    rcases lt_or_gt_of_ne (fun h ↦ hji (Fin.ext h) : (j : ℕ) ≠ (i : ℕ)) with h | h
    · have : ((j : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast h
      exact .inl ⟨by linarith [hs₁.2], by linarith [hs₀.2]⟩
    · have : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast h
      exact .inr ⟨by linarith [hs₁.1], by linarith [hs₀.1]⟩
  rw [update_of_ne htx', id_eq]
  have hti : edgeIndexAt n t ≠ i := fun h ↦ htx (hCTi t ht h)
  have hbpτx := boundaryParam_natCast_add poly i (Ioo_subset_Icc_self hr)
  have hbpτx' := boundaryParam_natCast_add poly j (Ioo_subset_Icc_self hs₀)
  refine ⟨crossingTimes_subset_Ico ht, hti,
    (hgo _ (fun h ↦ htx (hbpinj ht hτx (h.trans hbpτx.symm)))
      fun h ↦ htx' (hbpinj ht hτx' (h.trans hbpτx'.symm))).symm, rfl, ?_⟩
  -- A crossing time off edge `i` lies before `i` or after `i + 1`.
  have hside : t < (i : ℕ) ∨ ((i : ℕ) : ℝ) + 1 ≤ t := by
    by_contra! h
    refine hti ?_
    have := edgeIndexAt_natCast_add (n := n) i (s := t - (i : ℕ))
      ⟨by linarith [h.1], by linarith [h.2]⟩
    rwa [add_sub_cancel] at this
  exact hside.imp (fun h ↦ ⟨h, h⟩) fun h ↦ ⟨h, h⟩

/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: the change of
time `φ`, sending the time `i + r` of `x` to the time `τy` of `y`, and otherwise moving the time
`j + s₀` of `x'` to the time `j + s₁` of `y'` and reparametrizing for the inserted vertex, is
increasing on the crossing times, maps them onto those of `q`, matches the two boundary
parametrizations through `g`, and keeps the edge directions at every crossing time but `i + r`. -/
private theorem exists_strictMonoOn_crossingTimes
    (hbpinj : InjOn poly.boundaryParam (poly.crossingTimes p₀ d)) {i j : Fin n} {c : P}
    (hs' : (poly.insertVertex i c).IsSimple ℝ) (hji : j ≠ i) {r s₀ s₁ τy : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) (hs₁ : s₁ ∈ Ioo (0 : ℝ) 1)
    (hτy : τy ∈ Ioo ((i : ℕ) : ℝ) ((i : ℕ) + 2)) {g : P → P} {y : P}
    (hgx : g (lineMap (poly i) (poly (finRotate n i)) r) = y)
    (hgx' : g (poly.edgePath ℝ j s₀) = poly.edgePath ℝ j s₁)
    (hgo : ∀ z, z ≠ lineMap (poly i) (poly (finRotate n i)) r → z ≠ poly.edgePath ℝ j s₀ →
      g z = z)
    (hbpy : (poly.insertVertex i c).boundaryParam τy = y)
    (hτx : ((i : ℕ) : ℝ) + r ∈ poly.crossingTimes p₀ d)
    (hτx' : ((j : ℕ) : ℝ) + s₀ ∈ poly.crossingTimes p₀ d)
    (hCTi : ∀ t ∈ poly.crossingTimes p₀ d, edgeIndexAt n t = i → t = (i : ℕ) + r)
    (hgap : ∀ t ∈ poly.crossingTimes p₀ d,
      t ∈ uIcc (((j : ℕ) : ℝ) + s₀) (((j : ℕ) : ℝ) + s₁) → t = (j : ℕ) + s₀)
    (hgDP : MapsTo g (poly.doublePoints ℝ (projAlong ℝ p₀ d))
      ((poly.insertVertex i c).doublePoints ℝ (projAlong ℝ p₀ d)))
    (hDPq : ∀ z ∈ (poly.insertVertex i c).doublePoints ℝ (projAlong ℝ p₀ d),
      ∃ z₀ ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d), g z₀ = z) :
    ∃ φ : ℝ → ℝ, StrictMonoOn φ (poly.crossingTimes p₀ d) ∧
      (poly.insertVertex i c).crossingTimes p₀ d = φ '' poly.crossingTimes p₀ d ∧
      (∀ t ∈ poly.crossingTimes p₀ d,
        (poly.insertVertex i c).boundaryParam (φ t) = g (poly.boundaryParam t)) ∧
      φ ((i : ℕ) + r) = τy ∧ ∀ t ∈ poly.crossingTimes p₀ d, t ≠ (i : ℕ) + r →
        poly.insertVertex i c (finRotate (n + 1) (edgeIndexAt (n + 1) (φ t))) -ᵥ
          poly.insertVertex i c (edgeIndexAt (n + 1) (φ t)) =
          poly (finRotate n (edgeIndexAt n t)) -ᵥ poly (edgeIndexAt n t) := by
  classical
  obtain ⟨θ, hθmono, hθ⟩ :=
    exists_strictMonoOn_update hbpinj hji hr hs₀ hs₁ hgx' hgo hτx hτx' hCTi hgap
  obtain ⟨ψ, hψ, hψt, hψle, hψge⟩ := exists_strictMono_boundaryParam_insertVertex poly i c
  set φ : ℝ → ℝ := update (ψ ∘ θ) ((i : ℕ) + r) τy
  have hφx : φ ((i : ℕ) + r) = τy := update_self ..
  have hφo {t : ℝ} (h : t ≠ (i : ℕ) + r) : φ t = ψ (θ t) := update_of_ne h ..
  have hbp (t : ℝ) (ht : t ∈ poly.crossingTimes p₀ d) :
      (poly.insertVertex i c).boundaryParam (φ t) = g (poly.boundaryParam t) := by
    by_cases htx : t = (i : ℕ) + r
    · rw [htx, hφx, hbpy, boundaryParam_natCast_add _ _ (Ioo_subset_Icc_self hr), edgePath, hgx]
    · obtain ⟨h₁, h₂, h₃, -⟩ := hθ t ht htx
      rw [hφo htx, (hψt _ h₁ h₂).2.1, h₃]
  have hφmem (t : ℝ) (ht : t ∈ poly.crossingTimes p₀ d) : φ t ∈ Ico (0 : ℝ) (n + 1 : ℕ) := by
    by_cases htx : t = (i : ℕ) + r
    · have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
      rw [htx, hφx]
      push_cast
      exact ⟨by linarith [hτy.1, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (i : ℕ))], by linarith [hτy.2]⟩
    · obtain ⟨h₁, h₂, -⟩ := hθ t ht htx
      rw [hφo htx]
      exact (hψt _ h₁ h₂).1
  refine ⟨φ, ((hψ.comp_strictMonoOn hθmono).mono sdiff_subset).update (fun t ht htlt ↦ ?_)
    (fun t ht htgt ↦ ?_), ?_, hbp, hφx, fun t ht htx ↦ ?_⟩
  · rcases (hθ t ht htlt.ne).2.2.2.2 with h | h
    · rw [Function.comp_apply, hψle _ h.1.le]
      linarith [hτy.1, h.1]
    · linarith [h.2, hr.2]
  · rcases (hθ t ht htgt.ne').2.2.2.2 with h | h
    · linarith [h.2, hr.1]
    · rw [Function.comp_apply, hψge _ h.1]
      linarith [hτy.2, h.1]
  · refine Subset.antisymm (fun t' ht' ↦ ?_) ?_
    · obtain ⟨ht'I, ht'DP⟩ := mem_crossingTimes.1 ht'
      obtain ⟨z₀, hz₀, hgz⟩ := hDPq _ ht'DP
      rw [← image_boundaryParam_crossingTimes] at hz₀
      obtain ⟨t, ht, rfl⟩ := hz₀
      exact ⟨t, ht, hs'.injOn_boundaryParam (hφmem t ht) ht'I (by rw [hbp t ht, hgz])⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact mem_crossingTimes.2
        ⟨hφmem t ht, by rw [hbp t ht]; exact hgDP (mem_crossingTimes.1 ht).2⟩
  · obtain ⟨h₁, h₂, -, h₄, -⟩ := hθ t ht htx
    rw [hφo htx, (hψt _ h₁ h₂).2.2, h₄]

omit [NeZero n] in
/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: the
correspondence `g` keeps over/under. At the moved crossing, `x` and `y` lie in `D` and `x'` and
`y'` on edge `j`, which `D` does not meet, so the heights of `x` over `x'` and of `y` over `y'` have
the same sign (`Affine.Simplex.pos_iff_pos_of_disjoint`); elsewhere `g` is the identity. -/
private theorem exists_pos_smul_eq_vsub (hd : d ≠ 0) {i j : Fin n} {c : P}
    (hΔ : poly.IsDeltaMove ℝ i c) (hji : j ≠ i) (ha : poly i ∉ poly.edgeSet ℝ j)
    (ha' : poly (finRotate n i) ∉ poly.edgeSet ℝ j) {g : P → P} {x x' y y' : P}
    (hgx : g x = y) (hgx' : g x' = y')
    (hgoff : ∀ z, projAlong ℝ p₀ d z ≠ projAlong ℝ p₀ d x → g z = z)
    (hxD : x ∈ hΔ.triangle.closedInterior) (hyD : y ∈ hΔ.triangle.closedInterior)
    (hx'j : x' ∈ poly.edgeSet ℝ j) (hy'j : y' ∈ poly.edgeSet ℝ j) (hyy' : y ≠ y')
    (hπy : projAlong ℝ p₀ d y = projAlong ℝ p₀ d y')
    (hpair : ∀ z ∈ poly.boundary ℝ, projAlong ℝ p₀ d z = projAlong ℝ p₀ d x → z = x ∨ z = x') :
    ∀ z ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d), ∀ w ∈ poly.doublePoints ℝ (projAlong ℝ p₀ d),
      (∃ c : ℝ, 0 < c ∧ c • d = z -ᵥ w) → ∃ c : ℝ, 0 < c ∧ c • d = g z -ᵥ g w := by
  have hdisj : ∀ z ∈ hΔ.triangle.closedInterior,
      z ∉ affineSegment ℝ (poly j) (poly (finRotate n j)) := fun z hz hzj ↦ by
    rcases hΔ.edgeSet_inter_closedInterior_subset hji ⟨hzj, hz⟩ with rfl | rfl
    exacts [ha hzj, ha' hzj]
  obtain ⟨h₁, hh₁⟩ := projAlong_eq_projAlong_iff.1 hπy
  have hheight {h₀ : ℝ} (hh₀ : h₀ • d = x -ᵥ x') : 0 < h₀ ↔ 0 < h₁ :=
    hΔ.triangle.pos_iff_pos_of_disjoint hdisj hxD hyD hx'j hy'j hh₀ hh₁
  have hh₁0 : h₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul, eq_comm, vsub_eq_zero_iff_eq] at hh₁
    exact hyy' hh₁
  rintro z hz w hw ⟨e, he, hed⟩
  have hπzw : projAlong ℝ p₀ d z = projAlong ℝ p₀ d w := projAlong_eq_projAlong_iff.2 ⟨e, hed⟩
  by_cases hzx : projAlong ℝ p₀ d z = projAlong ℝ p₀ d x
  · have hzw : z ≠ w := by
      rintro rfl
      rw [vsub_self, smul_eq_zero] at hed
      exact hed.elim he.ne' hd
    rcases hpair z (doublePoints_subset_boundary hz) hzx with rfl | rfl <;>
      rcases hpair w (doublePoints_subset_boundary hw) (hπzw ▸ hzx) with rfl | rfl
    · exact (hzw rfl).elim
    · exact ⟨h₁, (hheight hed).1 he, by rw [hgx, hgx', hh₁]⟩
    · refine ⟨-h₁, ?_, by rw [hgx, hgx', neg_smul, hh₁, neg_vsub_eq_vsub_rev]⟩
      have : ¬ 0 < h₁ := fun h ↦ by
        have := (hheight (by rw [neg_smul, hed, neg_vsub_eq_vsub_rev] : (-e) • d = _)).2 h
        linarith
      exact neg_pos.2 (lt_of_le_of_ne (not_lt.1 this) hh₁0)
    · exact (hzw rfl).elim
  · exact ⟨e, he, by rw [hgoff z hzx, hgoff w (hπzw ▸ hzx), hed]⟩

/-- A stage of `Polygon.gaussCode_insertVertex_of_crossing`, private to its proof: the change of
time `φ` keeps the signs of the crossings. At the moved crossing, the edge of `q` at `φ (i + r)`
gives `L = det (·, w, d)` the sign of `a' - a`, and edge `j` keeps its direction `w`; at every other
crossing both edges keep their directions. -/
private theorem sign_det_eq_of_slide
    (hbpinj : InjOn poly.boundaryParam (poly.crossingTimes p₀ d))
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) (b : Basis (Fin 3) ℝ V) {i j : Fin n}
    {c : P} (hji : j ≠ i) {r s₀ τy : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1)
    (hxx' : lineMap (poly i) (poly (finRotate n i)) r ≠ poly.edgePath ℝ j s₀)
    (hπx : projAlong ℝ p₀ d (lineMap (poly i) (poly (finRotate n i)) r) =
      projAlong ℝ p₀ d (poly.edgePath ℝ j s₀))
    (hτx : ((i : ℕ) : ℝ) + r ∈ poly.crossingTimes p₀ d)
    (hτx' : ((j : ℕ) : ℝ) + s₀ ∈ poly.crossingTimes p₀ d) {L : V →ₗ[ℝ] ℝ}
    (hL : ∀ v, L v = b.det ![v, poly (finRotate n j) -ᵥ poly j, d]) {φ : ℝ → ℝ}
    (hφx : φ ((i : ℕ) + r) = τy)
    (hdir : ∀ t ∈ poly.crossingTimes p₀ d, t ≠ (i : ℕ) + r →
      poly.insertVertex i c (finRotate (n + 1) (edgeIndexAt (n + 1) (φ t))) -ᵥ
        poly.insertVertex i c (edgeIndexAt (n + 1) (φ t)) =
        poly (finRotate n (edgeIndexAt n t)) -ᵥ poly (edgeIndexAt n t))
    (hdiry : SignType.sign (L (poly.insertVertex i c (finRotate (n + 1) (edgeIndexAt (n + 1) τy))
      -ᵥ poly.insertVertex i c (edgeIndexAt (n + 1) τy))) =
        SignType.sign (L (poly (finRotate n i) -ᵥ poly i))) :
    ∀ t ∈ poly.crossingTimes p₀ d, ∀ t' ∈ poly.crossingTimes p₀ d,
      poly.boundaryParam t' = poly.doublePointPartner ℝ (projAlong ℝ p₀ d) (poly.boundaryParam t) →
      SignType.sign (b.det
        ![poly.insertVertex i c (finRotate (n + 1) (edgeIndexAt (n + 1) (φ t))) -ᵥ
            poly.insertVertex i c (edgeIndexAt (n + 1) (φ t)),
          poly.insertVertex i c (finRotate (n + 1) (edgeIndexAt (n + 1) (φ t'))) -ᵥ
            poly.insertVertex i c (edgeIndexAt (n + 1) (φ t')), d]) =
      SignType.sign (b.det
        ![poly (finRotate n (edgeIndexAt n t)) -ᵥ poly (edgeIndexAt n t),
          poly (finRotate n (edgeIndexAt n t')) -ᵥ poly (edgeIndexAt n t'), d]) := by
  have hbpτx := boundaryParam_natCast_add poly i (Ioo_subset_Icc_self hr)
  have hbpτx' := boundaryParam_natCast_add poly j (Ioo_subset_Icc_self hs₀)
  have hpx : poly.doublePointPartner ℝ (projAlong ℝ p₀ d) (poly.edgePath ℝ i r) =
      poly.edgePath ℝ j s₀ := by
    rw [edgePath]
    exact (hπ.eq_doublePointPartner
      (subset_iUnion (poly.edgeSet ℝ) i ⟨r, Ioo_subset_Icc_self hr, rfl⟩)
      (subset_iUnion (poly.edgeSet ℝ) j ⟨s₀, Ioo_subset_Icc_self hs₀, rfl⟩) hxx'.symm hπx.symm).symm
  have hpx' : poly.doublePointPartner ℝ (projAlong ℝ p₀ d) (poly.edgePath ℝ j s₀) =
      poly.edgePath ℝ i r := by
    rw [← hpx, hπ.involutive_doublePointPartner]
  have hidx := edgeIndexAt_natCast_add i ⟨hr.1.le, hr.2⟩
  have hidx' := edgeIndexAt_natCast_add j ⟨hs₀.1.le, hs₀.2⟩
  have hτxx' : ((i : ℕ) : ℝ) + r ≠ (j : ℕ) + s₀ := fun h ↦ hji (by rw [← hidx', ← h, hidx])
  have hdirτy' := hdir _ hτx' hτxx'.symm
  rw [hidx'] at hdirτy'
  have hswap (u : V) : b.det ![poly (finRotate n j) -ᵥ poly j, u, d] =
      -b.det ![u, poly (finRotate n j) -ᵥ poly j, d] := by
    have h := b.det.map_swap ![u, poly (finRotate n j) -ᵥ poly j, d] (i := 0) (j := 1) (by decide)
    have he : ![u, poly (finRotate n j) -ᵥ poly j, d] ∘ (Equiv.swap (0 : Fin 3) 1) =
        ![poly (finRotate n j) -ᵥ poly j, u, d] := by
      funext k
      fin_cases k <;> rfl
    rwa [he] at h
  intro t ht t' ht' htt'
  by_cases htx : t = (i : ℕ) + r
  · subst htx
    obtain rfl : t' = (j : ℕ) + s₀ := hbpinj ht' hτx' (by rw [htt', hbpτx, hpx, hbpτx'])
    rw [hφx, hdirτy', hidx, hidx', ← hL, ← hL]
    exact hdiry
  by_cases htx' : t = (j : ℕ) + s₀
  · subst htx'
    obtain rfl : t' = (i : ℕ) + r := hbpinj ht' hτx (by rw [htt', hbpτx', hpx', hbpτx])
    rw [hφx, hdirτy', hidx, hidx', hswap, hswap, ← hL, ← hL, Left.sign_neg, Left.sign_neg,
      hdiry]
  -- Away from the moved crossing, both visits keep their edges.
  have ht'x : t' ≠ (i : ℕ) + r := fun h ↦ htx' (hbpinj ht hτx' (by
    rw [hbpτx', ← hpx, ← hbpτx, ← h, htt', hπ.involutive_doublePointPartner]))
  rw [hdir t ht htx, hdir t' ht' ht'x]

/-- **A strand sliding across the triangle of a Δ-move does not change the Gauss code.** Let `poly`
be a simple polygon in a three-dimensional real affine space, and `poly.insertVertex i c` the
simple polygon obtained from it by a Δ-move across the triangle `D` with vertices `a = poly i`,
`a' = poly (i + 1)` and `c`. Suppose that the projection `π` along `d` is regular for both
polygons and carries `D` onto a nondegenerate triangle, that edge `j` of `poly` crosses edge `i` in
the diagram, and that every point of another edge projecting into `π D` is `a` or `a'`. Then edge
`j` leaves `π D` across one of the projections of the two new edges, the move slides the crossing
of the two strands from edge `i` to that new edge, and the two polygons have the same Gauss code.
The numbers of crossings agree, and the codes are compared together with them. -/
theorem gaussCode_insertVertex_of_crossing (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {i j : Fin n} {c : P}
    (hs' : (poly.insertVertex i c).IsSimple ℝ)
    (hπ' : (poly.insertVertex i c).IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (hΔ : poly.IsDeltaMove ℝ i c)
    (hT : AffineIndependent ℝ ![projAlong ℝ p₀ d (poly i),
      projAlong ℝ p₀ d (poly (finRotate n i)), projAlong ℝ p₀ d c])
    (hprism : ∀ k, k ≠ i → k ≠ j → ∀ z ∈ poly.edgeSet ℝ k,
      projAlong ℝ p₀ d z ∈ projAlong ℝ p₀ d '' hΔ.triangle.closedInterior →
        z = poly i ∨ z = poly (finRotate n i))
    (hcross : ∃ x ∈ poly.edgeSet ℝ i, ∃ x' ∈ poly.edgeSet ℝ j, x ≠ x' ∧
      projAlong ℝ p₀ d x = projAlong ℝ p₀ d x')
    (b : Basis (Fin 3) ℝ V) :
    (⟨_, gaussCode hs' hπ' b⟩ : Σ m, BasedOrientedGaussCode m) = ⟨_, gaussCode hs hπ b⟩ := by
  /- The proof follows edge `j` in barycentric coordinates of the projected triangle until it
  leaves it at `y'`, lifts that point to the point `y` of the new edges, and then compares the two
  diagrams with `gaussCode_eq_of_strictMonoOn`: the crossing `x`/`x'` of edges `i` and `j` becomes
  the crossing `y`/`y'`, every other crossing is kept, the crossing times are matched by the change
  of time `φ`, and the over/under data and the signs are checked at the moved crossing. -/
  classical
  -- Stage 1: the crossing `x` over `x'` lies inside edges `i` and `j`.
  obtain ⟨x, hx, x', hx', hxx', hπx⟩ := hcross
  obtain ⟨hd, hji, ha, ha', hxDP, hx'DP, hpair, ⟨r, hr, rfl⟩, s₀, hs₀, rfl⟩ :=
    exists_mem_Ioo_of_crossing hs hπ hx hx' hxx' hπx
  -- Stage 2: edge `j` leaves the projected triangle at `y'`, over the point `y` of the new edges.
  obtain ⟨s₁, hs₁, hs₁₀, y, τy, L, hL, hyD, hπy, hyy', hyb, hyq, hy'q, hxq, hτy, hbpy, hdiry, hDPj,
    hN⟩ := exists_slide hs hπ hπ' hΔ hT hprism b hd hji ha ha' hr hs₀ hxDP hπx
  -- Stage 3: the correspondence `g` of double points, sending `x ↦ y` and `x' ↦ y'`.
  obtain ⟨g, hgx, hgx', hgo⟩ : ∃ g : P → P, g (lineMap (poly i) (poly (finRotate n i)) r) = y ∧
      g (poly.edgePath ℝ j s₀) = poly.edgePath ℝ j s₁ ∧
      ∀ z, z ≠ lineMap (poly i) (poly (finRotate n i)) r → z ≠ poly.edgePath ℝ j s₀ → g z = z :=
    ⟨update (update id _ (poly.edgePath ℝ j s₁)) _ y, update_self .., by
      rw [update_of_ne hxx'.symm, update_self], fun z h₁ h₂ ↦ by
      rw [update_of_ne h₁, update_of_ne h₂, id_eq]⟩
  have hgoff (z : P) (h : projAlong ℝ p₀ d z ≠
      projAlong ℝ p₀ d (lineMap (poly i) (poly (finRotate n i)) r)) : g z = z :=
    hgo z (fun h' ↦ h (by rw [h'])) fun h' ↦ h (by rw [h', hπx])
  have hDPi := fun z ↦ eq_of_mem_edgeSet_of_mem_doublePoints hs hπ hΔ hprism hji hx hx' hπx (z := z)
  obtain ⟨hginj, hfib⟩ := injOn_doublePoints_and_apply_eq hgx hgx' hgo hgoff hyy' hπy
    (fun h ↦ hyb (doublePoints_subset_boundary h)) (fun h ↦ hs₁₀ (hDPj s₁ right_mem_uIcc h)) hpair
  -- Stage 4: the change of time `φ`, matching the crossing times.
  have hbpinj : InjOn poly.boundaryParam (poly.crossingTimes p₀ d) :=
    hs.injOn_boundaryParam.mono crossingTimes_subset_Ico
  obtain ⟨⟨hτx, hτx'⟩, hCTi, hgap⟩ :=
    natCast_add_mem_crossingTimes hs hr hs₀ hs₁ hxDP hx'DP hDPi hDPj
  obtain ⟨φ, hφ, hct, hbp, hφx, hdir⟩ := exists_strictMonoOn_crossingTimes hbpinj hs' hji hr hs₀ hs₁
    hτy hgx hgx' hgo hbpy hτx hτx' hCTi hgap
    (mapsTo_doublePoints_insertVertex hgx hgx' hgo hDPi hpair hyq hy'q)
    fun z hz ↦ exists_mem_doublePoints_eq hπ hgx hgx' hgo hxDP hx'DP hxx' hπx hxq hN hz
  -- Stage 5: the over/under data and the signs are kept.
  exact gaussCode_eq_of_strictMonoOn b hs hπ b hs' hπ' hφ hct hbp hginj hfib
    (exists_pos_smul_eq_vsub hd hΔ hji ha ha' hgx hgx' hgoff (hΔ.edgeSet_subset_closedInterior hx)
      hyD hx' ⟨s₁, Ioo_subset_Icc_self hs₁, rfl⟩ hyy' hπy hpair)
    (sign_det_eq_of_slide hbpinj hπ b hji hr hs₀ hxx' hπx hτx hτx' hL hφx hdir hdiry)

end Polygon
