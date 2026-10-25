/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Floor.Ring
public import TauCeti.Geometry.Polygon.DoublePoint
public import TauCeti.Geometry.Polygon.Simple

/-!
# Subdividing an edge of a polygon

Subdividing edge `i` of a polygon `poly` at one of its points `c = poly.edgePath R i s`, with
`s ∈ [0, 1]`, inserts `c` as a new vertex after vertex `i` (`Polygon.insertVertex`). This is the
degenerate Δ-move `TauCeti.SimplePolygon.IsElementaryMove.subdivide`. It does not move the polygon:
the boundary is unchanged (`Polygon.boundary_insertVertex_edgePath`), and so are the double points
of every map out of the ambient space (`Polygon.doublePoints_insertVertex_edgePath`). A projection
stays regular exactly when the new vertex is not a double point
(`Polygon.isRegularProjection_insertVertex_edgePath_iff`).

Over the reals, the boundary parametrizations before and after subdividing at an interior point of
an edge differ by an increasing change of time
(`Polygon.exists_strictMono_boundaryParam_insertVertex_edgePath`): the traversal of the subdivided
polygon passes through the same points in the same order, and at each time it runs along an edge
pointing in the same direction as the edge of the original polygon at the corresponding time. This
is what keeps the diagram read off from a projection of a polygonal knot unchanged by subdivision.
The same change of time works away from edge `i` when any vertex `c` is inserted after vertex `i`
(`Polygon.exists_strictMono_boundaryParam_insertVertex`), as in a Δ-move: off the moved edge the two
traversals pass through the same points, along edges with the same directions.

## Main results

* `Polygon.doublePoints_insertVertex_edgePath`: subdividing an edge does not change the double
  points.
* `Polygon.isRegularProjection_insertVertex_edgePath_iff`: a projection is regular for the
  subdivided polygon exactly when it is regular for the original one and the new vertex is not a
  double point.
* `Polygon.exists_strictMono_boundaryParam_insertVertex_edgePath`: the boundary parametrizations
  before and after subdividing differ by an increasing change of time preserving edge directions.
* `Polygon.exists_strictMono_boundaryParam_insertVertex`: inserting any vertex changes the boundary
  parametrization away from the moved edge by an increasing change of time preserving edge
  directions.

## References

* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1 §B, for subdivision as a degenerate Δ-move.
-/

public section

open Set Function AffineMap

namespace Polygon

variable {R V P Q : Type*} {n : ℕ}

/-! ### Edges, double points and regular projections -/

section Parameter

variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P] (poly : Polygon P n) (i : Fin n)

/-- If subdividing edge `i` at parameter `s ∈ [0, 1]` leaves the edges nondegenerate, then the
new vertex is neither end point of the edge: `s ∈ (0, 1)`. -/
theorem mem_Ioo_of_hasNondegenerateEdges_insertVertex_edgePath [PartialOrder R] {s : R}
    (hs : s ∈ Icc (0 : R) 1)
    (h : (poly.insertVertex i (poly.edgePath R i s)).HasNondegenerateEdges) :
    s ∈ Ioo (0 : R) 1 := by
  refine ⟨hs.1.lt_of_ne fun h₀ ↦ h i.castSucc ?_, hs.2.lt_of_ne fun h₁ ↦ h i.succ ?_⟩
  · rw [finRotate_apply, Fin.coeSucc_eq_succ, insertVertex_apply_succ_self,
      insertVertex_apply_castSucc_self, ← h₀, edgePath, lineMap_apply_zero]
  · rw [insertVertex_apply_finRotate_succ_self, insertVertex_apply_succ_self, h₁, edgePath,
      lineMap_apply_one]

end Parameter

section Subdivide

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V]
  [AddTorsor V P] (poly : Polygon P n) (i : Fin n) {s : R}

/-- Subdividing an edge does not change the double points of a map. -/
theorem doublePoints_insertVertex_edgePath (π : P → Q) (hs : s ∈ Icc (0 : R) 1) :
    (poly.insertVertex i (poly.edgePath R i s)).doublePoints R π = poly.doublePoints R π :=
  doublePoints_eq_of_boundary_eq (boundary_insertVertex_edgePath poly i hs)

/-- After subdividing an edge, a projection is regular exactly when it was regular before and the
new vertex is not a double point. -/
theorem isRegularProjection_insertVertex_edgePath_iff {π : P → Q} (hs : s ∈ Icc (0 : R) 1) :
    (poly.insertVertex i (poly.edgePath R i s)).IsRegularProjection R π ↔
      poly.IsRegularProjection R π ∧ poly.edgePath R i s ∉ poly.doublePoints R π := by
  have hb := boundary_insertVertex_edgePath poly i hs
  have hc : poly.edgePath R i s ∈ poly.boundary R := mem_boundary_iff.2 ⟨i, s, hs, rfl⟩
  constructor
  · intro h
    refine ⟨⟨fun x y z hx hy hz ↦ ?_, fun k x hx hxk ↦ ?_⟩, fun hcd ↦ ?_⟩
    · exact h.eq_or_eq_or_eq_of_apply_eq (hb ▸ hx) (hb ▸ hy) (hb ▸ hz)
    · have := h.eq_vertex_of_apply_eq (i.succ.succAbove k) (hb ▸ hx)
        (by rwa [insertVertex_apply_succAbove])
      rwa [insertVertex_apply_succAbove] at this
    · obtain ⟨-, y, hy, hne, hy'⟩ := mem_doublePoints.1 hcd
      have := h.eq_vertex_of_apply_eq i.succ (hb ▸ hy) (by rwa [insertVertex_apply_succ_self])
      rw [insertVertex_apply_succ_self] at this
      exact hne this
  · rintro ⟨h, hcd⟩
    refine ⟨fun x y z hx hy hz ↦ h.eq_or_eq_or_eq_of_apply_eq (hb ▸ hx) (hb ▸ hy) (hb ▸ hz),
      fun j x hx hxj ↦ ?_⟩
    rw [hb] at hx
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i.succ j
    · rw [insertVertex_apply_succ_self] at hxj ⊢
      by_contra hne
      exact hcd (mem_doublePoints.2 ⟨hc, x, hx, hne, hxj⟩)
    · rw [insertVertex_apply_succAbove] at hxj ⊢
      exact h.eq_vertex_of_apply_eq k hx hxj

end Subdivide

/-! ### The boundary parametrization after subdividing -/

section Param

variable [AddCommGroup V] [Module ℝ V] [AddTorsor V P] [NeZero n] (poly : Polygon P n)
  (i : Fin n) {s : ℝ}

/-- The change of time from the boundary parametrization of a polygon to that of the polygon with
edge `i` subdivided at parameter `s`: the identity before time `a = i`, the affine maps of
`[a, a + s]` onto `[a, a + 1]` and of `[a + s, a + 1]` onto `[a + 1, a + 2]`, and the shift by `1`
after time `a + 1`. -/
private noncomputable def subdivisionTime (a s t : ℝ) : ℝ :=
  t + (s⁻¹ - 1) * min (max (t - a) 0) s + ((1 - s)⁻¹ - 1) * min (max (t - a - s) 0) (1 - s)

private theorem strictMono_subdivisionTime (a : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
    StrictMono (subdivisionTime a s) := by
  have h₁ : 0 ≤ s⁻¹ - 1 := sub_nonneg.2 ((one_le_inv₀ hs.1).2 hs.2.le)
  have h₂ : 0 ≤ (1 - s)⁻¹ - 1 :=
    sub_nonneg.2 ((one_le_inv₀ (sub_pos.2 hs.2)).2 (by linarith [hs.1]))
  intro t u htu
  rw [subdivisionTime, subdivisionTime]
  have k₁ : min (max (t - a) 0) s ≤ min (max (u - a) 0) s := by gcongr
  have k₂ : min (max (t - a - s) 0) (1 - s) ≤ min (max (u - a - s) 0) (1 - s) := by gcongr
  nlinarith [mul_le_mul_of_nonneg_left k₁ h₁, mul_le_mul_of_nonneg_left k₂ h₂]

omit [NeZero n] in
/-- On each edge `j ≠ i` of `poly`, at parameter `u`, the change of time `subdivisionTime` lands on
the same edge of the polygon with any vertex `c` inserted after vertex `i`, at the same parameter,
so at the same point and with the same edge direction. -/
private theorem exists_subdivisionTime_eq_of_ne (hs : s ∈ Ioo (0 : ℝ) 1) (c : P) {j : Fin n}
    (hj : j ≠ i) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    ∃ j' : Fin (n + 1), subdivisionTime ((i : ℕ) : ℝ) s ((j : ℕ) + u) = (j' : ℕ) + u ∧
      (poly.insertVertex i c).edgePath ℝ j' u = poly.edgePath ℝ j u ∧
      poly.insertVertex i c (finRotate (n + 1) j') -ᵥ poly.insertVertex i c j' =
        poly (finRotate n j) -ᵥ poly j := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hu0, hu1⟩ := hu
  have hs1' : 0 < 1 - s := sub_pos.2 hs1
  refine ⟨i.succ.succAbove j, ?_, by rw [edgePath_insertVertex_succAbove _ _ _ hj], ?_⟩
  · rcases lt_or_gt_of_ne (fun h : (j : ℕ) = i ↦ hj (Fin.ext h)) with hji | hji
    · -- Before the inserted vertex, nothing changes.
      have hv : ((i.succ.succAbove j : Fin (n + 1)) : ℕ) = j := by
        rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega), Fin.val_castSucc]
      have hji' : ((j : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast hji
      rw [hv, subdivisionTime, max_eq_right (by linarith), max_eq_right (by linarith),
        min_eq_left hs0.le, min_eq_left hs1'.le]
      ring
    · -- After the inserted vertex, the time is shifted by `1`.
      have hv : ((i.succ.succAbove j : Fin (n + 1)) : ℕ) = j + 1 := by
        rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega), Fin.val_succ]
      have hij : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast hji
      rw [hv, Nat.cast_add_one, subdivisionTime, max_eq_left (by linarith),
        min_eq_right (by linarith), max_eq_left (by linarith), min_eq_right (by linarith)]
      field_simp
      ring
  · rw [Fin.finRotate_succ_succAbove_of_ne hj, insertVertex_apply_succAbove,
      insertVertex_apply_succAbove]

omit [NeZero n] in
/-- On each edge `j` of `poly`, at parameter `u`, the change of time `subdivisionTime` lands on an
edge `j'` of the subdivided polygon, at a parameter `u'`, at the same point and with the edge
direction rescaled by a positive factor. -/
private theorem exists_subdivisionTime_eq (hs : s ∈ Ioo (0 : ℝ) 1) (j : Fin n) {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) :
    ∃ j' : Fin (n + 1), ∃ u' ∈ Ico (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧
      subdivisionTime ((i : ℕ) : ℝ) s ((j : ℕ) + u) = (j' : ℕ) + u' ∧
      (poly.insertVertex i (poly.edgePath ℝ i s)).edgePath ℝ j' u' = poly.edgePath ℝ j u ∧
      poly.insertVertex i (poly.edgePath ℝ i s) (finRotate (n + 1) j') -ᵥ
          poly.insertVertex i (poly.edgePath ℝ i s) j' = r • (poly (finRotate n j) -ᵥ poly j) := by
  by_cases hji : j = i
  · -- On the subdivided edge, the time runs faster by the factor `1 / s` before the new vertex
    -- and `1 / (1 - s)` after it.
    subst hji
    obtain ⟨hs0, hs1⟩ := hs
    obtain ⟨hu0, hu1⟩ := hu
    have hs1' : 0 < 1 - s := sub_pos.2 hs1
    rcases lt_or_ge u s with hus | hus
    · refine ⟨j.castSucc, u / s, ⟨div_nonneg hu0 hs0.le, (div_lt_one hs0).2 hus⟩, s, hs0, ?_, ?_,
        ?_⟩
      · rw [Fin.val_castSucc, subdivisionTime, add_sub_cancel_left, max_eq_left hu0,
          min_eq_left hus.le, max_eq_right (by linarith), min_eq_left hs1'.le]
        field_simp
        ring
      · rw [edgePath_insertVertex_castSucc_self, edgePath, lineMap_lineMap_right,
          div_mul_cancel₀ _ hs0.ne']
      · rw [finRotate_apply, Fin.coeSucc_eq_succ, insertVertex_apply_succ_self,
          insertVertex_apply_castSucc_self, edgePath, lineMap_vsub_left]
    · refine ⟨j.succ, (u - s) / (1 - s),
        ⟨div_nonneg (by linarith) hs1'.le, (div_lt_one hs1').2 (by linarith)⟩, 1 - s, hs1', ?_, ?_,
        ?_⟩
      · rw [Fin.val_succ, Nat.cast_add_one, subdivisionTime, add_sub_cancel_left,
          max_eq_left hu0, min_eq_right hus, max_eq_left (by linarith), min_eq_left (by linarith)]
        field_simp
        ring
      · rw [edgePath_insertVertex_succ_self, edgePath, lineMap_lineMap_left]
        congr 1
        field_simp
        ring
      · rw [insertVertex_apply_finRotate_succ_self, insertVertex_apply_succ_self, edgePath,
          right_vsub_lineMap]
  · obtain ⟨j', hφ, hpath, hdir⟩ := exists_subdivisionTime_eq_of_ne poly i hs _ hji hu
    exact ⟨j', u, hu, 1, one_pos, hφ, hpath, by rw [hdir, one_smul]⟩

/-- **Subdividing an edge reparametrizes the boundary.** Subdividing edge `i` of a polygon at an
interior point changes its boundary parametrization by an increasing change of time `φ`, mapping
one period `[0, n)` into `[0, n + 1)`. At each time `t` the subdivided polygon runs along an edge
whose direction is a positive multiple of the direction of the edge along which `poly` runs at
time `t`. -/
theorem exists_strictMono_boundaryParam_insertVertex_edgePath (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∃ φ : ℝ → ℝ, StrictMono φ ∧ ∀ t ∈ Ico (0 : ℝ) n, φ t ∈ Ico (0 : ℝ) (n + 1 : ℕ) ∧
      (poly.insertVertex i (poly.edgePath ℝ i s)).boundaryParam (φ t) = poly.boundaryParam t ∧
      ∃ r : ℝ, 0 < r ∧
        poly.insertVertex i (poly.edgePath ℝ i s) (finRotate (n + 1) (edgeIndexAt (n + 1) (φ t))) -ᵥ
            poly.insertVertex i (poly.edgePath ℝ i s) (edgeIndexAt (n + 1) (φ t)) =
          r • (poly (finRotate n (edgeIndexAt n t)) -ᵥ poly (edgeIndexAt n t)) := by
  refine ⟨subdivisionTime ((i : ℕ) : ℝ) s, strictMono_subdivisionTime _ hs, fun t ht ↦ ?_⟩
  obtain ⟨j, u, hu, rfl⟩ := TauCeti.exists_eq_natCast_add_of_mem_Ico ht
  obtain ⟨j', u', hu', r, hr, hφ, hpath, hdir⟩ := exists_subdivisionTime_eq poly i hs j hu
  rw [hφ, boundaryParam_natCast_add _ _ (Ico_subset_Icc_self hu'),
    poly.boundaryParam_natCast_add j (Ico_subset_Icc_self hu), hpath,
    edgeIndexAt_natCast_add _ hu', edgeIndexAt_natCast_add _ hu]
  refine ⟨⟨add_nonneg (Nat.cast_nonneg _) hu'.1, ?_⟩, rfl, r, hr, hdir⟩
  have hj' : ((j' : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast j'.isLt
  linarith [hu'.2]

/-- **Inserting a vertex reparametrizes the boundary away from the moved edge.** Inserting any
vertex `c` after vertex `i` of a polygon changes its boundary parametrization, away from edge `i`,
by an increasing change of time `φ`. At each time `t ∈ [0, n)` at which `poly` does not run along
edge `i`, the time `φ t` lies in `[0, n + 1)`, and the new polygon is at the same point at time
`φ t`, running along an edge with the same direction. -/
theorem exists_strictMono_boundaryParam_insertVertex (c : P) :
    ∃ φ : ℝ → ℝ, StrictMono φ ∧ ∀ t ∈ Ico (0 : ℝ) n, edgeIndexAt n t ≠ i →
      φ t ∈ Ico (0 : ℝ) (n + 1 : ℕ) ∧
      (poly.insertVertex i c).boundaryParam (φ t) = poly.boundaryParam t ∧
      poly.insertVertex i c (finRotate (n + 1) (edgeIndexAt (n + 1) (φ t))) -ᵥ
          poly.insertVertex i c (edgeIndexAt (n + 1) (φ t)) =
        poly (finRotate n (edgeIndexAt n t)) -ᵥ poly (edgeIndexAt n t) := by
  have hs : (2⁻¹ : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  refine ⟨subdivisionTime ((i : ℕ) : ℝ) 2⁻¹, strictMono_subdivisionTime _ hs, fun t ht hti ↦ ?_⟩
  obtain ⟨j, u, hu, rfl⟩ := TauCeti.exists_eq_natCast_add_of_mem_Ico ht
  rw [edgeIndexAt_natCast_add _ hu] at hti ⊢
  obtain ⟨j', hφ, hpath, hdir⟩ := exists_subdivisionTime_eq_of_ne poly i hs c hti hu
  rw [hφ, boundaryParam_natCast_add _ _ (Ico_subset_Icc_self hu),
    poly.boundaryParam_natCast_add j (Ico_subset_Icc_self hu), hpath, edgeIndexAt_natCast_add _ hu]
  refine ⟨⟨add_nonneg (Nat.cast_nonneg _) hu.1, ?_⟩, rfl, hdir⟩
  have hj' : ((j' : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast j'.isLt
  linarith [hu.2]

end Param

end Polygon
