/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.PolygonalTable
public import TauCeti.Analysis.Complex.Rectangle
import TauCeti.Analysis.Complex.PlaneSeparation.Convex

/-!
# A polygonal billiard table with a flat vertex

The polygon with vertices `0, 1, 2, 2 + i, i` in this order is simple
(`TauCeti.Examples.FlatVertex.isSimple_flatPolygon`), although its vertex `1` lies on the open
segment between its neighbours `0` and `2`, so that the interior angle there is `π`
(`TauCeti.Examples.FlatVertex.flatPolygon_one_mem_openSegment`). Its boundary is the frontier of
the closed rectangle `[0, 2] × [0, 1]` (`TauCeti.Examples.FlatVertex.boundary_flatPolygon`), so
it bounds a polygonal table (`TauCeti.Examples.FlatVertex.flatVertexTable`) with this rectangle
as carrier (`TauCeti.Examples.FlatVertex.carrier_flatVertexTable`), `h = 0` holes, and `n = 5`
vertices, the flat vertex `1` among them
(`TauCeti.Examples.FlatVertex.one_mem_vertexSet_flatVertexTable`,
`TauCeti.Examples.FlatVertex.ncard_vertexSet_flatVertexTable`).
-/

open Complex Set

public noncomputable section

namespace TauCeti.Examples.FlatVertex

/-- The polygon with vertices `0, 1, 2, 2 + i, i`, in counterclockwise order. -/
def flatPolygon : Polygon ℂ 5 := ⟨![0, 1, 2, 2 + I, I]⟩

/-- The first vertex of the flat polygon is `0`. -/
@[simp] theorem flatPolygon_zero : flatPolygon 0 = 0 := (rfl)

/-- The second vertex of the flat polygon is `1`. -/
@[simp] theorem flatPolygon_one : flatPolygon 1 = 1 := (rfl)

/-- The third vertex of the flat polygon is `2`. -/
@[simp] theorem flatPolygon_two : flatPolygon 2 = 2 := (rfl)

/-- The fourth vertex of the flat polygon is `2 + I`. -/
@[simp] theorem flatPolygon_three : flatPolygon 3 = 2 + I := (rfl)

/-- The fifth vertex of the flat polygon is `I`. -/
@[simp] theorem flatPolygon_four : flatPolygon 4 = I := (rfl)

/-- The edges of the flat polygon, as horizontal and vertical segments. -/
theorem edgeSet_flatPolygon (i : Fin 5) :
    flatPolygon.edgeSet ℝ i =
      ![Icc 0 1 ×ℂ {0}, Icc 1 2 ×ℂ {0}, {2} ×ℂ Icc 0 1, Icc 0 2 ×ℂ {1}, {0} ×ℂ Icc 0 1] i := by
  rw [Polygon.edgeSet, affineSegment_eq_segment, finRotate_apply]
  fin_cases i
  · rw [segment_eq_reProdIm_of_im_eq] <;> simp [flatPolygon]
  · rw [segment_eq_reProdIm_of_im_eq] <;> norm_num [flatPolygon]
  · rw [segment_eq_reProdIm_of_re_eq] <;> simp [flatPolygon]
  · rw [segment_eq_reProdIm_of_im_eq] <;> simp [flatPolygon, uIcc_of_ge]
  · rw [segment_eq_reProdIm_of_re_eq] <;> simp [flatPolygon, uIcc_of_ge]

/-- **The flat polygon is simple.** -/
theorem isSimple_flatPolygon : flatPolygon.IsSimple ℝ := by
  refine ⟨fun i => ?_, fun i j x hij hi hj => ?_⟩
  · rw [finRotate_apply]
    fin_cases i <;> norm_num [flatPolygon, Complex.ext_iff]
  · rw [edgeSet_flatPolygon] at hi hj
    rw [finRotate_apply, finRotate_apply]
    fin_cases i <;> fin_cases j <;>
      simp [mem_reProdIm, Complex.ext_iff] at hi hj ⊢ <;> grind

/-- The vertex `1` of the flat polygon is flat: it lies on the open segment between its
neighbours `0` and `2`. -/
theorem flatPolygon_one_mem_openSegment :
    flatPolygon 1 ∈ openSegment ℝ (flatPolygon 0) (flatPolygon 2) := by
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  simp only [flatPolygon]
  norm_num [Complex.ext_iff]

/-- The flat polygon as a simple polygon. -/
def flatSimplePolygon : SimplePolygon ℝ ℂ where
  numVertices := 5
  toPolygon := flatPolygon
  isSimple := isSimple_flatPolygon

/-- The boundary of the flat polygon is the frontier of the closed rectangle
`Rectangle 0 (2 + I) = [0, 2] × [0, 1]`. -/
theorem boundary_flatPolygon : flatPolygon.boundary ℝ = frontier (Rectangle 0 (2 + I)) := by
  rw [frontier_rectangle, Polygon.boundary]
  ext x
  simp only [mem_iUnion, edgeSet_flatPolygon, mem_union, mem_reProdIm, mem_singleton_iff,
    mem_insert_iff, zero_re, zero_im, add_re, add_im, I_re, I_im, add_zero]
  norm_num [uIcc_of_le]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp [mem_reProdIm] at hi <;> grind
  · rintro (⟨h1, h | h⟩ | ⟨h | h, h2⟩)
    · rcases le_total x.re 1 with hx | hx
      · exact ⟨0, by simpa [mem_reProdIm] using ⟨⟨h1.1, hx⟩, h⟩⟩
      · exact ⟨1, by simpa [mem_reProdIm] using ⟨⟨hx, h1.2⟩, h⟩⟩
    · exact ⟨3, by simpa [mem_reProdIm] using ⟨h1, h⟩⟩
    · exact ⟨4, by simpa [mem_reProdIm] using ⟨h, h2⟩⟩
    · exact ⟨2, by simpa [mem_reProdIm] using ⟨h, h2⟩⟩

/-- The polygonal billiard table bounded by the flat polygon. -/
def flatVertexTable : PolygonalTable :=
  PolygonalTable.ofSimplePolygon flatSimplePolygon

/-- The flat-vertex table has no holes. -/
theorem numHoles_flatVertexTable : flatVertexTable.numHoles = 0 :=
  PolygonalTable.ofSimplePolygon_numHoles _

/-- **The carrier of the flat-vertex table is the closed rectangle** `[0, 2] × [0, 1]`. -/
theorem carrier_flatVertexTable : flatVertexTable.carrier = Rectangle 0 (2 + I) := by
  rw [flatVertexTable, PolygonalTable.ofSimplePolygon_carrier]
  -- `flatSimplePolygon.toPolygon` is `flatPolygon` by definition, up to the dependent vertex
  -- count, so we `change`.
  change filledHull (flatPolygon.boundary ℝ) = _
  rw [boundary_flatPolygon,
    (convex_rectangle 0 (2 + I)).filledHull_frontier
      (interior_rectangle_nonempty (by simp) (by simp)) (isCompact_rectangle 0 (2 + I)).isBounded,
    (isClosed_rectangle 0 (2 + I)).closure_eq]

/-- **The flat vertex is a vertex of the table.** -/
theorem one_mem_vertexSet_flatVertexTable : (1 : ℂ) ∈ flatVertexTable.vertexSet := by
  rw [flatVertexTable, PolygonalTable.vertexSet_ofSimplePolygon]
  exact ⟨(1 : Fin 5), rfl⟩

/-- **The flat-vertex table has five vertices.** -/
theorem ncard_vertexSet_flatVertexTable : flatVertexTable.vertexSet.ncard = 5 := by
  rw [flatVertexTable, PolygonalTable.vertexSet_ofSimplePolygon]
  -- As in `carrier_flatVertexTable`, `flatSimplePolygon.toPolygon` is `flatPolygon`.
  change (range flatPolygon.vertices).ncard = 5
  have hinj : Function.Injective flatPolygon.vertices := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      first | rfl | norm_num [flatPolygon, Complex.ext_iff] at h
  rw [ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]

end TauCeti.Examples.FlatVertex
