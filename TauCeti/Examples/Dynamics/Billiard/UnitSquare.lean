/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.PhaseSpace
public import TauCeti.Analysis.Complex.Rectangle
import TauCeti.Analysis.Complex.PlaneSeparation.Convex
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The unit square as a polygonal billiard table

The polygon with vertices `0, 1, 1 + i, i` in this order is simple
(`TauCeti.Examples.UnitSquare.isSimple_squarePolygon`): its edges are the four sides of the unit
square, and two distinct sides meet only at the common vertex of consecutive sides. Its boundary
is the frontier of the closed unit square `[0, 1] × [0, 1]`
(`TauCeti.Examples.UnitSquare.boundary_squarePolygon`), so the polygonal table it bounds
(`TauCeti.Examples.UnitSquare.unitSquareTable`) has as carrier the closed unit square
(`TauCeti.Examples.UnitSquare.carrier_unitSquareTable`), `n = 4` vertices and `h = 0` holes
(`TauCeti.Examples.UnitSquare.ncard_vertexSet_unitSquareTable`,
`TauCeti.Examples.UnitSquare.numHoles_unitSquareTable`).

The Liouville probability measure `μ_P` of its phase space gives the states whose position lies in
the square `[0, 1/2] × [0, 1/2]` the mass `1/4`
(`TauCeti.Examples.UnitSquare.liouville_position_preimage_quarter`): the position is well defined
on the phase space, since the identification of states at the sides keeps the position
(`TauCeti.Examples.UnitSquare.position`), and `μ_P` is the area of the position set, divided by
the area `1` of the table, the directions contributing a factor `2π / 2π`.
-/

open Complex Set MeasureTheory
open scoped ENNReal Real ComplexConjugate

public noncomputable section

namespace TauCeti.Examples.UnitSquare

/-- The polygon with vertices `0, 1, 1 + i, i`, in counterclockwise order. -/
def squarePolygon : Polygon ℂ 4 := ⟨![0, 1, 1 + I, I]⟩

/-- The first vertex of the square polygon is `0`. -/
@[simp] theorem squarePolygon_zero : squarePolygon 0 = 0 := (rfl)

/-- The second vertex of the square polygon is `1`. -/
@[simp] theorem squarePolygon_one : squarePolygon 1 = 1 := (rfl)

/-- The third vertex of the square polygon is `1 + I`. -/
@[simp] theorem squarePolygon_two : squarePolygon 2 = 1 + I := (rfl)

/-- The fourth vertex of the square polygon is `I`. -/
@[simp] theorem squarePolygon_three : squarePolygon 3 = I := (rfl)

/-- The edges of the square polygon, as horizontal and vertical segments. -/
theorem edgeSet_squarePolygon (i : Fin 4) :
    squarePolygon.edgeSet ℝ i =
      ![Icc 0 1 ×ℂ {0}, {1} ×ℂ Icc 0 1, Icc 0 1 ×ℂ {1}, {0} ×ℂ Icc 0 1] i := by
  rw [Polygon.edgeSet, affineSegment_eq_segment, finRotate_apply]
  fin_cases i
  · rw [segment_eq_reProdIm_of_im_eq] <;> simp [squarePolygon]
  · rw [segment_eq_reProdIm_of_re_eq] <;> simp [squarePolygon]
  · rw [segment_eq_reProdIm_of_im_eq] <;> simp [squarePolygon, uIcc_of_ge]
  · rw [segment_eq_reProdIm_of_re_eq] <;> simp [squarePolygon, uIcc_of_ge]

/-- **The square polygon is simple.** -/
theorem isSimple_squarePolygon : squarePolygon.IsSimple ℝ := by
  refine ⟨fun i => ?_, fun i j x hij hi hj => ?_⟩
  · rw [finRotate_apply]
    fin_cases i <;> simp [squarePolygon, Complex.ext_iff]
  · rw [edgeSet_squarePolygon] at hi hj
    rw [finRotate_apply, finRotate_apply]
    fin_cases i <;> fin_cases j <;>
      simp_all [mem_reProdIm, Complex.ext_iff]

/-- The unit square as a simple polygon. -/
def squareSimplePolygon : SimplePolygon ℝ ℂ where
  numVertices := 4
  toPolygon := squarePolygon
  isSimple := isSimple_squarePolygon

/-- The boundary of the square polygon is the frontier of the closed unit square
`Rectangle 0 (1 + I) = [0, 1] × [0, 1]`. -/
theorem boundary_squarePolygon : squarePolygon.boundary ℝ = frontier (Rectangle 0 (1 + I)) := by
  rw [frontier_rectangle, Polygon.boundary]
  ext x
  simp only [mem_iUnion, edgeSet_squarePolygon, mem_union, mem_reProdIm, mem_singleton_iff,
    mem_insert_iff, zero_re, zero_im, add_re, add_im, one_re, one_im, I_re, I_im, add_zero,
    zero_add, uIcc_of_le zero_le_one]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp [mem_reProdIm] at hi <;> tauto
  · rintro (⟨h1, h | h⟩ | ⟨h | h, h2⟩)
    · exact ⟨0, by simpa [mem_reProdIm] using ⟨h1, h⟩⟩
    · exact ⟨2, by simpa [mem_reProdIm] using ⟨h1, h⟩⟩
    · exact ⟨3, by simpa [mem_reProdIm] using ⟨h, h2⟩⟩
    · exact ⟨1, by simpa [mem_reProdIm] using ⟨h, h2⟩⟩

/-- The polygonal billiard table bounded by the unit square. -/
def unitSquareTable : PolygonalTable :=
  PolygonalTable.ofSimplePolygon squareSimplePolygon

/-- The unit-square table has no holes. -/
theorem numHoles_unitSquareTable : unitSquareTable.numHoles = 0 :=
  PolygonalTable.ofSimplePolygon_numHoles _

/-- **The carrier of the unit-square table is the closed unit square** `[0, 1] × [0, 1]`. -/
theorem carrier_unitSquareTable : unitSquareTable.carrier = Rectangle 0 (1 + I) := by
  rw [unitSquareTable, PolygonalTable.ofSimplePolygon_carrier]
  -- `squareSimplePolygon.toPolygon` is `squarePolygon` by definition; its type
  -- `Polygon ℂ squareSimplePolygon.numVertices` only unfolds to `Polygon ℂ 4`, so we `change`.
  change filledHull (squarePolygon.boundary ℝ) = _
  rw [boundary_squarePolygon,
    (convex_rectangle 0 (1 + I)).filledHull_frontier
      (interior_rectangle_nonempty (by simp) (by simp)) (isCompact_rectangle 0 (1 + I)).isBounded,
    (isClosed_rectangle 0 (1 + I)).closure_eq]

/-- **The unit-square table has four vertices.** -/
theorem ncard_vertexSet_unitSquareTable : unitSquareTable.vertexSet.ncard = 4 := by
  rw [unitSquareTable, PolygonalTable.vertexSet_ofSimplePolygon]
  -- As in `carrier_unitSquareTable`, `squareSimplePolygon.toPolygon` is `squarePolygon` by
  -- definition, up to the dependent vertex count.
  change (range squarePolygon.vertices).ncard = 4
  have hinj : Function.Injective squarePolygon.vertices := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [squarePolygon, Complex.ext_iff]
  rw [ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The position of a state of the unit-square table: the identification of states at the sides
keeps the position. -/
def position : unitSquareTable.PhaseSpace → ℂ :=
  PolygonalTable.PhaseSpace.lift (fun p => (p.1 : ℂ)) fun p q h => by
    rcases PolygonalTable.phaseRel_iff.1 h with rfl | ⟨h1, -⟩
    · rfl
    · rw [h1]

/-- The position of the class of a state is its base point. -/
@[simp]
theorem position_mk (p : unitSquareTable.carrier × Circle) :
    position (PolygonalTable.PhaseSpace.mk p) = p.1 :=
  PolygonalTable.PhaseSpace.lift_mk _ _ p

/-- The position is measurable. -/
theorem measurable_position : Measurable position :=
  PolygonalTable.PhaseSpace.measurable_lift (continuous_subtypeVal.comp continuous_fst).measurable

/-- **The Liouville measure of a quarter of the unit square.** The states of the unit-square table
whose position lies in `[0, 1/2] × [0, 1/2]` have Liouville measure `1/4`. -/
theorem liouville_position_preimage_quarter :
    unitSquareTable.liouville (position ⁻¹' (Icc 0 (1 / 2) ×ℂ Icc 0 (1 / 2))) =
      ENNReal.ofReal (1 / 4) := by
  set Q : Set ℂ := Icc 0 (1 / 2) ×ℂ Icc 0 (1 / 2)
  have hQm : MeasurableSet Q := measurableSet_Icc.reProdIm measurableSet_Icc
  have hQ : Q ⊆ unitSquareTable.carrier := by
    rw [carrier_unitSquareTable]
    intro x hx
    simp only [Q, mem_reProdIm, mem_Icc] at hx
    rw [mem_rectangle_iff (by simp) (by simp)]
    simp only [zero_re, zero_im, add_re, add_im, one_re, one_im, I_re, I_im, add_zero, zero_add]
    exact ⟨⟨hx.1.1, by linarith [hx.1.2]⟩, ⟨hx.2.1, by linarith [hx.2.2]⟩⟩
  have hpre : PolygonalTable.PhaseSpace.mk ⁻¹' (position ⁻¹' Q) =
      ((↑) ⁻¹' Q : Set unitSquareTable.carrier) ×ˢ univ := by
    ext p
    simp
  have hvolQ : volume Q = ENNReal.ofReal (1 / 4) := by
    rw [volume_reProdIm, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hvol : volume (Rectangle 0 (1 + I)) = 1 := by
    rw [Rectangle, volume_reProdIm]
    simp
  have h2π : ENNReal.ofReal (2 * π) ≠ 0 := by simp [Real.pi_pos]
  rw [unitSquareTable.liouville_apply (measurable_position hQm), hpre, Measure.prod_prod,
    comap_subtypeVal_apply unitSquareTable.isClosed_carrier.measurableSet,
    image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.2 hQ, hvolQ,
    circleArcLength_univ, carrier_unitSquareTable, hvol]
  -- `(2π · 1)⁻¹ · (1/4 · 2π) = 1/4`
  rw [mul_one, mul_left_comm, ENNReal.inv_mul_cancel h2π ENNReal.ofReal_ne_top, mul_one]

end TauCeti.Examples.UnitSquare
