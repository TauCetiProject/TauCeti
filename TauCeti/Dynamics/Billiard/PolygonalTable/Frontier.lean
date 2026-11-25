/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.PolygonalTable
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.ConstantSpeed
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The frontier of a polygonal table is a null set

The frontier of a polygonal billiard table is the union of its finitely many sides. Each side is a
segment in `ℂ`, the image of a Lipschitz curve, so it is Lebesgue-null
(`LocallyBoundedVariationOn.addHaar_image_eq_zero`). Hence the frontier is a Lebesgue-null set
(`TauCeti.PolygonalTable.volume_frontier_carrier`), and the table and its interior have the same
area (`TauCeti.PolygonalTable.volume_interior_carrier`). The positions on the frontier therefore
carry no mass for the Liouville measure of the table.

## References

* N. Chernov, R. Markarian, *Chaotic Billiards*, Mathematical Surveys and Monographs 127, AMS
  (2006), Chapter 2.
-/

public section

open MeasureTheory Set

namespace TauCeti.PolygonalTable

variable (T : PolygonalTable)

/-- **The frontier of a polygonal table is Lebesgue-null**: it is the union of the finitely many
sides of the table, which are segments. -/
theorem volume_frontier_carrier : volume (frontier T.carrier) = 0 := by
  rw [frontier_eq_iUnion_side, measure_iUnion_null_iff]
  intro s
  rw [side_eq_segment, segment_eq_image_lineMap]
  exact ((lipschitzWith_lineMap _ _).locallyBoundedVariationOn _).addHaar_image_eq_zero volume
    (by simp)

/-- A polygonal table and its interior have the same area. -/
theorem volume_interior_carrier : volume (interior T.carrier) = volume T.carrier :=
  measure_congr (interior_ae_eq_of_null_frontier T.volume_frontier_carrier)

end TauCeti.PolygonalTable
