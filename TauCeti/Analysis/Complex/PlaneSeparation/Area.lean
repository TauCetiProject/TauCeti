/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve
-- Supplies the locally convex, hence locally connected, instance on the complex plane.
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# The area enclosed by a Jordan curve

The inside of a Jordan curve `C ⊆ ℂ` is `filledHull C \ C`, the union of the bounded components
of the complement of `C`. Its Lebesgue area is the area term in the planar isoperimetric
inequality. This file shows that this area is positive and finite, so that it may be compared
with the length of the curve in real arithmetic.

Finiteness holds because the filled hull of a bounded set is bounded
(`TauCeti.isBounded_filledHull`), hence has finite measure. Positivity uses the Jordan curve
theorem: the inside is open, as the union of components of the open complement of a closed set
(`IsClosed.isOpen_filledHull_sdiff`), and nonempty
(`TauCeti.IsJordanCurve.nonempty_filledHull_sdiff`).
Both statements are proved for every measure with the relevant regularity, in particular for
`volume` on `ℂ`.

## Main results

* `TauCeti.IsJordanCurve.measure_filledHull_sdiff_pos`: the inside of a Jordan curve has positive
  area.
* `TauCeti.IsJordanCurve.measure_filledHull_sdiff_lt_top`: the inside of a Jordan curve has finite
  area.
* `TauCeti.IsJordanCurve.measureReal_filledHull_sdiff_pos`: the same for the real-valued area.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {C : Set ℂ}

/-- **The inside of a Jordan curve has positive area.** For a Jordan curve `C ⊆ ℂ` and a measure
which is positive on nonempty open sets, such as `volume`, the inside `filledHull C \ C` has
positive measure. -/
theorem IsJordanCurve.measure_filledHull_sdiff_pos (h : IsJordanCurve C)
    (μ : Measure ℂ := by volume_tac) [μ.IsOpenPosMeasure] : 0 < μ (filledHull C \ C) :=
  h.isClosed.isOpen_filledHull_sdiff.measure_pos μ h.nonempty_filledHull_sdiff

/-- **The inside of a Jordan curve has finite area.** For a Jordan curve `C ⊆ ℂ` and a measure
which is finite on compact sets, such as `volume`, the inside `filledHull C \ C` has finite
measure. -/
theorem IsJordanCurve.measure_filledHull_sdiff_lt_top (h : IsJordanCurve C)
    (μ : Measure ℂ := by volume_tac) [IsFiniteMeasureOnCompacts μ] :
    μ (filledHull C \ C) < ∞ :=
  ((isBounded_filledHull.2 h.isCompact.isBounded).subset sdiff_subset).measure_lt_top

/-- **The inside of a Jordan curve has positive finite area.** For a Jordan curve `C ⊆ ℂ` and a
measure which is positive on nonempty open sets and finite on compact sets, such as `volume`, the
real-valued measure of the inside `filledHull C \ C` is positive. -/
theorem IsJordanCurve.measureReal_filledHull_sdiff_pos (h : IsJordanCurve C)
    (μ : Measure ℂ := by volume_tac) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ] :
    0 < μ.real (filledHull C \ C) :=
  ENNReal.toReal_pos (h.measure_filledHull_sdiff_pos μ).ne' (h.measure_filledHull_sdiff_lt_top μ).ne

end TauCeti
