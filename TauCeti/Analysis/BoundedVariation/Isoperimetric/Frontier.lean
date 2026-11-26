/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import Mathlib.Geometry.Euclidean.Volume.Measure
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Analysis.BoundedVariation.FrontierCriterion
import TauCeti.Analysis.BoundedVariation.Isoperimetric.Basic
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.Geometry.Euclidean.Volume.Sphere
import TauCeti.MeasureTheory.Measure.Haar.Hausdorff.Frontier

/-!
# The isoperimetric inequality for the topological frontier

Let `E` be a finite-dimensional real inner product space of dimension `n ≥ 2`, write
`ω_n = volume (ball 0 1)`, and let `Hⁿ⁻¹ = μHE[n - 1]` be the normalized Euclidean Hausdorff
measure. This file proves that every set `s` of finite volume, measurable or not, satisfies

`nⁿ ω_n |s|ⁿ⁻¹ ≤ Hⁿ⁻¹(frontier s)ⁿ`

(`TauCeti.finrank_pow_mul_volume_ball_mul_volume_pow_le_euclideanHausdorffMeasure_frontier_pow`),
in particular every bounded set, which has finite volume. The two sides are compared through the
perimeter `P(s)`: when `Hⁿ⁻¹(frontier s) < ∞`, the frontier of `s` is null and `s` is
null-measurable (`TauCeti.nullMeasurableSet_of_hausdorffMeasure_frontier_ne_top`), and then
`P(s) ≤ Hⁿ⁻¹(frontier s)` (`TauCeti.perimeter_le_euclideanHausdorffMeasure_frontier`) and the
sharp isoperimetric inequality for the perimeter conclude.

Balls attain equality (`TauCeti.euclideanHausdorffMeasure_frontier_ball_pow`). Conversely,
equality forces the frontier to have finite measure, the perimeter of `s` to equal
`Hⁿ⁻¹(frontier s)` (`TauCeti.perimeter_eq_of_euclideanHausdorffMeasure_frontier_pow_eq`), and
hence equality in the sharp inequality for the perimeter
(`TauCeti.perimeter_pow_eq_of_euclideanHausdorffMeasure_frontier_pow_eq`), the hypothesis of ball
rigidity for sets of finite perimeter.

The frontier is sensitive to null modifications while the volume is not: in `ℝⁿ`, removing the
points with rational coordinates from a ball gives a set whose frontier is the closed ball, of
infinite `Hⁿ⁻¹` measure, so the inequality is strict for it. The finite-volume hypothesis is
needed: the complement of a ball has infinite volume and a frontier of finite measure.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, §14.2, for the isoperimetric inequality for sets of finite perimeter.
* H. Federer, *Geometric Measure Theory*, Springer, 1969, 4.5.11, for the bound of the perimeter
  by the Hausdorff measure of the topological frontier.
-/

public section

open MeasureTheory Metric Module Set
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {s : Set E}

/-- A set whose frontier has finite `Hⁿ⁻¹` measure is null-measurable for the volume. -/
private theorem nullMeasurableSet_of_euclideanHausdorffMeasure_frontier_ne_top
    (hH : μHE[finrank ℝ E - 1] (frontier s) ≠ ∞) : NullMeasurableSet s volume :=
  nullMeasurableSet_of_hausdorffMeasure_frontier_ne_top volume
    (Measure.euclideanHausdorffMeasure_lt_top_iff.1 (lt_top_iff_ne_top.2 hH)).ne

/-- **The isoperimetric inequality for the topological frontier.** In a Euclidean space of
dimension `n ≥ 2`, every set `s` of finite volume, measurable or not, satisfies
`nⁿ ω_n |s|ⁿ⁻¹ ≤ Hⁿ⁻¹(frontier s)ⁿ`, where `ω_n = volume (ball 0 1)` and `Hⁿ⁻¹` is the normalized
Euclidean Hausdorff measure. Balls attain equality
(`TauCeti.euclideanHausdorffMeasure_frontier_ball_pow`). -/
theorem finrank_pow_mul_volume_ball_mul_volume_pow_le_euclideanHausdorffMeasure_frontier_pow
    (hn : 2 ≤ finrank ℝ E) (hs : volume s ≠ ∞) :
    (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) * volume s ^ (finrank ℝ E - 1) ≤
      μHE[finrank ℝ E - 1] (frontier s) ^ finrank ℝ E := by
  by_cases hH : μHE[finrank ℝ E - 1] (frontier s) = ∞
  · rw [hH, ENNReal.top_pow (by omega)]
    exact le_top
  exact ((nullMeasurableSet_of_euclideanHausdorffMeasure_frontier_ne_top
    hH).finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow_of_two_le hs hn).trans
    (pow_le_pow_left₀ zero_le (perimeter_le_euclideanHausdorffMeasure_frontier s) _)

/-- **Balls attain equality in the frontier isoperimetric inequality.** In positive dimension `n`,
a ball of radius `r > 0` satisfies `Hⁿ⁻¹(frontier (ball c r))ⁿ = nⁿ ω_n |ball c r|ⁿ⁻¹`, where
`ω_n = volume (ball 0 1)`. -/
theorem euclideanHausdorffMeasure_frontier_ball_pow (hn : finrank ℝ E ≠ 0) (c : E) {r : ℝ}
    (hr : 0 < r) :
    μHE[finrank ℝ E - 1] (frontier (ball c r)) ^ finrank ℝ E =
      (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
        volume (ball c r) ^ (finrank ℝ E - 1) := by
  have h : μHE[finrank ℝ E - 1] (frontier (ball c r)) = perimeter volume ⊤ (ball c r) := by
    rw [frontier_ball c hr.ne', euclideanHausdorffMeasure_sphere c hr, perimeter_ball hr,
      ENNReal.ofReal_pow hr.le]
    ring
  rw [h, perimeter_ball_pow hn hr]

/-- **Equality in the frontier isoperimetric inequality identifies the perimeter.** In a
Euclidean space of dimension `n ≥ 2`, if a set `s` of finite volume satisfies
`Hⁿ⁻¹(frontier s)ⁿ = nⁿ ω_n |s|ⁿ⁻¹`, where `ω_n = volume (ball 0 1)`, then its perimeter is the
Hausdorff measure of its frontier. -/
theorem perimeter_eq_of_euclideanHausdorffMeasure_frontier_pow_eq
    (hn : 2 ≤ finrank ℝ E) (hs : volume s ≠ ∞)
    (h : μHE[finrank ℝ E - 1] (frontier s) ^ finrank ℝ E =
      (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
        volume s ^ (finrank ℝ E - 1)) :
    perimeter volume ⊤ s = μHE[finrank ℝ E - 1] (frontier s) := by
  -- The right side of `h` is finite, so the frontier has finite measure and `s` is measurable.
  have hH : μHE[finrank ℝ E - 1] (frontier s) ≠ ∞ := by
    intro hH
    rw [hH, ENNReal.top_pow (by omega)] at h
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne)
      (ENNReal.pow_ne_top hs) h.symm
  -- The sharp inequality for the perimeter gives the reverse comparison of `n`-th powers.
  refine le_antisymm (perimeter_le_euclideanHausdorffMeasure_frontier s)
    ((ENNReal.pow_le_pow_left_iff (n := finrank ℝ E) (by omega)).1 ?_)
  rw [h]
  exact (nullMeasurableSet_of_euclideanHausdorffMeasure_frontier_ne_top
    hH).finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow_of_two_le hs hn

/-- **Equality in the frontier isoperimetric inequality forces equality for the perimeter.** In a
Euclidean space of dimension `n ≥ 2`, if a set `s` of finite volume satisfies
`Hⁿ⁻¹(frontier s)ⁿ = nⁿ ω_n |s|ⁿ⁻¹`, where `ω_n = volume (ball 0 1)`, then it attains equality in
the sharp isoperimetric inequality for the perimeter: `P(s)ⁿ = nⁿ ω_n |s|ⁿ⁻¹`. -/
theorem perimeter_pow_eq_of_euclideanHausdorffMeasure_frontier_pow_eq
    (hn : 2 ≤ finrank ℝ E) (hs : volume s ≠ ∞)
    (h : μHE[finrank ℝ E - 1] (frontier s) ^ finrank ℝ E =
      (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
        volume s ^ (finrank ℝ E - 1)) :
    perimeter volume ⊤ s ^ finrank ℝ E =
      (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
        volume s ^ (finrank ℝ E - 1) := by
  rw [perimeter_eq_of_euclideanHausdorffMeasure_frontier_pow_eq hn hs h, h]

end TauCeti
