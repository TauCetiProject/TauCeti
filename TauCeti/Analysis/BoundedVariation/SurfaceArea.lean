/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.Convex.Measure
import TauCeti.Analysis.BoundedVariation.Convex
import TauCeti.Analysis.BoundedVariation.DeGiorgi
import TauCeti.Analysis.BoundedVariation.EssentialBoundary
import TauCeti.Analysis.BoundedVariation.ParallelVolume
import TauCeti.MeasureTheory.Covering.EssentialBoundary
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The surface area of a convex set

Let `E` be a finite-dimensional real inner product space of dimension `n ≥ 2`, and write
`Hⁿ⁻¹ = μHE[n - 1]` for the normalized `(n - 1)`-dimensional Euclidean Hausdorff measure. For a
convex set `K ⊆ E` with nonempty interior, bounded or not, the perimeter of `K` is the Hausdorff
measure of its topological frontier:

`P(K; Ω) = Hⁿ⁻¹(frontier K ∩ Ω)` for every open `Ω`, and `P(K) = Hⁿ⁻¹(frontier K)`

(`Convex.perimeter_eq_euclideanHausdorffMeasure_frontier_inter`,
`Convex.perimeter_eq_euclideanHausdorffMeasure_frontier`). So the surface area of a convex body,
defined measure-theoretically as its perimeter, agrees with the Hausdorff area of its boundary.
For a compact convex set with nonempty interior, the volume of the outer parallel body
`K + t • closedBall 0 1` therefore has right derivative `Hⁿ⁻¹(frontier K)` at `t = 0`
(`Convex.hasDerivWithinAt_volume_real_add_smul_closedBall_euclideanHausdorffMeasure_frontier`).

The nonempty interior is needed: a compact convex set `K` with empty interior lies in a
hyperplane, so it is null and has perimeter zero, while its frontier is `K` itself, which may have
positive `Hⁿ⁻¹`-measure, as for a segment in the plane. Its parallel volume then has right
derivative `2 Hⁿ⁻¹(K)` when its affine span has dimension `n - 1`
(`TauCeti.hasDerivWithinAt_volume_real_add_smul_closedBall_of_finrank_add_one_eq`).

The proof combines three facts. Convex sets have locally finite perimeter
(`Convex.exists_opens_totalVariationOn_indicator_ne_top`), so De Giorgi's theorem gives
`P(K; Ω) = Hⁿ⁻¹(∂*K)` for the reduced boundary `∂*K` of `K` in `Ω`
(`TauCeti.perimeter_eq_euclideanHausdorffMeasure_reducedBoundary`), and Federer's theorem says that
`∂*K` and the part in `Ω` of the essential boundary `∂ᵉK` agree up to an `Hⁿ⁻¹`-null set
(`TauCeti.essentialBoundary_inter_ae_eq_reducedBoundary`). Finally, `K` has neither density zero
nor density one at a point of its frontier, so `∂ᵉK = frontier K`
(`Convex.essentialBoundary_eq_frontier`).

## Main results

* `Convex.perimeter_eq_euclideanHausdorffMeasure_frontier_inter`:
  `P(K; Ω) = Hⁿ⁻¹(frontier K ∩ Ω)`.
* `Convex.perimeter_eq_euclideanHausdorffMeasure_frontier`: `P(K) = Hⁿ⁻¹(frontier K)`.
* `Convex.hasDerivWithinAt_volume_real_add_smul_closedBall_euclideanHausdorffMeasure_frontier`:
  the outer parallel volume of a compact convex set with nonempty interior has right derivative
  `Hⁿ⁻¹(frontier K)` at zero.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Theorem 15.9 and Theorem 16.2.
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §5.8.
-/

public section

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {K : Set E}

namespace Convex

open TauCeti

/-- **The perimeter of a convex set is the Hausdorff measure of its frontier.** In dimension
`n ≥ 2`, a convex set `K` with nonempty interior has `P(K; Ω) = Hⁿ⁻¹(frontier K ∩ Ω)` in every
open set `Ω`. No boundedness of `K` is needed. -/
theorem perimeter_eq_euclideanHausdorffMeasure_frontier_inter (hn : 2 ≤ finrank ℝ E)
    (hK : Convex ℝ K) (hKi : (interior K).Nonempty) (Ω : Opens E) :
    perimeter volume Ω K = μHE[finrank ℝ E - 1] (frontier K ∩ Ω) := by
  have hu : LocallyIntegrableOn (K.indicator (1 : E → ℝ)) Ω volume :=
    locallyIntegrableOn_indicator_const
      ((hK.nullMeasurableSet volume).mono Measure.restrict_le_self) 1
  have hfin (C : Set E) (hC : IsCompact C) (_ : C ⊆ Ω) :
      ∃ U : Opens E, C ⊆ (U : Set E) ∧ totalVariationOn volume U (K.indicator 1) ≠ ∞ :=
    hK.exists_opens_totalVariationOn_indicator_ne_top hC.isBounded
  rw [perimeter_eq_euclideanHausdorffMeasure_reducedBoundary hn hu hfin,
    ← measure_congr (essentialBoundary_inter_ae_eq_reducedBoundary hn hu hfin),
    hK.essentialBoundary_eq_frontier hKi]

/-- **The perimeter of a convex set is the Hausdorff measure of its frontier.** In dimension
`n ≥ 2`, a convex set `K` with nonempty interior has `P(K) = Hⁿ⁻¹(frontier K)`: its surface area,
defined as its perimeter, is the Hausdorff area of its boundary. No boundedness of `K` is needed;
for unbounded `K` both sides may be infinite. -/
theorem perimeter_eq_euclideanHausdorffMeasure_frontier (hn : 2 ≤ finrank ℝ E) (hK : Convex ℝ K)
    (hKi : (interior K).Nonempty) :
    perimeter volume ⊤ K = μHE[finrank ℝ E - 1] (frontier K) := by
  simpa using hK.perimeter_eq_euclideanHausdorffMeasure_frontier_inter hn hKi ⊤

/-- **The outer parallel volume of a convex body has the boundary area as right derivative.** In
dimension `n ≥ 2`, for a compact convex set `K` with nonempty interior, the volume of the outer
parallel body `K + t • closedBall 0 1` has right derivative `Hⁿ⁻¹(frontier K)` at `t = 0`. -/
theorem hasDerivWithinAt_volume_real_add_smul_closedBall_euclideanHausdorffMeasure_frontier
    (hn : 2 ≤ finrank ℝ E) (hKc : Convex ℝ K) (hK : IsCompact K) (hKi : (interior K).Nonempty) :
    HasDerivWithinAt (fun t : ℝ => volume.real (K + t • closedBall (0 : E) 1))
      (μHE[finrank ℝ E - 1] (frontier K)).toReal (Ici 0) 0 := by
  rw [← hKc.perimeter_eq_euclideanHausdorffMeasure_frontier hn hKi]
  exact hKc.hasDerivWithinAt_measureReal_add_smul_closedBall hK hKi

end Convex
