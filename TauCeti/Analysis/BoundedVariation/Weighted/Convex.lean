/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.ReducedBoundary
public import TauCeti.Analysis.BoundedVariation.Convex
import Mathlib.Analysis.Convex.Measure
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The weighted perimeter of a convex set

For a `C¹` weight `W` with measure `μ = e^{−W} · volume`, in dimension `n ≥ 2`, a convex set `C`
with nonempty interior, bounded or not, has weighted perimeter
`P_μ(C; Ω) = ∫_{∂C ∩ Ω} e^{−W} dHⁿ⁻¹ = μ^{n−1}(∂C ∩ Ω)` in every open set `Ω`
(`Convex.weightedPerimeter_eq_setLIntegral_frontier_inter`); in particular this holds for every
open convex set (`IsOpen.weightedPerimeter_eq_setLIntegral_frontier_inter_of_convex`), and for the
Gaussian perimeter (`Convex.gaussianPerimeter_eq_setLIntegral_frontier`).

The proof proceeds as follows: a convex set has locally finite Euclidean
perimeter (`Convex.exists_opens_totalVariationOn_indicator_ne_top`). The weighted perimeter is
then the weighted Hausdorff measure of the essential boundary
(`TauCeti.weightedPerimeter_eq_lintegral_essentialBoundary_inter`), and the essential boundary of
a convex set with nonempty interior is its frontier (`Convex.essentialBoundary_eq_frontier`).

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022).
* A. Cianchi, N. Fusco, F. Maggi, A. Pratelli, *On the isoperimetric deficit in Gauss space*,
  Amer. J. Math. (2011).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Module Metric
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {C : Set E}

/-- **The weighted perimeter of a convex set.** For a `C¹` weight `W`, in dimension `n ≥ 2`, a
convex set `C` with nonempty interior, bounded or not, has `P_μ(C; Ω) = ∫_{∂C ∩ Ω} e^{−W} dHⁿ⁻¹`
in every open set `Ω`. -/
theorem _root_.Convex.weightedPerimeter_eq_setLIntegral_frontier_inter (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (hC : Convex ℝ C) (hCi : (interior C).Nonempty) (Ω : Opens E) :
    weightedPerimeter W Ω C =
      ∫⁻ x in frontier C ∩ Ω, ENNReal.ofReal (Real.exp (-W x)) ∂μHE[finrank ℝ E - 1] := by
  have hu : LocallyIntegrableOn (C.indicator (1 : E → ℝ)) Ω volume :=
    locallyIntegrableOn_indicator_const
      ((hC.nullMeasurableSet (μ := volume)).mono Measure.restrict_le_self) 1
  rw [weightedPerimeter_eq_lintegral_essentialBoundary_inter hW hn hu
      fun _ hK _ => hC.exists_opens_totalVariationOn_indicator_ne_top hK.isBounded,
    hC.essentialBoundary_eq_frontier hCi]

/-- **The weighted perimeter of an open convex set.** For a `C¹` weight `W`, in dimension
`n ≥ 2`, every open convex set `C`, bounded or not and possibly empty, has
`P_μ(C; Ω) = ∫_{∂C ∩ Ω} e^{−W} dHⁿ⁻¹` in every open set `Ω`. -/
theorem _root_.IsOpen.weightedPerimeter_eq_setLIntegral_frontier_inter_of_convex
    (hW : ContDiff ℝ 1 W) (hn : 2 ≤ finrank ℝ E) (hCo : IsOpen C) (hC : Convex ℝ C)
    (Ω : Opens E) :
    weightedPerimeter W Ω C =
      ∫⁻ x in frontier C ∩ Ω, ENNReal.ofReal (Real.exp (-W x)) ∂μHE[finrank ℝ E - 1] := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp [weightedPerimeter_empty]
  · exact hC.weightedPerimeter_eq_setLIntegral_frontier_inter hW hn (by rwa [hCo.interior_eq]) Ω

/-- **The Gaussian perimeter of a convex set.** In dimension `n ≥ 2`, a convex set `C` with
nonempty interior, bounded or not, has Gaussian perimeter `P_γ(C) = ∫_{∂C} e^{−W} dHⁿ⁻¹` for the
Gaussian weight `W`, that is `γ^{n−1}(∂C)`. -/
theorem _root_.Convex.gaussianPerimeter_eq_setLIntegral_frontier (hn : 2 ≤ finrank ℝ E)
    (hC : Convex ℝ C) (hCi : (interior C).Nonempty) :
    gaussianPerimeter C =
      ∫⁻ x in frontier C, ENNReal.ofReal (Real.exp (-gaussianWeight E x))
        ∂μHE[finrank ℝ E - 1] := by
  rw [gaussianPerimeter_def,
    hC.weightedPerimeter_eq_setLIntegral_frontier_inter contDiff_gaussianWeight hn hCi ⊤]
  simp

end TauCeti
