/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.VariationMeasure
public import TauCeti.Analysis.BoundedVariation.DeGiorgi
public import TauCeti.Analysis.BoundedVariation.EssentialBoundary
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The weighted perimeter as a weighted Hausdorff measure of the boundary

Let `W` be a `C¹` weight on a finite-dimensional real inner product space `E` of dimension
`n ≥ 2`, with measure `μ = e^{−W} · volume`, and let `U` be a set of locally finite perimeter in
an open set `Ω`. The weighted perimeter of `U` in `Ω` is the weighted `(n − 1)`-dimensional
Hausdorff measure of its reduced boundary, and of the part of its essential boundary in `Ω`:

`P_μ(U; Ω) = ∫_{∂*U} e^{−W} dHⁿ⁻¹ = ∫_{∂ᵉU ∩ Ω} e^{−W} dHⁿ⁻¹`

(`TauCeti.weightedPerimeter_eq_lintegral_reducedBoundary`,
`TauCeti.weightedPerimeter_eq_lintegral_essentialBoundary_inter`). A null-measurable set of
finite weighted perimeter in `Ω` has locally finite perimeter there
(`TauCeti.exists_totalVariationOn_indicator_ne_top_of_weightedPerimeter_ne_top`), so the
reduced-boundary formula holds for it
(`TauCeti.weightedPerimeter_eq_lintegral_reducedBoundary_of_ne_top`).

The proof combines `V_μ(u; Ω) = ∫_Ω e^{−W} d|Du|`
(`TauCeti.weightedVariation_eq_lintegral_variationMeasure`) with De Giorgi's theorem
`|Dχ_U| = Hⁿ⁻¹ ⌊ ∂*U` (`TauCeti.variationMeasure_eq_comap_restrict_reducedBoundary`) and the
comparison of the essential and reduced boundaries
(`TauCeti.essentialBoundary_inter_ae_eq_reducedBoundary`).

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022), Section 3.
* A. Cianchi, N. Fusco, F. Maggi, A. Pratelli, *On the isoperimetric deficit in Gauss space*,
  Amer. J. Math. (2011), equations (2.3)–(2.5).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Module
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {Ω : Opens E} {s : Set E}

/-- **The weighted perimeter is the weighted Hausdorff measure of the reduced boundary.** For a
`C¹` weight `W`, in dimension `n ≥ 2`, a set `s` of locally finite perimeter in `Ω` has
`P_μ(s; Ω) = ∫_{∂*s} e^{−W} dHⁿ⁻¹`. -/
theorem weightedPerimeter_eq_lintegral_reducedBoundary (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞) :
    weightedPerimeter W Ω s =
      ∫⁻ x in reducedBoundary volume Ω s, ENNReal.ofReal (Real.exp (-W x))
        ∂μHE[finrank ℝ E - 1] := by
  rw [weightedPerimeter_def, weightedVariation_eq_lintegral_variationMeasure hW hu hfin,
    variationMeasure_eq_comap_restrict_reducedBoundary hn]
  refine (lintegral_subtype_comap (s := (Ω : Set E)) Ω.isOpen.measurableSet
    fun x => ENNReal.ofReal (Real.exp (-W x))).trans ?_
  rw [Measure.restrict_restrict Ω.isOpen.measurableSet, inter_eq_right.2 reducedBoundary_subset]

/-- **The weighted perimeter is the weighted Hausdorff measure of the essential boundary.** For a
`C¹` weight `W`, in dimension `n ≥ 2`, a set `s` of locally finite perimeter in `Ω` has
`P_μ(s; Ω) = ∫_{∂ᵉs ∩ Ω} e^{−W} dHⁿ⁻¹`. -/
theorem weightedPerimeter_eq_lintegral_essentialBoundary_inter (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞) :
    weightedPerimeter W Ω s =
      ∫⁻ x in essentialBoundary volume s ∩ Ω, ENNReal.ofReal (Real.exp (-W x))
        ∂μHE[finrank ℝ E - 1] := by
  rw [weightedPerimeter_eq_lintegral_reducedBoundary hW hn hu hfin,
    setLIntegral_congr (essentialBoundary_inter_ae_eq_reducedBoundary hn hu hfin)]

/-- **Finite weighted perimeter gives locally finite perimeter.** For a `C¹` weight `W`, a
null-measurable set `s` of finite weighted perimeter in `Ω` has locally finite perimeter there:
every compact subset of `Ω` has an open neighbourhood on which the indicator of `s` has finite
Euclidean variation. -/
theorem exists_totalVariationOn_indicator_ne_top_of_weightedPerimeter_ne_top
    (hW : ContDiff ℝ 1 W) (hs : NullMeasurableSet s (volume.restrict Ω))
    (h : weightedPerimeter W Ω s ≠ ∞) :
    ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞ :=
  exists_totalVariationOn_ne_top_of_weightedVariation_ne_top hW
    (locallyIntegrableOn_indicator_const hs 1) (weightedPerimeter_def (W := W) ▸ h)

/-- For a `C¹` weight `W`, in dimension `n ≥ 2`, a null-measurable set `s` of finite weighted
perimeter in `Ω` has `P_μ(s; Ω) = ∫_{∂*s} e^{−W} dHⁿ⁻¹`. -/
theorem weightedPerimeter_eq_lintegral_reducedBoundary_of_ne_top (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (hs : NullMeasurableSet s (volume.restrict Ω))
    (h : weightedPerimeter W Ω s ≠ ∞) :
    weightedPerimeter W Ω s =
      ∫⁻ x in reducedBoundary volume Ω s, ENNReal.ofReal (Real.exp (-W x))
        ∂μHE[finrank ℝ E - 1] :=
  weightedPerimeter_eq_lintegral_reducedBoundary hW hn (locallyIntegrableOn_indicator_const hs 1)
    (exists_totalVariationOn_indicator_ne_top_of_weightedPerimeter_ne_top hW hs h)

end TauCeti
