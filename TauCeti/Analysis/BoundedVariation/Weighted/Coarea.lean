/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.VariationMeasure
public import TauCeti.Analysis.BoundedVariation.Coarea
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The weighted coarea formula

For a `C¹` weight `W` and a function `u` locally integrable on an open set `Ω`, the weighted
variation is the integral of the weighted perimeters of the superlevel sets,
`V_μ(u; Ω) = ∫_ℝ P_μ({u > t}; Ω) dt` in `[0, ∞]`
(`TauCeti.weightedVariation_eq_lintegral_weightedPerimeter`).

When `u` has locally finite Euclidean variation in `Ω`, both sides are integrals of `e^{−W}`:
the left one against `|Du|` (`TauCeti.weightedVariation_eq_lintegral_variationMeasure`), the
right one against `|D1_{u > t}|` for almost every `t`, and the Euclidean coarea formula
`TauCeti.lintegral_variationMeasure_eq_lintegral_lintegral` identifies them. Otherwise some
compact `K ⊆ Ω` has infinite variation on each of its neighbourhoods. The weighted variation is
then infinite (`TauCeti.exists_totalVariationOn_ne_top_of_weightedVariation_ne_top`), and so is
the right side: on a neighbourhood `U ≤ Ω` of `K` the weight is bounded below by some `m > 0`, so
`P_μ({u > t}; Ω) ≥ m P({u > t}; U)` (`TauCeti.exists_mul_totalVariationOn_le_weightedVariation`),
whose integral over `t` is `m |Du|(U) = ∞` by the Euclidean coarea formula
`TauCeti.totalVariationOn_eq_lintegral_perimeter`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press (2012), Sections 13.1 and 18.1.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {Ω : Opens E} {u : E → ℝ}

/-- The weighted coarea formula for functions of locally finite Euclidean variation. -/
private theorem weightedVariation_eq_lintegral_weightedPerimeter_of_locallyFinite
    (hW : ContDiff ℝ 1 W) (hu : LocallyIntegrableOn u Ω)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U u ≠ ∞) :
    weightedVariation W Ω u = ∫⁻ t, weightedPerimeter W Ω {x | t < u x} := by
  have hum : AEMeasurable u (volume.restrict Ω) := hu.aestronglyMeasurable.aemeasurable
  have hρ : Measurable fun x : Ω => ENNReal.ofReal (Real.exp (-W x)) :=
    (hW.continuous.comp continuous_subtypeVal).neg.rexp.measurable.ennreal_ofReal
  rw [weightedVariation_eq_lintegral_variationMeasure hW hu hfin,
    lintegral_variationMeasure_eq_lintegral_lintegral hu hfin hρ.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_exists_perimeter_setOf_lt_ne_top hu hfin] with t ht
  rw [weightedPerimeter_def]
  refine (weightedVariation_eq_lintegral_variationMeasure hW
    (locallyIntegrableOn_indicator_const (nullMeasurableSet_lt aemeasurable_const hum) 1)
    fun K hK hKΩ => ?_).symm
  obtain ⟨U, hKU, hU⟩ := ht K hK hKΩ
  exact ⟨U, hKU, by rw [perimeter_def] at hU; exact hU⟩

/-- Without locally finite Euclidean variation, the integral of the weighted perimeters of the
superlevel sets is infinite. -/
private theorem lintegral_weightedPerimeter_eq_top (hW : ContDiff ℝ 1 W)
    (hu : LocallyIntegrableOn u Ω)
    (hfin : ¬ ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U u ≠ ∞) :
    ∫⁻ t, weightedPerimeter W Ω {x | t < u x} = ∞ := by
  simp only [not_forall, not_exists, not_and, ne_eq, not_not] at hfin
  obtain ⟨K, hK, hKΩ, hinf⟩ := hfin
  obtain ⟨U, hKU, hUΩ, m, hm0, hm⟩ := exists_mul_totalVariationOn_le_weightedVariation hW hK hKΩ
  have hum : AEMeasurable u (volume.restrict Ω) := hu.aestronglyMeasurable.aemeasurable
  have hle : (m : ℝ≥0∞) * totalVariationOn volume U u ≤
      ∫⁻ t, weightedPerimeter W Ω {x | t < u x} := by
    rw [totalVariationOn_eq_lintegral_perimeter (hu.mono_set hUΩ),
      ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    refine lintegral_mono fun t => ?_
    rw [perimeter_def, weightedPerimeter_def]
    exact hm _ (locallyIntegrableOn_indicator_const (nullMeasurableSet_lt aemeasurable_const hum) 1)
  rw [hinf U hKU, ENNReal.mul_top (ENNReal.coe_ne_zero.2 hm0)] at hle
  exact top_le_iff.1 hle

/-- **The weighted coarea formula.** For a `C¹` weight `W` and `u` locally integrable on the open
set `Ω`, the weighted variation of `u` is the integral of the weighted perimeters of its
superlevel sets: `V_μ(u; Ω) = ∫_ℝ P_μ({u > t}; Ω) dt` in `[0, ∞]`. -/
theorem weightedVariation_eq_lintegral_weightedPerimeter (hW : ContDiff ℝ 1 W)
    (hu : LocallyIntegrableOn u Ω) :
    weightedVariation W Ω u = ∫⁻ t, weightedPerimeter W Ω {x | t < u x} := by
  by_cases hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U u ≠ ∞
  · exact weightedVariation_eq_lintegral_weightedPerimeter_of_locallyFinite hW hu hfin
  · rw [lintegral_weightedPerimeter_eq_top hW hu hfin]
    by_contra h
    exact hfin (exists_totalVariationOn_ne_top_of_weightedVariation_ne_top hW hu h)

end TauCeti
