/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.VariationMeasure
public import TauCeti.Analysis.BoundedVariation.Coarea
public import TauCeti.MeasureTheory.Function.Coarea.Lipschitz
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Analysis.InnerProductSpace.NormDet

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

For `u` of locally finite Euclidean variation the identity also holds on every Borel subset `B`
of `Ω`, with the measure `e^{−W} |Du|` of `B` in place of the weighted variation:
`∫_B e^{−W} d|Du| = ∫_ℝ ∫_B e^{−W} d|D1_{u > t}| dt`
(`TauCeti.setLIntegral_exp_neg_variationMeasure_eq_lintegral_setLIntegral`). Only measurability
of the weight enters here.

For a locally Lipschitz `f : E → ℝ` and a measurable `g : E → [0, ∞]`, the weighted Lipschitz
coarea formula `∫ g ‖∇f‖ dμ = ∫_ℝ ∫_{f⁻¹(t)} g dμ^{n−1} dt` holds, where
`μ^{n−1} = e^{−W} · μHE[n − 1]`
(`TauCeti.lintegral_mul_enorm_fderiv_weightedMeasure_eq_lintegral_setLIntegral_preimage`), also
over every null-measurable set `s` in place of `E`
(`TauCeti.setLIntegral_mul_enorm_fderiv_weightedMeasure_eq_lintegral_setLIntegral_fiber`). It is
the coarea formula for
locally Lipschitz maps
(`LocallyLipschitz.lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber`) with
the weight `e^{−W} g`, the coarea Jacobian of a map to `ℝ` being the norm of its derivative
(`ContinuousLinearMap.normDet_adjoint_eq_norm`).

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

/-- **The weighted coarea formula on Borel subsets.** For a measurable weight `W`, `u` locally
integrable on the open set `Ω` with locally finite Euclidean variation there, and a measurable
subset `B` of `Ω`, `∫_B e^{−W} d|Du| = ∫_ℝ ∫_B e^{−W} d|D1_{u > t}| dt`. For `B = Ω` and a `C¹`
weight both sides are `V_μ(u; Ω)` and `∫_ℝ P_μ({u > t}; Ω) dt`
(`TauCeti.weightedVariation_eq_lintegral_weightedPerimeter`). -/
theorem setLIntegral_exp_neg_variationMeasure_eq_lintegral_setLIntegral (hW : Measurable W)
    (hu : LocallyIntegrableOn u Ω)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U u ≠ ∞)
    {B : Set Ω} (hB : MeasurableSet B) :
    ∫⁻ x in B, ENNReal.ofReal (Real.exp (-W x)) ∂variationMeasure volume Ω u =
      ∫⁻ t, ∫⁻ x in B, ENNReal.ofReal (Real.exp (-W x))
        ∂variationMeasure volume Ω ({x | t < u x}.indicator 1) := by
  have hρ : Measurable fun x : Ω => ENNReal.ofReal (Real.exp (-W x)) :=
    (hW.comp measurable_subtypeVal).neg.exp.ennreal_ofReal
  simp_rw [← lintegral_indicator hB]
  exact lintegral_variationMeasure_eq_lintegral_lintegral hu hfin (hρ.indicator hB).aemeasurable

section Lipschitz

variable {f : E → ℝ} {g : E → ℝ≥0∞} {s : Set E}

/-- **The weighted Lipschitz coarea formula on a set.** For a locally Lipschitz `f : E → ℝ`, a
null-measurable set `s`, a weight `W` and a `g : E → [0, ∞]`, both almost everywhere measurable
on `s`, `∫_s g ‖∇f‖ dμ = ∫_ℝ ∫_{s ∩ f⁻¹(t)} g dμ^{n−1} dt`, where `μ = e^{−W} · volume` and
`μ^{n−1} = e^{−W} · μHE[n − 1]`. -/
theorem setLIntegral_mul_enorm_fderiv_weightedMeasure_eq_lintegral_setLIntegral_fiber
    (hW : AEMeasurable W (volume.restrict s)) (hf : LocallyLipschitz f)
    (hs : NullMeasurableSet s) (hg : AEMeasurable g (volume.restrict s)) :
    ∫⁻ x in s, g x * ‖fderiv ℝ f x‖ₑ ∂weightedMeasure W =
      ∫⁻ t, ∫⁻ x in s ∩ f ⁻¹' {t}, ENNReal.ofReal (Real.exp (-W x)) * g x
        ∂μHE[Module.finrank ℝ E - 1] := by
  have hρ : AEMeasurable (fun x => ENNReal.ofReal (Real.exp (-W x))) (volume.restrict s) :=
    hW.neg.exp.ennreal_ofReal
  have hcoarea := hf.lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber hs
    (hρ.mul hg)
  simp only [Module.finrank_self, Pi.mul_apply] at hcoarea
  rw [← hcoarea, weightedMeasure_def, restrict_withDensity',
    lintegral_withDensity_eq_lintegral_mul₀ (g := fun x => g x * ‖fderiv ℝ f x‖ₑ) hρ
      (hg.mul (measurable_fderiv ℝ f).eNorm.aemeasurable)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, ContinuousLinearMap.normDet_adjoint_eq_norm, ofReal_norm]
  ring

/-- **The weighted Lipschitz coarea formula.** For an almost everywhere measurable weight `W`, a
locally Lipschitz `f : E → ℝ` and an almost everywhere measurable `g : E → [0, ∞]`,
`∫ g ‖∇f‖ dμ = ∫_ℝ ∫_{f⁻¹(t)} g dμ^{n−1} dt`, where `μ = e^{−W} · volume` and
`μ^{n−1} = e^{−W} · μHE[n − 1]`. -/
theorem lintegral_mul_enorm_fderiv_weightedMeasure_eq_lintegral_setLIntegral_preimage
    (hW : AEMeasurable W) (hf : LocallyLipschitz f) (hg : AEMeasurable g) :
    ∫⁻ x, g x * ‖fderiv ℝ f x‖ₑ ∂weightedMeasure W =
      ∫⁻ t, ∫⁻ x in f ⁻¹' {t}, ENNReal.ofReal (Real.exp (-W x)) * g x
        ∂μHE[Module.finrank ℝ E - 1] := by
  simpa using setLIntegral_mul_enorm_fderiv_weightedMeasure_eq_lintegral_setLIntegral_fiber
    hW.restrict hf MeasurableSet.univ.nullMeasurableSet hg.restrict

end Lipschitz

end TauCeti
