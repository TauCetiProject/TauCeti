/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Polarization
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# The sharp variation estimate for polarized spectral measures

For the complex measure `P.polarizedComplexMeasure ψ ξ` associated with a normalized
projection-valued measure, we prove

`(P.polarizedComplexMeasure ψ ξ).variation univ ≤ ofReal (‖ψ‖ * ‖ξ‖)`.

This sharp bound makes the polarized complex measure a finite-variation measure, with
its total variation controlled by the product of the norms of the two vectors. It gives
uniform norm control for integration against polarized spectral measures: integrating
a bounded measurable function is bounded in absolute value by its supremum norm times
`‖ψ‖ * ‖ξ‖`.

On the diagonal, the variation of `P.polarizedComplexMeasure ξ ξ` is exactly `P.diag ξ`, and in
general the variation is symmetric in the two vectors (`variation_polarizedComplexMeasure_comm`)
and absolutely continuous with respect to both `P.diag ξ` and `P.diag ψ`
(`variation_polarizedComplexMeasure_absolutelyContinuous_diag`,
`variation_polarizedComplexMeasure_absolutelyContinuous_diag_left`).

For every set `B` (not necessarily measurable), the local Cauchy–Schwarz variation estimate
`(P.polarizedComplexMeasure ψ ξ).variation B ≤ (P.diag ψ B) ^ (1 / 2) * (P.diag ξ B) ^ (1 / 2)`
holds (`polarizedComplexMeasure_variation_apply_le`), and summing over simple functions yields the
variation Cauchy–Schwarz inequalities `lintegral_variation_polarizedComplexMeasure_le` and
`lintegral_variation_polarizedComplexMeasure_le_left` for every `g : X → ℝ≥0∞`.

The finite-variation instance makes this property available to the vector-measure
integration API and subsequent spectral-integral estimates.

The underlying PVM and polarized-measure constructions are adapted from the
AIQ-Kitware DKPS formalization (Apache-2.0):
https://github.com/AIQ-Kitware/aiq-dkps-formalization.
-/

public section

open MeasureTheory
open scoped InnerProductSpace ENNReal NNReal

namespace TauCeti.ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The sharp variation bound for nonzero vectors. -/
private theorem polarizedComplexMeasure_variation_univ_le_of_ne_zero
    (P : ProjValMeasure X H) {ψ ξ : H} (hψz : ψ ≠ 0) (hξz : ξ ≠ 0) :
    (P.polarizedComplexMeasure ψ ξ).variation Set.univ ≤
      ENNReal.ofReal (‖ψ‖ * ‖ξ‖) := by
  have hψ : 0 < ‖ψ‖ := norm_pos_iff.mpr hψz
  have hξ : 0 < ‖ξ‖ := norm_pos_iff.mpr hξz
  let a : ℝ≥0 := ⟨‖ξ‖ / (2 * ‖ψ‖), by positivity⟩
  let b : ℝ≥0 := ⟨‖ψ‖ / (2 * ‖ξ‖), by positivity⟩
  have ha : (a : ℝ) = ‖ξ‖ / (2 * ‖ψ‖) := rfl
  have hb : (b : ℝ) = ‖ψ‖ / (2 * ‖ξ‖) := rfl
  let m : Measure X := a • P.diag ψ + b • P.diag ξ
  have hm (B : Set X) :
      m.real B = (a : ℝ) * (P.diag ψ).real B + (b : ℝ) * (P.diag ξ).real B := by
    simp only [m]
    rw [measureReal_add_apply, measureReal_nnreal_smul_apply, measureReal_nnreal_smul_apply]
  have hmajor : (P.polarizedComplexMeasure ψ ξ).variation ≤ m := by
    apply VectorMeasure.variation_le_of_forall_eNorm_le
    intro B hB
    have hbound : ‖P.polarizedComplexMeasure ψ ξ B‖ ≤ m.real B := by
      rw [hm B, ha, hb]
      exact P.norm_polarizedComplexMeasure_apply_le B hB
    simpa only [measureReal_def, ofReal_norm] using
      (ENNReal.ofReal_le_of_le_toReal hbound)
  have hmass : m.real Set.univ = ‖ψ‖ * ‖ξ‖ := by
    rw [hm Set.univ, P.diag_real_univ, P.diag_real_univ, ha, hb]
    field_simp [ne_of_gt hψ, ne_of_gt hξ]
    ring
  calc
    (P.polarizedComplexMeasure ψ ξ).variation Set.univ ≤ m Set.univ := hmajor Set.univ
    _ = ENNReal.ofReal (m.real Set.univ) :=
        (ofReal_measureReal (μ := m) (s := Set.univ)).symm
    _ = ENNReal.ofReal (‖ψ‖ * ‖ξ‖) := by rw [hmass]

/-- The variation of a polarized spectral measure has the sharp mass bound. -/
theorem polarizedComplexMeasure_variation_univ_le (P : ProjValMeasure X H) (ψ ξ : H) :
    (P.polarizedComplexMeasure ψ ξ).variation Set.univ ≤
      ENNReal.ofReal (‖ψ‖ * ‖ξ‖) := by
  by_cases hψz : ψ = 0
  · subst ψ
    rw [P.polarizedComplexMeasure_zero_left, VectorMeasure.variation_zero]
    simp
  by_cases hξz : ξ = 0
  · subst ξ
    rw [P.polarizedComplexMeasure_zero_right, VectorMeasure.variation_zero]
    simp
  exact P.polarizedComplexMeasure_variation_univ_le_of_ne_zero hψz hξz

/-- The variation of a polarized complex measure is finite. -/
instance instIsFiniteMeasurePolarizedVariation (P : ProjValMeasure X H) (ψ ξ : H) :
    IsFiniteMeasure (P.polarizedComplexMeasure ψ ξ).variation := by
  refine ⟨?_⟩
  exact (P.polarizedComplexMeasure_variation_univ_le ψ ξ).trans_lt
    ENNReal.ofReal_lt_top

/-- Swapping the two vectors conjugates the polarized complex measure and therefore leaves its
variation unchanged. -/
theorem variation_polarizedComplexMeasure_comm (P : ProjValMeasure X H) (ψ ξ : H) :
    (P.polarizedComplexMeasure ψ ξ).variation = (P.polarizedComplexMeasure ξ ψ).variation := by
  have hle (u v : H) :
      (P.polarizedComplexMeasure u v).variation ≤ (P.polarizedComplexMeasure v u).variation := by
    rw [← P.mapRangeL_conjCLE_polarizedComplexMeasure v u]
    simpa [Complex.conjCLE_nnNorm] using
      VectorMeasure.variation_mapRangeL_le (Complex.conjCLE : ℂ →L[ℝ] ℂ)
        (P.polarizedComplexMeasure v u)
  exact le_antisymm (hle ψ ξ) (hle ξ ψ)

/-- The variation of `P.polarizedComplexMeasure ψ ξ` is absolutely continuous with respect to the
diagonal measure `P.diag ξ`. -/
theorem variation_polarizedComplexMeasure_absolutelyContinuous_diag (P : ProjValMeasure X H)
    (ψ ξ : H) :
    (P.polarizedComplexMeasure ψ ξ).variation ≪ P.diag ξ := by
  refine Measure.AbsolutelyContinuous.mk fun B hB h0 => ?_
  have hproj : P.proj B hB ξ = 0 :=
    eNorm_eq_zero.1 (sq_eq_zero_iff.1 ((P.enorm_sq_proj_apply B hB ξ).trans h0))
  have hres : (P.polarizedComplexMeasure ψ ξ).restrict B = 0 := by
    rw [← P.polarizedComplexMeasure_proj_right B hB ψ ξ, hproj,
      P.polarizedComplexMeasure_zero_right]
  have hvar := congrArg (fun ν => ν.variation Set.univ) hres
  simpa [VectorMeasure.variation_restrict hB, Measure.restrict_apply_univ] using hvar

/-- The variation of `P.polarizedComplexMeasure ψ ξ` is absolutely continuous with respect to the
diagonal measure `P.diag ψ`. -/
theorem variation_polarizedComplexMeasure_absolutelyContinuous_diag_left (P : ProjValMeasure X H)
    (ψ ξ : H) :
    (P.polarizedComplexMeasure ψ ξ).variation ≪ P.diag ψ := by
  rw [P.variation_polarizedComplexMeasure_comm ψ ξ]
  exact P.variation_polarizedComplexMeasure_absolutelyContinuous_diag ξ ψ

/-- The variation of the diagonal polarized measure is the diagonal measure. -/
@[simp]
theorem variation_polarizedComplexMeasure_self (P : ProjValMeasure X H) (ξ : H) :
    (P.polarizedComplexMeasure ξ ξ).variation = P.diag ξ := by
  rw [polarizedComplexMeasure_self_eq_withDensityᵥ,
    Measure.variation_withDensityᵥ (integrable_const _)]
  simp

/-- Local variation bound on a measurable set: `|μ_(ψ,ξ)|(B) ≤ ‖P(B) ψ‖ₑ * ‖P(B) ξ‖ₑ`. -/
theorem polarizedComplexMeasure_variation_apply_le_enorm (P : ProjValMeasure X H) (ψ ξ : H)
    (B : Set X) (hB : MeasurableSet B) :
    (P.polarizedComplexMeasure ψ ξ).variation B ≤
      ‖P.proj B hB ψ‖ₑ * ‖P.proj B hB ξ‖ₑ := by
  calc (P.polarizedComplexMeasure ψ ξ).variation B
      = ((P.polarizedComplexMeasure ψ ξ).variation.restrict B) Set.univ := by
        rw [Measure.restrict_apply_univ]
    _ = ((P.polarizedComplexMeasure ψ ξ).restrict B).variation Set.univ := by
        rw [VectorMeasure.variation_restrict hB]
    _ = (P.polarizedComplexMeasure (P.proj B hB ψ) (P.proj B hB ξ)).variation Set.univ := by
        simp
    _ ≤ ENNReal.ofReal (‖P.proj B hB ψ‖ * ‖P.proj B hB ξ‖) :=
        P.polarizedComplexMeasure_variation_univ_le _ _
    _ = ‖P.proj B hB ψ‖ₑ * ‖P.proj B hB ξ‖ₑ := by
        rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]

/-- Local variation bound on any set `B` (not necessarily measurable):
`|μ_(ψ,ξ)|(B) ≤ (P.diag ψ B) ^ (1 / 2) * (P.diag ξ B) ^ (1 / 2)`. -/
theorem polarizedComplexMeasure_variation_apply_le (P : ProjValMeasure X H) (ψ ξ : H)
    (B : Set X) :
    (P.polarizedComplexMeasure ψ ξ).variation B ≤
      (P.diag ψ B) ^ (1 / 2 : ℝ) * (P.diag ξ B) ^ (1 / 2 : ℝ) := by
  let E := toMeasurable (P.diag ψ) B ∩ toMeasurable (P.diag ξ) B
  have hE : MeasurableSet E :=
    (measurableSet_toMeasurable _ _).inter (measurableSet_toMeasurable _ _)
  have hBE : B ⊆ E := Set.subset_inter (subset_toMeasurable _ _) (subset_toMeasurable _ _)
  have hdiag (v : H) : ‖P.proj E hE v‖ₑ = (P.diag v E) ^ (1 / 2 : ℝ) := by
    rw [← P.enorm_sq_proj_apply E hE v, ENNReal.sq_rpow_one_half]
  have hψE : P.diag ψ E ≤ P.diag ψ B :=
    (measure_mono Set.inter_subset_left).trans_eq (measure_toMeasurable B)
  have hξE : P.diag ξ E ≤ P.diag ξ B :=
    (measure_mono Set.inter_subset_right).trans_eq (measure_toMeasurable B)
  calc (P.polarizedComplexMeasure ψ ξ).variation B
      ≤ (P.polarizedComplexMeasure ψ ξ).variation E := measure_mono hBE
    _ ≤ ‖P.proj E hE ψ‖ₑ * ‖P.proj E hE ξ‖ₑ :=
        P.polarizedComplexMeasure_variation_apply_le_enorm ψ ξ E hE
    _ = (P.diag ψ E) ^ (1 / 2 : ℝ) * (P.diag ξ E) ^ (1 / 2 : ℝ) := by
        rw [hdiag ψ, hdiag ξ]
    _ ≤ (P.diag ψ B) ^ (1 / 2 : ℝ) * (P.diag ξ B) ^ (1 / 2 : ℝ) := by
        gcongr

/-- Simple-function Cauchy–Schwarz inequality for the variation of a polarized spectral measure. -/
private theorem simpleFunc_lintegral_variation_le (P : ProjValMeasure X H) (ψ ξ : H)
    (s : SimpleFunc X ℝ≥0∞) :
    s.lintegral (P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ₑ * (∫⁻ t, s t ^ 2 ∂(P.diag ξ)) ^ (1 / 2 : ℝ) := by
  have hhalf_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
    rw [one_div, ENNReal.rpow_inv_rpow two_ne_zero]
  have hψ : (∑ c ∈ s.range, P.diag ψ (s ⁻¹' {c})) ^ (1 / 2 : ℝ) = ‖ψ‖ₑ := by
    rw [s.sum_range_measure_preimage_singleton, P.diag_univ, ENNReal.sq_rpow_one_half]
  have hξ : ∑ c ∈ s.range, c ^ 2 * P.diag ξ (s ⁻¹' {c}) = ∫⁻ t, s t ^ 2 ∂(P.diag ξ) := by
    rw [← SimpleFunc.map_lintegral (fun c => c ^ 2) s,
      ← (s.map (fun c => c ^ 2)).lintegral_eq_lintegral]
    simp only [SimpleFunc.coe_map, Function.comp_apply]
  calc s.lintegral (P.polarizedComplexMeasure ψ ξ).variation
      = ∑ c ∈ s.range, c * (P.polarizedComplexMeasure ψ ξ).variation (s ⁻¹' {c}) := by
        rw [SimpleFunc.lintegral]
    _ ≤ ∑ c ∈ s.range, (P.diag ψ (s ⁻¹' {c})) ^ (1 / 2 : ℝ) *
          (c * (P.diag ξ (s ⁻¹' {c})) ^ (1 / 2 : ℝ)) := by
        refine Finset.sum_le_sum fun c _ => ?_
        calc c * (P.polarizedComplexMeasure ψ ξ).variation (s ⁻¹' {c})
            ≤ c * ((P.diag ψ (s ⁻¹' {c})) ^ (1 / 2 : ℝ) *
                (P.diag ξ (s ⁻¹' {c})) ^ (1 / 2 : ℝ)) :=
              mul_le_mul_right (P.polarizedComplexMeasure_variation_apply_le ψ ξ _) _
          _ = (P.diag ψ (s ⁻¹' {c})) ^ (1 / 2 : ℝ) *
                (c * (P.diag ξ (s ⁻¹' {c})) ^ (1 / 2 : ℝ)) := by ring
    _ ≤ (∑ c ∈ s.range, ((P.diag ψ (s ⁻¹' {c})) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∑ c ∈ s.range, (c * (P.diag ξ (s ⁻¹' {c})) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.inner_le_Lp_mul_Lq s.range _ _ (Real.HolderConjugate.two_two)
    _ = ‖ψ‖ₑ * (∫⁻ t, s t ^ 2 ∂(P.diag ξ)) ^ (1 / 2 : ℝ) := by
        rw [← hψ, ← hξ]
        congr 2 <;> refine Finset.sum_congr rfl fun c _ => ?_
        · exact hhalf_sq _
        · rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.rpow_two, hhalf_sq]

/-- **Cauchy–Schwarz inequality for the variation of a polarized spectral measure** (in the right
vector): for every `g : X → ℝ≥0∞` (with no measurability hypothesis),
`∫⁻ t, g t ∂|μ_(ψ,ξ)| ≤ ‖ψ‖ₑ * (∫⁻ t, g t ^ 2 ∂(P.diag ξ)) ^ (1 / 2)`. -/
theorem lintegral_variation_polarizedComplexMeasure_le (P : ProjValMeasure X H) (ψ ξ : H)
    (g : X → ℝ≥0∞) :
    ∫⁻ t, g t ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ₑ * (∫⁻ t, g t ^ 2 ∂(P.diag ξ)) ^ (1 / 2 : ℝ) := by
  rw [lintegral_def]
  refine iSup₂_le fun s hs => (P.simpleFunc_lintegral_variation_le ψ ξ s).trans ?_
  gcongr with t
  exact hs t

/-- **Cauchy–Schwarz inequality for the variation of a polarized spectral measure** (in the left
vector): for every `g : X → ℝ≥0∞`,
`∫⁻ t, g t ∂|μ_(ψ,ξ)| ≤ (∫⁻ t, g t ^ 2 ∂(P.diag ψ)) ^ (1 / 2) * ‖ξ‖ₑ`. -/
theorem lintegral_variation_polarizedComplexMeasure_le_left (P : ProjValMeasure X H) (ψ ξ : H)
    (g : X → ℝ≥0∞) :
    ∫⁻ t, g t ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      (∫⁻ t, g t ^ 2 ∂(P.diag ψ)) ^ (1 / 2 : ℝ) * ‖ξ‖ₑ := by
  rw [P.variation_polarizedComplexMeasure_comm, mul_comm]
  exact P.lintegral_variation_polarizedComplexMeasure_le ξ ψ g

end TauCeti.ProjValMeasure
