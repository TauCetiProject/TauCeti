/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Polarization
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.Analysis.Complex.OperatorNorm
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

end TauCeti.ProjValMeasure
