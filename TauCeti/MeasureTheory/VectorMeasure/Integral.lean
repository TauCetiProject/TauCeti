/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.SetToL1.ChangeMeasure
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import TauCeti.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Naturality and homogeneity of the vector-measure integral

The integral `∫ᵛ x, f x ∂[B; μ]` of Mathlib is natural in the measure: a continuous linear map `φ`
applied to the values of `μ` corresponds to a continuous linear map applied to the integral,
whenever the pairings are compatible (`map_integral_comp_eq_integral_mapRangeL`). As consequences,
the integral is homogeneous for scalars acting on the integrand or on the measure, whenever the
pairing is linear over those scalars.

## Main declarations

* `MeasureTheory.VectorMeasure.map_integral_comp_eq_integral_mapRangeL`: naturality of the
  vector-measure integral under continuous linear maps of the values.
* `MeasureTheory.VectorMeasure.integral_fun_smul_of_smul_left` and
  `MeasureTheory.VectorMeasure.integral_smul_vectorMeasure_of_smul_right`: homogeneity in the
  integrand and in the measure.
-/

public section

open MeasureTheory ContinuousLinearMap
open scoped ENNReal NNReal

namespace MeasureTheory.VectorMeasure

variable {X E₀ E F F' G G' 𝕜 : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup G'] [NormedSpace ℝ G']

/-- **Naturality of the vector-measure integral.** Let `ψ`, `φ` and `L` be continuous linear maps
on the integrand, on the values of the measure and on the values of the integral, compatible with
the pairings `B` and `B'` in the sense that `L (B (ψ x) y) = B' x (φ y)`. Then for `f` integrable
against `μ`, applying `L` to the integral of `ψ ∘ f` against `μ` gives the integral of `f` against
the measure `φ ∘ μ`. -/
theorem map_integral_comp_eq_integral_mapRangeL [CompleteSpace G] [CompleteSpace G']
    (μ : VectorMeasure X F) {f : X → E₀} (hf : μ.Integrable f) (ψ : E₀ →L[ℝ] E)
    (φ : F →L[ℝ] F') (L : G →L[ℝ] G') {B : E →L[ℝ] F →L[ℝ] G} {B' : E₀ →L[ℝ] F' →L[ℝ] G'}
    (h : ∀ x y, L (B (ψ x) y) = B' x (φ y)) :
    L (∫ᵛ x, ψ (f x) ∂[B; μ]) = ∫ᵛ x, f x ∂[B'; mapRangeL φ μ] := by
  have hvar := variation_mapRangeL_le φ μ
  rw [ENNReal.smul_def] at hvar
  -- Both sides are `setToFun` of the same set function, against comparable reference measures.
  have hT : μ.transpose (compL ℝ F G G' L ∘L (B ∘L ψ)) = (mapRangeL φ μ).transpose B' := by
    ext s x
    simp [transpose_eq_cbmApplyMeasure, h]
  rw [integral_continuousLinearMap_comp hf, continuousLinearMap_apply_integral hf,
    integral_eq_setToFun, integral_eq_setToFun,
    setToFun_congr_measure_of_integrable _ ENNReal.coe_ne_top hvar _
      (hT ▸ dominatedFinMeasAdditive_cbmApplyMeasure (mapRangeL φ μ) B') f hf]
  exact setToFun_congr_left _ _ (congrArg _ hT) f

/-- The vector-measure integral is homogeneous for scalars of a normed division ring `𝕜` acting
on the integrand, when the pairing is `𝕜`-linear in its first argument. -/
theorem integral_fun_smul_of_smul_left [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    [Module 𝕜 G] [NormSMulClass 𝕜 G] {μ : VectorMeasure X F} {B : E →L[ℝ] F →L[ℝ] G}
    (hB : ∀ (c : 𝕜) x y, B (c • x) y = c • B x y) (c : 𝕜) (f : X → E) :
    ∫ᵛ x, c • f x ∂[B; μ] = c • ∫ᵛ x, f x ∂[B; μ] := by
  simp only [integral_eq_setToFun]
  exact setToFun_smul _ (fun c s x => by simp [transpose_eq_cbmApplyMeasure, hB]) c f

/-- The vector-measure integral is homogeneous for scalars of a normed field `𝕜` acting on the
measure, when the pairing is `𝕜`-linear in its second argument.

This generalizes Mathlib's `MeasureTheory.VectorMeasure.integral_smul_vectorMeasure` (real
scalars). -/
theorem integral_smul_vectorMeasure_of_smul_right [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] [NormedSpace 𝕜 G] [IsScalarTower ℝ 𝕜 G]
    {μ : VectorMeasure X F} {B : E →L[ℝ] F →L[ℝ] G}
    (hB : ∀ (c : 𝕜) x y, B x (c • y) = c • B x y) (c : 𝕜) (f : X → E) :
    ∫ᵛ x, f x ∂[B; c • μ] = c • ∫ᵛ x, f x ∂[B; μ] := by
  -- The case split on completeness of `G` and the comparison of variations through
  -- `variation_smul` in the non-integrable branch are adapted from the proof of Mathlib's
  -- `MeasureTheory.VectorMeasure.integral_smul_vectorMeasure`; the integrable branch uses
  -- `map_integral_comp_eq_integral_mapRangeL` instead.
  by_cases hG : CompleteSpace G; swap
  · simp [integral_of_not_completeSpace hG]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  by_cases hf : μ.Integrable f
  · have hμ : c • μ = mapRangeL (lsmul ℝ 𝕜 c) μ := by
      ext s
      simp
    have := map_integral_comp_eq_integral_mapRangeL μ hf (ContinuousLinearMap.id ℝ E)
      (lsmul ℝ 𝕜 c) (lsmul ℝ 𝕜 c) (B := B) (B' := B) (fun x y => by simp [hB])
    simpa [← hμ] using this.symm
  · have hf' : ¬(c • μ).Integrable f := by
      rwa [VectorMeasure.Integrable, variation_smul, ENNReal.smul_def,
        integrable_smul_measure (by simpa using hc) ENNReal.coe_ne_top]
    rw [integral_undef hf, integral_undef hf', smul_zero]

end MeasureTheory.VectorMeasure
