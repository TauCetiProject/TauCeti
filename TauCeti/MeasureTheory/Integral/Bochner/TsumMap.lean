/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Commuting continuous linear maps with `tsum` of Bochner integrals

Given a countable family `g : J → X → E` of a.e. strongly measurable functions into a Banach space
`E` with `∑' j, ∫⁻ x, ‖g j x‖ₑ ∂μ ≠ ∞` and a continuous linear map `L : E →L[ℝ] F` into a Banach
space `F`, this file proves that `L (∑' j, ∫ x, g j x ∂μ) = ∫ x, ∑' j, L (g j x) ∂μ`.
Specializing `L` to a coordinate projection on `PiLp p E` yields the coordinatewise exchange
identity `(∑' j, ∫ x, g j x ∂μ) i = ∫ x, ∑' j, g j x i ∂μ`.

## Provenance

Extracted and generalized from `grh-lean`
(https://github.com/lsernau/grh-lean at commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC), file `src/New/Spanning/Unfolding/AmplitudeSums.lean`
(`tsum_integral_apply`).
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

/-- A continuous linear map `L : E →L[ℝ] F` commutes with the countable sum of Bochner integrals
of a family `g : J → X → E` satisfying `∑' j, ∫⁻ x, ‖g j x‖ₑ ∂μ ≠ ∞`. -/
theorem map_tsum_integral {X J E F : Type*} [MeasurableSpace X] {μ : Measure X} [Countable J]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) {g : J → X → E}
    (hg_meas : ∀ j, AEStronglyMeasurable (g j) μ)
    (hg_fin : ∑' j, ∫⁻ x, ‖g j x‖ₑ ∂μ ≠ ∞) :
    L (∑' j, ∫ x, g j x ∂μ) = ∫ x, ∑' j, L (g j x) ∂μ := by
  have h_int (j : J) : Integrable (g j) μ :=
    ⟨hg_meas j, lt_of_le_of_lt (le_tsum (fun j ↦ ∫⁻ x, ‖g j x‖ₑ ∂μ) j) hg_fin.lt_top⟩
  have h_summable : Summable fun j ↦ ∫ x, g j x ∂μ :=
    .of_eNorm (ne_of_lt (lt_of_le_of_lt
      (tsum_le_tsum fun j ↦ eNorm_integral_le_lintegral_eNorm (g j)) hg_fin.lt_top))
  have h_map_fin : ∑' j, ∫⁻ x, ‖L (g j x)‖ₑ ∂μ ≠ ∞ := by
    have hL : ‖L‖ₑ < ∞ := ENNReal.coe_lt_top
    refine ne_of_lt (lt_of_le_of_lt ?_ (ENNReal.mul_lt_top hL hg_fin.lt_top))
    rw [← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun j ↦ ?_
    rw [← lintegral_const_mul' ‖L‖ₑ (fun x ↦ ‖g j x‖ₑ) hL.ne]
    exact lintegral_mono fun x ↦ L.le_opENorm (g j x)
  calc
    L (∑' j, ∫ x, g j x ∂μ) = ∑' j, L (∫ x, g j x ∂μ) := L.map_tsum h_summable
    _ = ∑' j, ∫ x, L (g j x) ∂μ := tsum_congr fun j ↦ (L.integral_comp_comm (h_int j)).symm
    _ = ∫ x, ∑' j, L (g j x) ∂μ :=
      (integral_tsum (fun j ↦ L.continuous.comp_aestronglyMeasurable (hg_meas j)) h_map_fin).symm

/-- Coordinatewise exchange of a countable sum and a Bochner integral in `PiLp p E`. -/
theorem tsum_integral_piLp_apply {X J I : Type*} [MeasurableSpace X] {μ : Measure X} [Countable J]
    [Fintype I] {p : ℝ≥0∞} [Fact (1 ≤ p)] {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]
    {g : J → X → PiLp p E} (hg_meas : ∀ j, AEStronglyMeasurable (g j) μ)
    (hg_fin : ∑' j, ∫⁻ x, ‖g j x‖ₑ ∂μ ≠ ∞) (i : I) :
    (∑' j, ∫ x, g j x ∂μ) i = ∫ x, ∑' j, g j x i ∂μ :=
  map_tsum_integral (PiLp.proj (𝕜 := ℝ) p E i) hg_meas hg_fin

end TauCeti
