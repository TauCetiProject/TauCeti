/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# The Riesz–Markov–Kakutani theorem on a compact space

On a compact Hausdorff space `X` every continuous function is compactly supported, so Mathlib's
Riesz–Markov–Kakutani theorem (`RealRMK.integral_rieszMeasure`), stated for positive linear
functionals on `C_c(X, ℝ)`, applies to a linear functional `L` on `C(X, ℝ)` that is nonnegative
on nonnegative functions: such an `L` is integration against a regular measure `μ`. When
`0 < L 1`, the measure `μ` is finite and nonzero, with `μ X = L 1`, so normalizing it gives a
regular probability measure `ν` with `∫ h dν = L h / L 1`.

## Main results

* `LinearMap.exists_regular_integral_eq`: a positive linear functional on `C(X, ℝ)`, `X` compact
  Hausdorff, is integration against a regular measure.
* `LinearMap.exists_isProbabilityMeasure_integral_eq_div`: if moreover `0 < L 1`, then
  `∫ h dν = L h / L 1` for a regular probability measure `ν`.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace LinearMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

/-- **Riesz–Markov–Kakutani** on a compact Hausdorff space: a linear functional on `C(X, ℝ)`
that is nonnegative on nonnegative functions is integration against a regular measure. -/
theorem exists_regular_integral_eq (L : C(X, ℝ) →ₗ[ℝ] ℝ) (hL : ∀ h, 0 ≤ h → 0 ≤ L h) :
    ∃ μ : Measure X, μ.Regular ∧ ∀ h : C(X, ℝ), ∫ x, h x ∂μ = L h := by
  -- `L` as a positive functional on compactly supported (here: all) continuous functions.
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀
    { toFun h := L h.toContinuousMap
      -- `toContinuousMap` commutes with addition and scalar multiplication by definition.
      map_add' h₁ h₂ := map_add L h₁.toContinuousMap h₂.toContinuousMap
      map_smul' c h := map_smul L c h.toContinuousMap }
    fun h hh ↦ hL _ fun x ↦ hh x
  exact ⟨RealRMK.rieszMeasure Λ, inferInstance, fun h ↦
    RealRMK.integral_rieszMeasure Λ (CompactlySupportedContinuousMap.continuousMapEquiv h)⟩

/-- On a compact Hausdorff space, a linear functional `L` on `C(X, ℝ)` that is positive at `1`
and nonnegative on nonnegative functions satisfies `∫ h dν = L h / L 1` for a regular
probability measure `ν`. -/
theorem exists_isProbabilityMeasure_integral_eq_div (L : C(X, ℝ) →ₗ[ℝ] ℝ) (hL1 : 0 < L 1)
    (hL : ∀ h, 0 ≤ h → 0 ≤ L h) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ ν.Regular ∧
      ∀ h : C(X, ℝ), ∫ x, h x ∂ν = L h / L 1 := by
  obtain ⟨μ, hreg, hμ⟩ := exists_regular_integral_eq L hL
  have hμ1 : μ.real Set.univ = L 1 := by simpa using hμ 1
  have hμ0 : μ Set.univ ≠ 0 := fun h0 ↦ by
    have : μ.real Set.univ = 0 := by simp [measureReal_def, h0]
    linarith
  have : NeZero μ := ⟨fun h ↦ hμ0 (by simp [h])⟩
  refine ⟨(μ Set.univ)⁻¹ • μ, inferInstance, Measure.Regular.smul (ENNReal.inv_ne_top.2 hμ0),
    fun h ↦ ?_⟩
  rw [integral_smul_measure, hμ, ENNReal.toReal_inv, ← measureReal_def, hμ1, smul_eq_mul,
    inv_mul_eq_div]

end LinearMap
