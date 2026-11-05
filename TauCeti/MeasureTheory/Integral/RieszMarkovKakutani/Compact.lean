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
Riesz–Markov–Kakutani theorem (`RealRMK.integral_rieszMeasure`) applies directly to linear
functionals on `C(X, ℝ)`. This file states it for a linear functional `L` on `C(X, ℝ)`
that is *nonpositive* on nonnegative functions, the sign in which such a functional arises from a
Hahn–Banach separation: `-L` is integration against a regular measure. If moreover `L 1 < 0`,
normalizing that measure gives a regular probability measure `ν` with `L h / L 1 = ∫ h dν`.

## Main results

* `LinearMap.exists_regular_integral_eq_neg`: `-L` is integration against a regular
  measure.
* `LinearMap.exists_isProbabilityMeasure_integral_eq_div`: if moreover `L 1 < 0`, then
  `L h / L 1 = ∫ h dν` for a regular probability measure `ν`.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace LinearMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

/-- **Riesz–Markov–Kakutani** for a linear functional `L` on `C(X, ℝ)`, `X` compact
Hausdorff, that is nonpositive on nonnegative functions: `-L` is integration against a regular
measure. -/
theorem exists_regular_integral_eq_neg (L : C(X, ℝ) →ₗ[ℝ] ℝ) (hL : ∀ h, 0 ≤ h → L h ≤ 0) :
    ∃ μ : Measure X, μ.Regular ∧ ∀ h : C(X, ℝ), ∫ x, h x ∂μ = -L h := by
  -- The positive functional `-L`, on compactly supported (here: all) continuous functions.
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀
    { toFun h := -L h.toContinuousMap
      -- `toContinuousMap` commutes with addition and scalar multiplication by definition.
      map_add' h₁ h₂ := by rw [← neg_add, ← map_add]; rfl
      map_smul' c h := by
        rw [RingHom.id_apply, smul_eq_mul, mul_neg, ← smul_eq_mul, ← map_smul]; rfl }
    fun h hh ↦ neg_nonneg.2 (hL _ fun f ↦ hh f)
  exact ⟨RealRMK.rieszMeasure Λ, inferInstance, fun h ↦
    RealRMK.integral_rieszMeasure Λ (CompactlySupportedContinuousMap.continuousMapEquiv h)⟩

/-- A linear functional `L` on `C(X, ℝ)`, `X` compact Hausdorff, that is negative at
`1` and nonpositive on nonnegative functions is `h ↦ L 1 * ∫ h dν` for a regular probability
measure `ν`. -/
theorem exists_isProbabilityMeasure_integral_eq_div (L : C(X, ℝ) →ₗ[ℝ] ℝ) (hL1 : L 1 < 0)
    (hL : ∀ h, 0 ≤ h → L h ≤ 0) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ ν.Regular ∧
      ∀ h : C(X, ℝ), ∫ x, h x ∂ν = L h / L 1 := by
  obtain ⟨μ, hreg, hμ⟩ := exists_regular_integral_eq_neg L hL
  have hμ1 : μ.real Set.univ = -L 1 := by simpa using hμ 1
  have hμ0 : μ Set.univ ≠ 0 := fun h0 ↦ by
    have : μ.real Set.univ = 0 := by simp [measureReal_def, h0]
    linarith
  have : NeZero μ := ⟨fun h ↦ hμ0 (by simp [h])⟩
  refine ⟨(μ Set.univ)⁻¹ • μ, inferInstance, Measure.Regular.smul (ENNReal.inv_ne_top.2 hμ0),
    fun h ↦ ?_⟩
  rw [integral_smul_measure, hμ, ENNReal.toReal_inv, ← measureReal_def, hμ1, smul_eq_mul,
    inv_mul_eq_div, neg_div_neg_eq]

end LinearMap
