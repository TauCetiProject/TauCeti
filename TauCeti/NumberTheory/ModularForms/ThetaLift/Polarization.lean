/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.NumberTheory.NumberField.IntegralSqrt

/-!
# The polarization parameter from an imaginary quadratic subfield

For a square root `δ` of `-d` in an imaginary quadratic subfield, the polarization parameter is
`j = -δ⁻¹`. At embeddings extending the base embedding with `Im δ > 0` its value is `i/√d`.
It is anti-invariant under complex conjugation, and `(1 - j⁻¹)/2` is the trace-one half-generator,
which is integral when `d ≡ 3 (mod 4)`. These are the archimedean sign and integrality conditions
on the polarization parameter of the Weil representation.

The normalization follows `New.Parameters.phi_weilData_j` and
`New.Parameters.traceOne_eq_betaKInE` in `New/Derivatives/Field/WeilData.lean` of lsernau/grh-lean
(commit `72fead102f663d5c7a407964a13dc0cf9d977207`).
-/

public section

open Complex

namespace TauCeti

/-- The polarization parameter attached to a chosen imaginary quadratic generator `δ`. -/
noncomputable def quadraticWeilParameter {K : Type*} [Field K] (δ : K) : K := -δ⁻¹

/-- The polarization parameter is the negative reciprocal of its generator. -/
theorem quadraticWeilParameter_def {K : Type*} [Field K] (δ : K) :
    quadraticWeilParameter δ = -δ⁻¹ := (rfl)

/-- The polarization parameter vanishes exactly when the chosen generator does. -/
@[simp] theorem quadraticWeilParameter_eq_zero_iff {K : Type*} [Field K] (δ : K) :
    quadraticWeilParameter δ = 0 ↔ δ = 0 := by simp [quadraticWeilParameter_def]

/-- The half-generator is recovered by taking the inverse of the polarization parameter. -/
theorem one_sub_inv_quadraticWeilParameter_div_two {K : Type*} [Field K] (δ : K) :
    (1 - (quadraticWeilParameter δ)⁻¹) / 2 = (1 + δ) / 2 := by
  simp [quadraticWeilParameter_def, sub_neg_eq_add]

/-- For `δ² = -d` with `d ≡ 3 (mod 4)`, the half-generator recovered from the
polarization parameter is an algebraic integer. -/
theorem isIntegral_one_sub_inv_quadraticWeilParameter_div_two {K : Type*} [Field K] [CharZero K]
    {δ : K} {d : ℕ} (hδ : δ ^ 2 = -(d : K)) (hd : d % 4 = 3) :
    IsIntegral ℤ ((1 - (quadraticWeilParameter δ)⁻¹) / 2) := by
  rw [one_sub_inv_quadraticWeilParameter_div_two]
  apply isIntegral_one_add_div_two_of_sq_eq (d := -(d : ℤ)) (by simpa using hδ)
  omega

end TauCeti

namespace NumberField.IsCMField

open TauCeti

/-- The polarization parameter of a square root of a nonpositive integer is purely imaginary. -/
theorem complexConj_quadraticWeilParameter {K : Type*} [Field K] [CharZero K]
    [Algebra.IsIntegral ℚ K] [IsCMField K] {δ : K} {d : ℕ} (hδ : δ ^ 2 = -(d : K)) :
    complexConj K (quadraticWeilParameter δ) = -quadraticWeilParameter δ := by
  let σ : K →+* ℂ := Classical.arbitrary _
  have hsq : (σ δ) ^ 2 = -((d : ℝ) : ℂ) := by
    simpa using congrArg σ hδ
  have hconj : complexConj K δ = -δ := by
    apply σ.injective
    rw [complexEmbedding_complexConj, map_neg]
    exact Complex.conj_eq_neg_of_sq_eq_neg (Nat.cast_nonneg _) hsq
  simp [quadraticWeilParameter_def, hconj]

end NumberField.IsCMField

namespace NumberField.ComplexEmbedding.Extension

open TauCeti

/-- Every embedding extending the positively oriented base embedding sends the polarization
parameter to `i/√d`. In particular the value is independent of the extension. -/
theorem map_quadraticWeilParameter_algebraMap {K E : Type*} [Field K] [Field E] [Algebra K E]
    {σ : K →+* ℂ} (τ : ComplexEmbedding.Extension E σ) {δ : K} {d : ℕ}
    (hδ : δ ^ 2 = -(d : K)) (hσ : 0 < (σ δ).im) :
    τ.val (quadraticWeilParameter (algebraMap K E δ)) = I / (Real.sqrt d : ℂ) := by
  have hsq : (σ δ) ^ 2 = -((d : ℝ) : ℂ) := by
    simpa using congrArg σ hδ
  have hτ : τ.val (algebraMap K E δ) = σ δ := DFunLike.congr_fun τ.comp_eq δ
  simp [quadraticWeilParameter_def, hτ, eq_I_mul_ofReal_sqrt_of_sq_eq_neg hsq hσ,
    inv_I, div_eq_mul_inv, mul_comm]

end NumberField.ComplexEmbedding.Extension
