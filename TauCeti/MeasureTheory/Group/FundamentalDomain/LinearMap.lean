/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Unfolding Bochner integrals over an additive fundamental domain

Let D be a fundamental domain for the translation action of a countable additive subgroup Γ
on a measure space (A, μ) with a Γ-invariant measure. Suppose a function P : A → Y satisfies
P (e i +ᵥ z) = T i (F z) for an enumeration e : I ≃ Γ, a function F : A → X integrable on
D, and continuous linear maps T i : X →L[ℝ] Y whose operator norms are summable. Then P is
integrable on A and its Bochner integral unfolds as the unconditionally convergent series
∑' i, T i (∫ z in D, F z ∂μ).

## Main statements

* TauCeti.integrable_of_isAddFundamentalDomain_clm: P is integrable on A.
* TauCeti.hasSum_integral_of_isAddFundamentalDomain_clm: the series
  i ↦ T i (∫ z in D, F z ∂μ) has sum ∫ z, P z ∂μ.
* TauCeti.integral_eq_tsum_of_isAddFundamentalDomain_clm: ∫ z, P z ∂μ equals
  ∑' i, T i (∫ z in D, F z ∂μ).

## Provenance

Adapted from New.integrable_and_integral_eq_tsum_of_fundamentalDomain in
grh/src/Lib/SiegelWeil/OneVector/SiegelClassSum.lean of grh-lean
(<https://github.com/lsernau/grh-lean>, commit 72fead102f663d5c7a407964a13dc0cf9d977207),
generalized from ℂ-linear functionals to real continuous linear maps between normed spaces.
-/

@[expose] public section

open MeasureTheory

namespace TauCeti

variable {A X Y I : Type*} [AddCommGroup A] [MeasurableSpace A] {μ : Measure A}
  {Γ : AddSubgroup A} [Countable Γ] [MeasurableConstVAdd Γ A] [VAddInvariantMeasure Γ A μ]
  {D : Set A} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- If P (e i +ᵥ z) = T i (F z) on translates of an additive fundamental domain D, with F
integrable on D and ‖T i‖ summable, then P is integrable on A. -/
theorem integrable_of_isAddFundamentalDomain_clm (hD : IsAddFundamentalDomain Γ D μ)
    (e : I ≃ Γ) {T : I → X →L[ℝ] Y} (hT : Summable fun i : I ↦ ‖T i‖)
    {F : A → X} (hF : IntegrableOn F D μ) {P : A → Y} (hP_meas : AEStronglyMeasurable P μ)
    (hPF : ∀ (i : I) (z : A), P (e i +ᵥ z) = T i (F z)) :
    Integrable P μ := by
  refine ⟨hP_meas, ?_⟩
  calc ∫⁻ z, ‖P z‖ₑ ∂μ
      = ∑' i : I, ∫⁻ z in D, ‖T i (F z)‖ₑ ∂μ := by
        simp [hD.lintegral_eq_tsum'', ← e.tsum_eq, hPF]
    _ ≤ ∑' i : I, ∫⁻ z in D, ‖T i‖ₑ * ‖F z‖ₑ ∂μ := by
        gcongr with i z
        exact (T i).le_opENorm _
    _ < ⊤ := by
        simpa [lintegral_const_mul', ENNReal.tsum_mul_right] using
          ENNReal.mul_lt_top hT.tsum_ofReal_lt_top hF.hasFiniteIntegral

/-- Unfolding over an additive fundamental domain D: if P (e i +ᵥ z) = T i (F z) with F
integrable on D and ‖T i‖ summable, then ∫ z, P z ∂μ = ∑' i, T i (∫ z in D, F z ∂μ). -/
theorem integral_eq_tsum_of_isAddFundamentalDomain_clm [CompleteSpace X] [CompleteSpace Y]
    (hD : IsAddFundamentalDomain Γ D μ) (e : I ≃ Γ) {T : I → X →L[ℝ] Y}
    (hT : Summable fun i : I ↦ ‖T i‖) {F : A → X} (hF : IntegrableOn F D μ) {P : A → Y}
    (hP_meas : AEStronglyMeasurable P μ) (hPF : ∀ (i : I) (z : A), P (e i +ᵥ z) = T i (F z)) :
    ∫ z, P z ∂μ = ∑' i : I, T i (∫ z in D, F z ∂μ) := by
  have hP : Integrable P μ :=
    integrable_of_isAddFundamentalDomain_clm hD e hT hF hP_meas hPF
  simp [hD.integral_eq_tsum'' P hP, ← e.tsum_eq, hPF, (T _).integral_comp_comm hF]

/-- The unfolded series i ↦ T i (∫ z in D, F z ∂μ) over an additive fundamental domain D has
sum ∫ z, P z ∂μ. -/
theorem hasSum_integral_of_isAddFundamentalDomain_clm [CompleteSpace X] [CompleteSpace Y]
    (hD : IsAddFundamentalDomain Γ D μ) (e : I ≃ Γ) {T : I → X →L[ℝ] Y}
    (hT : Summable fun i : I ↦ ‖T i‖) {F : A → X} (hF : IntegrableOn F D μ) {P : A → Y}
    (hP_meas : AEStronglyMeasurable P μ) (hPF : ∀ (i : I) (z : A), P (e i +ᵥ z) = T i (F z)) :
    HasSum (fun i : I ↦ T i (∫ z in D, F z ∂μ)) (∫ z, P z ∂μ) := by
  rw [integral_eq_tsum_of_isAddFundamentalDomain_clm hD e hT hF hP_meas hPF]
  refine Summable.hasSum (.of_norm_bounded (hT.mul_right ‖∫ z in D, F z ∂μ‖) fun i ↦ ?_)
  exact (T i).le_opNorm _

end TauCeti
