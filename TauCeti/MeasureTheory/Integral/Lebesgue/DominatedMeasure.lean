/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Small integrals against dominated measures

A function with finite nonnegative integral has uniformly small integrals against measures
that are dominated by a fixed measure and have small total mass. The quantitative estimate
here splits the function into a bounded simple function and an integrable remainder.
It applies without measurability of the function, using the lower Lebesgue integral.

This estimate controls the cost of completing partial transport plans when the cost has
an integrable marginal envelope, rather than a uniform bound.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ≥0∞}

/-- A finite nonnegative integral admits a uniform bound against every dominated measure:
for each positive error `η`, the integral is at most `C` times the total mass plus `η`.
Neither finiteness of the reference measure nor measurability of `f` is needed. -/
theorem exists_lintegral_le_mul_measure_add_of_ne_top
    (hf : ∫⁻ x, f x ∂μ ≠ ∞) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ C : ℝ≥0, ∀ ν ≤ μ, ∫⁻ x, f x ∂ν ≤ C * ν univ + η := by
  by_cases hzero : ∫⁻ x, f x ∂μ = 0
  · exact ⟨0, fun ν hν ↦ (lintegral_mono' hν le_rfl).trans (by simp [hzero])⟩
  -- A simple function `φ ≤ f` whose integral is within `η` of that of `f`.
  have happrox : (∫⁻ x, f x ∂μ) - η < ∫⁻ x, f x ∂μ := ENNReal.sub_lt_self hf hzero hη.ne'
  conv_rhs at happrox => rw [lintegral_eq_nnreal]
  obtain ⟨φ, hφint⟩ := lt_iSup_iff.mp happrox
  obtain ⟨hφf : ∀ x, (φ x : ℝ≥0∞) ≤ f x, hlt⟩ := lt_iSup_iff.mp hφint
  have hres : ∫⁻ x, f x - φ x ∂μ < η := by
    rw [lintegral_sub φ.measurable.coe_nnreal_ennreal
      (ne_top_of_le_ne_top hf (lintegral_mono hφf)) (ae_of_all _ hφf)]
    apply ENNReal.sub_lt_of_lt_add (lintegral_mono hφf)
    apply ENNReal.lt_add_of_sub_lt_left (.inl hf)
    simpa only [← SimpleFunc.lintegral_eq_lintegral, SimpleFunc.coe_map,
      Function.comp_apply] using hlt
  -- The bounded part `φ` contributes at most `C * ν univ`, the remainder `f - φ` less than `η`.
  obtain ⟨C, hC⟩ := φ.exists_forall_le
  refine ⟨C, fun ν hν ↦ ?_⟩
  calc
    ∫⁻ x, f x ∂ν ≤ ∫⁻ x, φ x + (f x - φ x) ∂ν := lintegral_mono fun _ ↦ le_add_tsub
    _ = (∫⁻ x, (φ x : ℝ≥0∞) ∂ν) + ∫⁻ x, f x - φ x ∂ν :=
      lintegral_add_left φ.measurable.coe_nnreal_ennreal _
    _ ≤ C * ν univ + η := by
      gcongr
      · exact (lintegral_mono fun x ↦ ENNReal.coe_le_coe.mpr (hC x)).trans_eq (lintegral_const _)
      · exact (lintegral_mono' hν le_rfl).trans hres.le

end TauCeti
