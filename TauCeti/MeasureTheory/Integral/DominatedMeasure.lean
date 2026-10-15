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
    ∃ C : ℝ≥0, ∀ ν : Measure X, ν ≤ μ →
      ∫⁻ x, f x ∂ν ≤ C * ν univ + η := by
  by_cases hzero : ∫⁻ x, f x ∂μ = 0
  · refine ⟨0, fun ν hν ↦ ?_⟩
    exact (lintegral_mono' hν le_rfl).trans (by simp [hzero])
  have happrox : (∫⁻ x, f x ∂μ) - η < ∫⁻ x, f x ∂μ :=
    ENNReal.sub_lt_self hf hzero hη.ne'
  conv_rhs at happrox => rw [lintegral_eq_nnreal]
  obtain ⟨φ, hφint⟩ := lt_iSup_iff.mp happrox
  obtain ⟨hle, hlt⟩ := lt_iSup_iff.mp hφint
  have hφle : ∀ x, (φ x : ℝ≥0∞) ≤ f x := hle
  have hφfinite : ∫⁻ x, (φ x : ℝ≥0∞) ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top hf (lintegral_mono hφle)
  have hres : ∫⁻ x, f x - φ x ∂μ < η := by
    rw [lintegral_sub φ.measurable.coe_nnreal_ennreal hφfinite (ae_of_all _ hφle)]
    apply ENNReal.sub_lt_of_lt_add (lintegral_mono hφle)
    apply ENNReal.lt_add_of_sub_lt_left (.inl hf)
    simpa only [← SimpleFunc.lintegral_eq_lintegral, SimpleFunc.coe_map,
      Function.comp_apply] using hlt
  obtain ⟨C, hC⟩ := φ.exists_forall_le
  refine ⟨C, fun ν hν ↦ ?_⟩
  calc
    ∫⁻ x, f x ∂ν = ∫⁻ x, (f x - φ x) + φ x ∂ν := by
      congr 1
      ext x
      exact (tsub_add_cancel_of_le (hφle x)).symm
    _ = (∫⁻ x, f x - φ x ∂ν) + ∫⁻ x, (φ x : ℝ≥0∞) ∂ν :=
      lintegral_add_right _ φ.measurable.coe_nnreal_ennreal
    _ ≤ η + C * ν univ := add_le_add
      ((lintegral_mono' hν le_rfl).trans hres.le)
      ((lintegral_mono fun x ↦ ENNReal.coe_le_coe.mpr (hC x)).trans_eq (lintegral_const C))
    _ = C * ν univ + η := add_comm _ _

end TauCeti
