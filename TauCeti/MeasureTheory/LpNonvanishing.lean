/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# A σ-finite measure carries a nowhere-vanishing `L²` function

On a σ-finite measure space there is an `F ∈ L²` with `F x ≠ 0` almost everywhere.

## Why it is wanted

In the multiplication model of spectral multiplicity theory, the scalar spectral measure of a
vector `F` is the pushforward of `|F|² · ρ`.  Such a measure is always dominated by the
pushforward of `ρ`; it is *equivalent* to it exactly when `F` is almost everywhere nonzero.  A
vector like that is what the classical development calls a **maximal vector**, and its existence
is what lets the measure class of the model be read off from a single vector.

σ-finiteness is exactly the right hypothesis, and it is used through
`MeasureTheory.exists_pos_lintegral_lt_of_sigmaFinite`: on a non-σ-finite space there need be no
integrable positive function at all, and hence no maximal vector.

## Main results

* `TauCeti.exists_ae_ne_zero_memLp_two`: a nowhere-vanishing square-integrable function.
* `TauCeti.exists_ae_ne_zero_lp_two`: the same, as an element of `Lp ℂ 2 ρ`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]

/-- **A σ-finite measure carries a nowhere-vanishing square-integrable function.**

Take a positive integrable `w` from σ-finiteness and use its pointwise square root: squaring
turns the `L²` condition into the `L¹` condition that `w` already satisfies. -/
theorem exists_ae_ne_zero_memLp_two (ρ : Measure α) [SigmaFinite ρ] :
    ∃ f : α → ℂ, MemLp f 2 ρ ∧ ∀ x, f x ≠ 0 := by
  obtain ⟨w, hwpos, hwmeas, hwint⟩ :=
    MeasureTheory.exists_pos_lintegral_lt_of_sigmaFinite ρ (ε := 1) one_ne_zero
  refine ⟨fun x => ((Real.sqrt (w x) : ℝ) : ℂ), ?_, ?_⟩
  · have hfmeas : AEStronglyMeasurable
        (fun x => ((Real.sqrt (w x) : ℝ) : ℂ)) ρ :=
      (Complex.continuous_ofReal.measurable.comp
        (Real.continuous_sqrt.measurable.comp
          (measurable_coe_nnreal_real.comp hwmeas))).aestronglyMeasurable
    change eLpNorm (fun x => ((Real.sqrt (w x) : ℝ) : ℂ)) 2 ρ < ∞
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hfmeas]
    have hcongr : ∫⁻ x, ‖((Real.sqrt (w x) : ℝ) : ℂ)‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂ρ
        = ∫⁻ x, (w x : ℝ≥0∞) ∂ρ := by
      refine lintegral_congr fun x => ?_
      have hnorm : ‖((Real.sqrt (w x) : ℝ) : ℂ)‖ = Real.sqrt (w x) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
        ← ofReal_norm, hnorm, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
        Real.sq_sqrt (w x).coe_nonneg, ENNReal.ofReal_coe_nnreal]
    rw [hcongr]
    exact hwint.trans_le le_top
  · intro x
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (hwpos x)))

/-- **A σ-finite measure carries an almost-everywhere nonvanishing `L²` vector.** -/
theorem exists_ae_ne_zero_lp_two (ρ : Measure α) [SigmaFinite ρ] :
    ∃ F : Lp ℂ 2 ρ, ∀ᵐ x ∂ρ, (F : α → ℂ) x ≠ 0 := by
  obtain ⟨f, hmem, hne⟩ := exists_ae_ne_zero_memLp_two ρ
  refine ⟨hmem.toLp f, ?_⟩
  filter_upwards [hmem.coeFn_toLp] with x hx
  rw [hx]
  exact hne x

end TauCeti
