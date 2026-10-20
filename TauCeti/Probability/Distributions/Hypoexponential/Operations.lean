/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypoexponential.Transforms

/-!
# Closure properties of hypoexponential laws

Reindexing a finite rate family preserves its hypoexponential law. Convolution concatenates
rate families, and multiplying a variable by a positive constant divides all of its rates
by that constant. These identities allow sums to be regrouped without requiring distinct
rates and retain empty families as convolution units.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Reindexing the rates along an equivalence does not change a hypoexponential law. -/
theorem hypoexponentialMeasure_reindex (r : κ → ℝ) (e : ι ≃ κ) :
    hypoexponentialMeasure (r ∘ e) = hypoexponentialMeasure r := by
  by_cases hr : ∀ i, 0 < r i
  · have hre : ∀ i, 0 < (r ∘ e) i := by
      simpa only [Function.comp_apply] using fun i ↦ hr (e i)
    let _ := isProbabilityMeasure_hypoexponentialMeasure hr
    let _ := isProbabilityMeasure_hypoexponentialMeasure hre
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_hypoexponentialMeasure hre, charFun_hypoexponentialMeasure hr]
    simpa only [Function.comp_apply] using
      e.prod_comp (fun i ↦ (r i : ℂ) / (r i - Complex.I * t))
  · have hre : ¬ ∀ i, 0 < (r ∘ e) i := by
      intro h
      exact hr fun i ↦ by simpa only [Function.comp_apply, e.apply_symm_apply] using h (e.symm i)
    simp only [hypoexponentialMeasure_eq_zero_of_invalid hre,
      hypoexponentialMeasure_eq_zero_of_invalid hr]

/-- Convolution of hypoexponential laws concatenates their rate families. -/
theorem hypoexponentialMeasure_conv_hypoexponentialMeasure
    {r : ι → ℝ} {s : κ → ℝ} :
    hypoexponentialMeasure r ∗ hypoexponentialMeasure s =
      hypoexponentialMeasure (Sum.elim r s) := by
  by_cases hr : ∀ i, 0 < r i
  · by_cases hs : ∀ j, 0 < s j
    · have hsum : ∀ i, 0 < Sum.elim r s i := by
        intro i
        cases i with
        | inl i => exact hr i
        | inr j => exact hs j
      let _ := isProbabilityMeasure_hypoexponentialMeasure hr
      let _ := isProbabilityMeasure_hypoexponentialMeasure hs
      let _ := isProbabilityMeasure_hypoexponentialMeasure hsum
      apply Measure.ext_of_charFun
      funext t
      simp only [charFun_conv, charFun_hypoexponentialMeasure hr,
        charFun_hypoexponentialMeasure hs, charFun_hypoexponentialMeasure hsum,
        Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    · have hsum : ¬ ∀ i, 0 < Sum.elim r s i := fun h ↦ hs fun j ↦ h (Sum.inr j)
      simp [hypoexponentialMeasure_eq_zero_of_invalid hs,
        hypoexponentialMeasure_eq_zero_of_invalid hsum]
  · have hsum : ¬ ∀ i, 0 < Sum.elim r s i := fun h ↦ hr fun i ↦ h (Sum.inl i)
    simp [hypoexponentialMeasure_eq_zero_of_invalid hr,
      hypoexponentialMeasure_eq_zero_of_invalid hsum]

/-- Positive scaling of a hypoexponential law divides every rate by the scale. -/
theorem map_mul_hypoexponentialMeasure {r : ι → ℝ} {c : ℝ} (hc : 0 < c) :
    (hypoexponentialMeasure r).map (c * ·) =
      hypoexponentialMeasure (fun i ↦ r i / c) := by
  by_cases hr : ∀ i, 0 < r i
  · have hscale : ∀ i, 0 < r i / c := fun i ↦ div_pos (hr i) hc
    let _ := isProbabilityMeasure_hypoexponentialMeasure hr
    let _ := isProbabilityMeasure_hypoexponentialMeasure hscale
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_map_mul, charFun_hypoexponentialMeasure hr,
      charFun_hypoexponentialMeasure hscale]
    apply Finset.prod_congr rfl
    intro i _
    have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    rw [Complex.ofReal_div, div_sub' hc0, div_div_div_cancel_right₀ hc0]
    congr 2
    push_cast
    ring
  · have hscale : ¬ ∀ i, 0 < r i / c := by
      simpa only [div_pos_iff_of_pos_right hc] using hr
    simp [hypoexponentialMeasure_eq_zero_of_invalid hr,
      hypoexponentialMeasure_eq_zero_of_invalid hscale]

end TauCeti.Probability
